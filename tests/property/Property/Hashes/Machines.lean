import Property.Hashes.Cipher
import Property.Hashes.Misc

/-!
# State machines

Two machines with their transitions in one type (`StateMachine`):

- The incremental Keccak-256 hasher.
- A counter-mode stream.

There the specification fixes the operations.

Two scenarios of commands (`Command`), run in madhouse mode:

- The nonce generator of RFC 6979.
- A session that seals and opens packets.

There the operations are a set that grows.
-/

open Hedgehog Support EthLib EthLib.Cryptography

namespace HashesProperty

/-! ## The incremental Keccak-256 hasher -/

/-- An operation of the hasher. -/
inductive HashStep where
  /-- Absorb more bytes. -/
  | absorb (chunk : ByteArray)
  /-- Read the digest of the bytes so far, which leaves the hasher as it is. -/
  | digest
  deriving Repr

/-- Given the bytes already absorbed, a chunk that ends near the end of a block, or any chunk.

Near means on, just before or just after the end. -/
def genChunk (absorbed : Nat) : Gen ByteArray := do
  let toBoundary := 136 - absorbed % 136
  let size ← Gen.frequency [
    (4, (fun d => toBoundary + 1 - d) <$> Gen.nat (.constant 0 2)),
    (2, (fun d => toBoundary + 136 + 1 - d) <$> Gen.nat (.constant 0 2)),
    (2, Gen.element [0, 1, 135, 136, 137, 272, 273]),
    (2, Gen.nat (.linear 0 300))]
  genBytesOf size

/-- The hasher against the message so far.

After any sequence of chunks its digest is the reference's Keccak-256 of their concatenation.

It holds fewer bytes than a block, and those bytes are the tail of the message. -/
def hasherMachine (oracle : Oracle) : StateMachine ByteArray HashStep Hash.Keccak.Hasher256 IO where
  initState := pure .empty
  transitions s := Gen.frequency [(4, .absorb <$> genChunk s.size), (1, pure .digest)]
  apply
    | s, .absorb chunk => s ++ chunk
    | s, .digest => s
  initSut _ := pure .empty
  applySut h before s
    | .absorb chunk => do
      classify "absorb: an empty chunk" chunk.isEmpty
      classify "absorb: the chunk ends exactly on a block" (!chunk.isEmpty && s.size % 136 == 0)
      classify "absorb: the chunk ends one byte before a block" (s.size % 136 == 135)
      classify "absorb: the chunk crosses a block" (before.size / 136 != s.size / 136)
      classify "absorb: the chunk holds two blocks or more" (chunk.size ≥ 272)
      classify "absorb: the chunk stays inside a block"
        (!chunk.isEmpty && before.size / 136 == s.size / 136)
      pure (h.absorb chunk)
    | .digest => do
      classify "digest: of nothing" s.isEmpty
      classify "digest: nothing pending, the padding is a whole block"
        (!s.isEmpty && s.size % 136 == 0)
      classify "digest: 135 bytes pending, the padding is one byte" (s.size % 136 == 135)
      classify "digest: after two blocks or more" (s.size ≥ 272)
      hexv h.digest === (← oracle.ask ["keccak256", hex s])
      pure h
  invariants h s := do
    ensure (h.pending.size < 136) "a whole block is pending"
    hex h.pending === hex (s.extract (s.size / 136 * 136) s.size)
    hexv h.digest === hexv (Hash.Keccak.keccak256 s)

/-! ## A counter-mode stream -/

/-- A stream: its key, the width of its counter, its first counter block, and its data so far. -/
structure Stream where
  key : ByteArray
  width : Nat
  counter : ByteArray
  data : ByteArray
  /-- Whether a partial block ended the stream. -/
  closed : Bool
  deriving Repr

/-- The next piece of a stream. -/
inductive StreamStep where
  /-- Some whole blocks. -/
  | blocks (data : ByteArray)
  /-- A last piece that ends in a partial block. -/
  | tail (data : ByteArray)
  deriving Repr

/-- The bytes of a piece. -/
def StreamStep.data' : StreamStep → ByteArray
  | .blocks data => data
  | .tail data => data

/-- A stream encrypted piece by piece is the stream encrypted at once by the reference.

The system keeps the next counter block, which it advances with the incrementing function.

So a piece that starts after the counter wrapped must continue where the reference is. -/
def streamMachine (oracle : Oracle) :
    StateMachine Stream StreamStep (Aes.Block × ByteArray) IO where
  initState := do
    let key ← genAesKey
    let width ← Gen.frequency [(3, Gen.element [128, 64, 32, 8, 2, 1]),
      (1, Gen.nat (.constant 1 128))]
    pure ⟨key, width, ← genCounterFor width, .empty, false⟩
  transitions _ := Gen.frequency [
    (5, (fun k => StreamStep.blocks k) <$> (do genBytesN (16 * (← Gen.nat (.constant 0 4))))),
    (1, (fun k => StreamStep.tail k) <$> (do
      genBytesN (16 * (← Gen.nat (.constant 0 2)) + (← Gen.nat (.constant 1 15)))))]
  preconditions s _ := !s.closed
  apply s t := { s with data := s.data ++ t.data', closed := t matches .tail _ }
  initSut s := pure (vec 16 s.counter, .empty)
  applySut sut before s t := do
    let (block, out) := sut
    let piece := t.data'
    let low := beNat before.counter % 2 ^ s.width
    classify "width: 128 bits" (s.width == 128)
    classify "width: 32 bits, as GCM" (s.width == 32)
    classify "width: under 8 bits" (s.width < 8)
    classify "width: not whole bytes" (s.width % 8 != 0)
    classify "piece: starts after the counter wrapped" (low + before.data.size / 16 ≥ 2 ^ s.width)
    classify "piece: the counter wraps inside it"
      (low + before.data.size / 16 < 2 ^ s.width &&
        low + (s.data.size + 15) / 16 > 2 ^ s.width)
    classify "piece: empty" piece.isEmpty
    classify "piece: a tail, which closes the stream" (t matches .tail _)
    pure (Nat.repeat (Aes.inc s.width) (piece.size / 16) block,
      out ++ Aes.ctr (aesCiph s.key) s.width block piece)
  invariants sut s := do
    hex sut.2 === (← oracle.ask ["ctr", hex s.key, toString s.width, hex s.counter, hex s.data])

/-! ## The nonce generator of RFC 6979 -/

/-- The generator and its model: the key `K` and the value `V` that the reference holds. -/
structure Drbg where
  sut : Option Rfc6979.NonceState := none
  key : ByteArray := .empty
  value : ByteArray := .empty
  /-- The rejections since the seed, to name the classes of a sequence. -/
  rejects : Nat := 0
  /-- The candidates drawn since the last rejection or the seed. -/
  draws : Nat := 0
  deriving Inhabited

/-- The system holds what the model holds. -/
def Drbg.agree (state : Rfc6979.NonceState) (key value : String) : TestT IO Unit := do
  hex state.key === key
  hex state.value === value

/-- Seed the generator with a private key and a message hash. -/
structure Seed where
  q : Nat
  x : Nat
  hash : ByteArray

instance : Command Seed Drbg Oracle IO where
  apply oracle c s := do
    let state := Rfc6979.nonceSeed c.q c.x (vec 32 c.hash)
    let (key, value) := two (← oracle.ask ["rfc_seed", toString c.q, toString c.x, hex c.hash])
    Drbg.agree state key value
    classify "seeded again, over a state in use" s.sut.isSome
    pure ⟨some state, state.key, state.value, 0, 0⟩
  label c := s!"SEED(q={c.q}, x={c.x}, h1={hex c.hash})"
  build _ := do
    let q ← genOrder
    pure ⟨q, ← genNearOrder q, ← Gen.choice [genBytesOf 32, beBytes 32 <$> genNearOrder q]⟩
  -- The state that the generator sees is seeded, whatever the seed.
  next _ _ s := { s with sut := some ⟨.empty, .empty⟩ }

/-- Draw the next candidate nonce. -/
structure Next where

instance : Command Next Drbg Oracle IO where
  check _ _ s := s.sut.isSome
  apply oracle _ s := do
    let some state := s.sut | failure
    let (candidate, next) := Rfc6979.nonceNext state
    let value ← oracle.ask ["rfc_next", hex s.key, hex s.value]
    Drbg.agree next (hex s.key) value
    hexv (Base.uintToBytes 32 candidate) === hex ⟨(unhex? value).getD .empty |>.data.reverse⟩
    classify "a candidate drawn" true
    classify "a candidate drawn after a rejection" (s.rejects > 0)
    classify "two candidates drawn with no rejection between" (s.draws > 0)
    pure ⟨some next, next.key, next.value, s.rejects, s.draws + 1⟩
  label _ := "NEXT"
  build _ := pure {}

/-- Reject the last candidate, which updates the key. -/
structure Reject where

instance : Command Reject Drbg Oracle IO where
  check _ _ s := s.sut.isSome
  apply oracle _ s := do
    let some state := s.sut | failure
    let next := Rfc6979.nonceReject state
    let (key, value) := two (← oracle.ask ["rfc_reject", hex s.key, hex s.value])
    Drbg.agree next key value
    classify "a candidate rejected" true
    classify "two rejections or more since the seed" (s.rejects > 0)
    classify "a rejection with no candidate drawn before" (s.draws == 0)
    pure ⟨some next, next.key, next.value, s.rejects + 1, 0⟩
  label _ := "REJECT"
  build _ := pure {}

/-- The command `κ` when the generator is seeded, and a seed otherwise.

A draw or a rejection before the first seed would be skipped, and the sequence would say less. -/
def onceSeeded (κ : Type) [Command κ Drbg Oracle IO] (oracle : Oracle) (s : Drbg) :
    Gen (CommandWrapper Drbg IO) :=
  if s.sut.isSome then Command.gen κ oracle s else Command.gen Seed oracle s

/-- Any sequence of seeding, drawing and rejecting leaves the generator where the reference is.

Step h of RFC 6979 §3.2 leaves the reference there. -/
def drbgScenario (mode : Mode) (oracle : Oracle) : Property IO :=
  scenario mode oracle [Command.gen Seed, onceSeeded Next, onceSeeded Reject,
    onceSeeded Next, onceSeeded Reject, onceSeeded Reject] (.linear 1 30)

/-! ## A session of sealed packets -/

/-- A sealed packet, with what it was sealed from. -/
structure Packet where
  chacha : Bool
  key : ByteArray
  nonce : ByteArray
  aad : ByteArray
  text : ByteArray
  tag : ByteArray
  plain : ByteArray
  deriving Inhabited

/-- A session: a key, a packet number that every seal uses once, and the packets in flight. -/
structure Session where
  key : ByteArray := ⟨Array.replicate 32 0⟩
  number : Nat := 0
  packets : List Packet := []
  deriving Inhabited

/-- The nonce of a packet number: 12 bytes, the least significant first. -/
def Session.nonce (s : Session) : ByteArray := unvec (Base.uintToBytes 12 s.number)

/-- Count a seal under the classes of the session it is made in. -/
def Session.labelSeal (s : Session) : TestT IO Unit := do
  classify "sealed at a number whose bytes carry next" (s.number % 256 == 255)
  classify "sealed at the number 2^96, whose nonce is zeros again" (s.number ≥ 2 ^ 96)
  classify "sealed with packets in flight" (!s.packets.isEmpty)

/-- Seal a packet under AES-GCM, with the first 16 or all 32 bytes of the session key. -/
structure SealGcm where
  wide : Bool
  aad : ByteArray
  plain : ByteArray

instance : Command SealGcm Session Oracle IO where
  apply oracle c s := do
    let key := if c.wide then s.key else s.key.extract 0 16
    let got := Aes.Gcm.encrypt (aesCiph key) 16 s.nonce c.plain c.aad
    pairOf got
      === (← oracle.ask ["gcm_enc", hex key, "16", hex s.nonce, hex c.plain, hex c.aad])
    let .ok (text, tag) := got | failure
    classify "sealed under AES-GCM" true
    s.labelSeal
    let packet : Packet := ⟨false, key, s.nonce, c.aad, text, tag, c.plain⟩
    pure { s with number := s.number + 1, packets := packet :: s.packets }
  label c := s!"SEAL-GCM(wide={c.wide}, aad={hex c.aad}, plain={hex c.plain})"
  -- The packet itself is known only after the seal; the generator needs their count.
  next _ _ s := { s with number := s.number + 1, packets := default :: s.packets }
  build _ := do
    let (aad, plain) ← Gen.zip (genTextLen >>= genBytesOf) (genTextLen >>= genBytesOf)
    pure ⟨← Gen.bool, aad, plain⟩

/-- Seal a packet under ChaCha20-Poly1305. -/
structure SealChaCha where
  aad : ByteArray
  plain : ByteArray

instance : Command SealChaCha Session Oracle IO where
  apply oracle c s := do
    let got := (ChaCha20Poly1305.encrypt (vec 32 s.key) (vec 12 s.nonce) c.aad c.plain).map
      fun (text, tag) => (text, unvec tag)
    pairOf got === (← oracle.ask ["aead_enc", hex s.key, hex s.nonce, hex c.aad, hex c.plain])
    let .ok (text, tag) := got | failure
    classify "sealed under ChaCha20-Poly1305" true
    s.labelSeal
    let packet : Packet := ⟨true, s.key, s.nonce, c.aad, text, tag, c.plain⟩
    pure { s with number := s.number + 1, packets := packet :: s.packets }
  label c := s!"SEAL-CHACHA(aad={hex c.aad}, plain={hex c.plain})"
  next _ _ s := { s with number := s.number + 1, packets := default :: s.packets }
  build _ := do
    pure ⟨← genBytesOf (← genTextLen), ← genBytesOf (← genLen 64 2)⟩

/-- What EthLib and the reference give for a packet, each as hexadecimal or `error`. -/
def openPacket (oracle : Oracle) (p : Packet) : TestT IO (String × String) := do
  if p.chacha then
    let got := ChaCha20Poly1305.decrypt (vec 32 p.key) (vec 12 p.nonce) p.aad p.text (vec 16 p.tag)
    pure (answerOf got,
      ← oracle.ask ["aead_dec", hex p.key, hex p.nonce, hex p.aad, hex p.text, hex p.tag])
  else
    let got := Aes.Gcm.decrypt (aesCiph p.key) 16 p.nonce p.text p.aad p.tag
    pure (answerOf got,
      ← oracle.ask ["gcm_dec", hex p.key, "16", hex p.nonce, hex p.text, hex p.aad, hex p.tag])

/-- Open a packet in flight, which delivers it. -/
structure Open where
  index : Nat

instance : Command Open Session Oracle IO where
  check _ _ s := !s.packets.isEmpty
  apply oracle c s := do
    let i := c.index % s.packets.length
    let some p := s.packets[i]? | failure
    let (got, expected) ← openPacket oracle p
    got === expected
    got === hex p.plain
    classify "opened a packet" true
    classify "opened a packet sealed under an earlier key" (hex p.key != hex s.key &&
      hex p.key != hex (s.key.extract 0 16))
    classify "opened a packet out of order" (i + 1 != s.packets.length)
    pure { s with packets := s.packets.eraseIdx i }
  label c := s!"OPEN({c.index})"
  build _ := do pure ⟨← Gen.nat (.constant 0 7)⟩
  next _ c s := { s with packets := s.packets.eraseIdx (c.index % s.packets.length) }
  -- Any of the packets in flight, the oldest and the newest most often.
  buildIn _ s := Open.mk <$> Gen.frequency [(1, pure 0), (1, pure (s.packets.length - 1)),
    (2, Gen.nat (.constant 0 (s.packets.length - 1)))]

/-- Open a packet in flight with one bit changed, which must be refused and deliver nothing. -/
structure OpenTampered where
  index : Nat
  tamper : Tamper
  bit : Nat

instance : Command OpenTampered Session Oracle IO where
  check _ _ s := !s.packets.isEmpty
  apply oracle c s := do
    let some p := s.packets[c.index % s.packets.length]? | failure
    classify s!"refused a packet, changed: {if c.tamper == .none then "key" else
      ctorName c.tamper}" true
    let p := match c.tamper with
      | .tag => { p with tag := flipBit p.tag c.bit }
      | .text => { p with text := flipBit p.text c.bit }
      | .aad => { p with aad := flipBit p.aad c.bit }
      | .nonce => { p with nonce := flipBit p.nonce c.bit }
      | _ => { p with key := flipBit p.key c.bit }
    let (got, expected) ← openPacket oracle p
    got === expected
    got === "error"
    pure s
  label c := s!"OPEN-TAMPERED({c.index}, {reprStr c.tamper}, bit {c.bit})"
  build _ := do
    pure ⟨← Gen.nat (.constant 0 7),
      ← Gen.element [.tag, .text, .aad, .nonce, .none], ← Gen.nat (.constant 0 1023)⟩
  buildIn _ s := do
    pure ⟨← Gen.nat (.constant 0 (s.packets.length - 1)),
      ← Gen.element [.tag, .text, .aad, .nonce, .none], ← Gen.nat (.constant 0 1023)⟩

/-- Change the session key, and move the packet number to where its bytes carry. -/
structure Rekey where
  key : ByteArray
  number : Nat

instance : Command Rekey Session Oracle IO where
  apply _ c s := pure { s with key := c.key, number := c.number }
  label c := s!"REKEY({hex c.key}, {c.number})"
  build _ := do
    let top ← Gen.element [2 ^ 8, 2 ^ 32, 2 ^ 64, 2 ^ 96]
    pure ⟨← genBytesOf 32, top - 1 - (← Gen.nat (.constant 0 2))⟩
  next _ c s := { s with key := c.key, number := c.number }

/-- The command `κ` when a packet is in flight, and a seal otherwise.

Opening with nothing in flight would be skipped, and the sequence would say less. -/
def inFlight (κ : Type) [Command κ Session Oracle IO] (oracle : Oracle) (s : Session) :
    Gen (CommandWrapper Session IO) :=
  if s.packets.isEmpty then Command.gen SealChaCha oracle s else Command.gen κ oracle s

/-- In any order of sealing, opening, tampering and rekeying, both AEADs seal as the reference.

Every packet in flight opens to what was sealed, and a tampered packet is refused by both. -/
def sessionScenario (mode : Mode) (oracle : Oracle) : Property IO :=
  scenario mode oracle [Command.gen SealGcm, Command.gen SealChaCha, inFlight Open,
    inFlight OpenTampered, Command.gen Rekey, Command.gen SealGcm, inFlight OpenTampered]
    (.linear 1 30)

end HashesProperty
