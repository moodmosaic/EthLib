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
  applySut h s
    | .absorb chunk => pure (h.absorb chunk)
    | .digest => do
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
    let width ← Gen.element [128, 64, 32, 8, 2, 1]
    pure ⟨key, width, ← genCounter, .empty, false⟩
  transitions _ := Gen.frequency [
    (5, (fun k => StreamStep.blocks k) <$> (do genBytesN (16 * (← Gen.nat (.constant 0 4))))),
    (1, (fun k => StreamStep.tail k) <$> (do
      genBytesN (16 * (← Gen.nat (.constant 0 2)) + (← Gen.nat (.constant 1 15)))))]
  preconditions s _ := !s.closed
  apply s t := { s with data := s.data ++ t.data', closed := t matches .tail _ }
  initSut s := pure (vec 16 s.counter, .empty)
  applySut sut s t := do
    let (block, out) := sut
    let piece := t.data'
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
  deriving Inhabited

/-- The system holds what the model holds. -/
def Drbg.agree (state : Rfc6979.NonceState) (key value : String) : TestT IO Unit := do
  hex state.key === key
  hex state.value === value

/-- Seed the generator with a private key and a message hash. -/
structure Seed where
  oracle : Oracle
  q : Nat
  x : Nat
  hash : ByteArray

instance : Command Seed Drbg Oracle IO where
  apply c _ := do
    let state := Rfc6979.nonceSeed c.q c.x (vec 32 c.hash)
    let (key, value) := two (← c.oracle.ask ["rfc_seed", toString c.q, toString c.x, hex c.hash])
    Drbg.agree state key value
    pure ⟨some state, state.key, state.value⟩
  label c := s!"SEED(q={c.q}, x={c.x}, h1={hex c.hash})"
  build oracle := do
    pure ⟨oracle, ← Gen.element orders, ← genNatBits 256, ← genBytesOf 32⟩

/-- Draw the next candidate nonce. -/
structure Next where
  oracle : Oracle

instance : Command Next Drbg Oracle IO where
  check _ s := s.sut.isSome
  apply c s := do
    let some state := s.sut | failure
    let (candidate, next) := Rfc6979.nonceNext state
    let value ← c.oracle.ask ["rfc_next", hex s.key, hex s.value]
    Drbg.agree next (hex s.key) value
    hexv (Base.uintToBytes 32 candidate) === hex ⟨(unhex? value).getD .empty |>.data.reverse⟩
    pure ⟨some next, next.key, next.value⟩
  label _ := "NEXT"
  build oracle := pure ⟨oracle⟩

/-- Reject the last candidate, which updates the key. -/
structure Reject where
  oracle : Oracle

instance : Command Reject Drbg Oracle IO where
  check _ s := s.sut.isSome
  apply c s := do
    let some state := s.sut | failure
    let next := Rfc6979.nonceReject state
    let (key, value) := two (← c.oracle.ask ["rfc_reject", hex s.key, hex s.value])
    Drbg.agree next key value
    pure ⟨some next, next.key, next.value⟩
  label _ := "REJECT"
  build oracle := pure ⟨oracle⟩

/-- Any sequence of seeding, drawing and rejecting leaves the generator where the reference is.

Step h of RFC 6979 §3.2 leaves the reference there. -/
def drbgScenario (mode : Mode) (oracle : Oracle) : Property IO :=
  scenario mode oracle [Command.gen Seed, Command.gen Next, Command.gen Reject,
    Command.gen Next, Command.gen Reject]

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

/-- A session: a key, a packet number that every seal uses once, and the packets in flight. -/
structure Session where
  key : ByteArray := ⟨Array.replicate 32 0⟩
  number : Nat := 0
  packets : List Packet := []
  deriving Inhabited

/-- The nonce of a packet number: 12 bytes, the least significant first. -/
def Session.nonce (s : Session) : ByteArray := unvec (Base.uintToBytes 12 s.number)

/-- Seal a packet under AES-GCM, with the first 16 or all 32 bytes of the session key. -/
structure SealGcm where
  oracle : Oracle
  wide : Bool
  aad : ByteArray
  plain : ByteArray

instance : Command SealGcm Session Oracle IO where
  apply c s := do
    let key := if c.wide then s.key else s.key.extract 0 16
    let got := Aes.Gcm.encrypt (aesCiph key) 16 s.nonce c.plain c.aad
    pairOf got
      === (← c.oracle.ask ["gcm_enc", hex key, "16", hex s.nonce, hex c.plain, hex c.aad])
    let .ok (text, tag) := got | failure
    let packet : Packet := ⟨false, key, s.nonce, c.aad, text, tag, c.plain⟩
    pure { s with number := s.number + 1, packets := packet :: s.packets }
  label c := s!"SEAL-GCM(wide={c.wide}, aad={hex c.aad}, plain={hex c.plain})"
  build oracle := do
    let (aad, plain) ← Gen.zip (genTextLen >>= genBytesOf) (genTextLen >>= genBytesOf)
    pure ⟨oracle, ← Gen.bool, aad, plain⟩

/-- Seal a packet under ChaCha20-Poly1305. -/
structure SealChaCha where
  oracle : Oracle
  aad : ByteArray
  plain : ByteArray

instance : Command SealChaCha Session Oracle IO where
  apply c s := do
    let got := (ChaCha20Poly1305.encrypt (vec 32 s.key) (vec 12 s.nonce) c.aad c.plain).map
      fun (text, tag) => (text, unvec tag)
    pairOf got === (← c.oracle.ask ["aead_enc", hex s.key, hex s.nonce, hex c.aad, hex c.plain])
    let .ok (text, tag) := got | failure
    let packet : Packet := ⟨true, s.key, s.nonce, c.aad, text, tag, c.plain⟩
    pure { s with number := s.number + 1, packets := packet :: s.packets }
  label c := s!"SEAL-CHACHA(aad={hex c.aad}, plain={hex c.plain})"
  build oracle := do
    pure ⟨oracle, ← genBytesOf (← genTextLen), ← genBytesOf (← genLen 64 2)⟩

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
  oracle : Oracle
  index : Nat

instance : Command Open Session Oracle IO where
  check _ s := !s.packets.isEmpty
  apply c s := do
    let i := c.index % s.packets.length
    let some p := s.packets[i]? | failure
    let (got, expected) ← openPacket c.oracle p
    got === expected
    got === hex p.plain
    pure { s with packets := s.packets.eraseIdx i }
  label c := s!"OPEN({c.index})"
  build oracle := do pure ⟨oracle, ← Gen.nat (.constant 0 7)⟩

/-- Open a packet in flight with one bit changed, which must be refused and deliver nothing. -/
structure OpenTampered where
  oracle : Oracle
  index : Nat
  tamper : Tamper
  bit : Nat

instance : Command OpenTampered Session Oracle IO where
  check _ s := !s.packets.isEmpty
  apply c s := do
    let some p := s.packets[c.index % s.packets.length]? | failure
    let p := match c.tamper with
      | .tag => { p with tag := flipBit p.tag c.bit }
      | .text => { p with text := flipBit p.text c.bit }
      | .aad => { p with aad := flipBit p.aad c.bit }
      | .nonce => { p with nonce := flipBit p.nonce c.bit }
      | _ => { p with key := flipBit p.key c.bit }
    let (got, expected) ← openPacket c.oracle p
    got === expected
    got === "error"
    pure s
  label c := s!"OPEN-TAMPERED({c.index}, {reprStr c.tamper}, bit {c.bit})"
  build oracle := do
    pure ⟨oracle, ← Gen.nat (.constant 0 7),
      ← Gen.element [.tag, .text, .aad, .nonce, .none], ← Gen.nat (.constant 0 1023)⟩

/-- Change the session key, and move the packet number to where its bytes carry. -/
structure Rekey where
  key : ByteArray
  number : Nat

instance : Command Rekey Session Oracle IO where
  apply c s := pure { s with key := c.key, number := c.number }
  label c := s!"REKEY({hex c.key}, {c.number})"
  build _ := do
    let top ← Gen.element [2 ^ 8, 2 ^ 32, 2 ^ 64, 2 ^ 96]
    pure ⟨← genBytesOf 32, top - 1 - (← Gen.nat (.constant 0 2))⟩

/-- In any order of sealing, opening, tampering and rekeying, both AEADs seal as the reference.

Every packet in flight opens to what was sealed, and a tampered packet is refused by both. -/
def sessionScenario (mode : Mode) (oracle : Oracle) : Property IO :=
  scenario mode oracle [Command.gen SealGcm, Command.gen SealChaCha, Command.gen Open,
    Command.gen OpenTampered, Command.gen Rekey, Command.gen SealGcm, Command.gen OpenTampered]

end HashesProperty
