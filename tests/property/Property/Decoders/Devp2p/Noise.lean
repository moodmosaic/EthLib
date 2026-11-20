import Hedgehog
import Support
import Property.Decoders.Devp2p.Common
import EthLib.Networking.Noise.Identity

/-!
# The handshake payload of noise-libp2p, on generated inputs

The reference is the `protobuf` package, with the schema of the Noise specification of libp2p.

The classes are built from its descriptor at run time.

libsecp256k1 signs and verifies, and the noiseprotocol package reads the handshake.
-/

open Hedgehog Support EthLib EthLib.Networking

namespace DecodersProperty.Devp2p.NoiseId

open DecodersProperty DecodersProperty.Devp2p

/-- Extensions as the oracle reads them: certificate hashes and stream muxers, or none. -/
def genExts : Gen String :=
  let part := Gen.frequency [
    (2, (fun b => "c" ++ hex b) <$> genBytes (.linear 0 6)),
    (2, (fun m => "m" ++ hex m.toUTF8) <$> Gen.element ["/yamux/1.0.0", "/mplex/6.7.0", "é", ""]),
    (1, pure "e")]
  Gen.frequency [(2, pure "none"), (3, (",".intercalate ·) <$> Gen.list (.constant 1 3) part)]

/-- The bytes of extensions, by the protobuf package. -/
def extBytes (oracle : Oracle) (exts : String) : TestT IO (Option ByteArray) := do
  if exts == "none" then pure none
  else
    let made ← oracle.ask ["noise_exts", exts]
    let some bytes := unhex? made | failWith s!"oracle: {made}"
    pure (some bytes)

/-- An optional value as the oracle writes it. -/
def optional (b : Option ByteArray) : String :=
  match b with
  | some b => hex b
  | none => "none"

/-! ## Writing -/

/-- The payload that EthLib makes is the deterministic serialization of the protobuf package.

Its key is the key of the peer ID specification, and its signature is libsecp256k1's. -/
def makes (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAllWith secretHex genSecret
  let static ← forAllWith hexv (genVector 32)
  let exts ← forAll genExts
  pure do
    let extensions ← extBytes oracle exts
    let expected ← oracle.ask ["noise_expect", secretHex sk, hexv static]
    let [key, sig] := words expected | failWith s!"oracle: {expected}"
    match Noise.makePayload (Fin.ofNat _ sk) static extensions with
    | .error e => failWith s!"makePayload refuses: {repr e}"
    | .ok payload =>
      hex payload === (← oracle.ask ["noise_make", key, sig, exts, "plain"])
      (← oracle.ask ["noise_payload", hex payload]) === s!"{key} {sig} {optional extensions}"
    cover 18 "with extensions" (exts != "none")
    cover 14 "without extensions" (exts == "none")

/-! ## Reading -/

/-- The forms of one message that the reference writes. -/
def forms : List String := ["plain", "reversed", "twice", "split", "unknown", "wiretype", "group"]

/-- A payload in any form that the protobuf encoding allows reads as the package reads it.

The fields may come in another order, twice, between unknown fields and groups.

The extensions may come in parts, which protobuf merges. -/
def reads (oracle : Oracle) : Property IO := propertyM do
  let key ← forAllWith hex (genBytes (.linear 0 40))
  let sig ← forAllWith hex (genBytes (.linear 0 72))
  let exts ← forAll genExts
  let form ← forAll (Gen.element forms)
  pure do
    let made ← oracle.ask ["noise_make", hex key, hex sig, exts, form]
    let some payload := unhex? made | failWith s!"oracle: {made}"
    annotate s!"payload: {hex payload}"
    let want ← oracle.ask ["noise_payload", hex payload]
    match Noise.decodePayload payload with
    | .error e => failWith s!"EthLib refuses ({repr e}), the reference reads {want}"
    | .ok p =>
      -- EthLib keeps the bytes of the extensions, so the package reads them for the comparison.
      let ext ← match p.extensions with
        | some bytes => oracle.ask ["noise_ext", hex bytes]
        | none => pure "none"
      s!"{hex p.publicKey} {hex p.signature} {ext}" === want
    cover 3 "the plain form" (form == "plain")
    cover 8 "extensions in parts" (form != "plain" && (exts.splitOn ",").length > 1)
    cover 4 "a field twice" (form == "twice")
    cover 5 "a field with another wire type" (form == "wiretype")
    cover 4 "a group" (form == "group")

/-- A payload with one byte changed reads as the package reads it, or is refused.

The package reads the extensions as bytes here, as EthLib keeps them closed.

The package skips an unknown group without checking the field numbers of the keys inside it.

So the reference also walks the bytes by the rules of the encoding guide, and both must accept. -/
def readsChanged (oracle : Oracle) : Property IO := propertyM do
  let key ← forAllWith hex (genBytes (.linear 0 12))
  let sig ← forAllWith hex (genBytes (.linear 0 12))
  let exts ← forAll genExts
  let form ← forAll (Gen.element forms)
  let change ← forAll genChange
  pure do
    let made ← oracle.ask ["noise_make", hex key, hex sig, exts, form]
    let some payload := unhex? made | failWith s!"oracle: {made}"
    let payload := mutate change payload
    annotate s!"payload: {hex payload}"
    let want ← oracle.ask ["noise_outer", hex payload]
    let got := match Noise.decodePayload payload with
      | .ok p => s!"{hex p.publicKey} {hex p.signature}"
      | .error _ => "error"
    got === verdict want
    cover 1 "mutated and still accepted by the reference" (!refused want)
    cover 5 "refused by the reference" (refused want)
    classify "read by the package, refused by the wire rules"
      (want.startsWith "error only by the wire rules")

/-- A key with the field number 0 inside an unknown group is refused, and the package reads it.

`Encoding/Protobuf.lean` says that a reader rejects field numbers outside 1 to `2^29 - 1`.

The package rejects such a key in a message, and only skips it inside a group it does not know. -/
def groupZero (oracle : Oracle) : Property IO := propertyM do
  let key ← forAllWith hex (genBytes (.linear 0 12))
  let sig ← forAllWith hex (genBytes (.linear 0 12))
  let exts ← forAll genExts
  pure do
    let made ← oracle.ask ["noise_make", hex key, hex sig, exts, "groupzero"]
    let some payload := unhex? made | failWith s!"oracle: {made}"
    annotate s!"payload: {hex payload}"
    ensure (Noise.decodePayload payload).toOption.isNone "EthLib reads a key with field number 0"
    let read ← oracle.ask ["noise_payload", hex payload]
    ensure (read.startsWith s!"{hex key} {hex sig} ") s!"the package says {read}"
    (← oracle.ask ["noise_outer", hex payload]) === "error only by the wire rules"

/-! ## Authentication -/

/-- What is wrong with a payload, if anything. -/
def faults : List String :=
  ["otherStatic", "otherSigner", "flip", "ed25519", "noPoint", "noKey", "noSig", "longKey"]

/-- A payload authenticates exactly when its key is a secp256k1 key that signed the static key.

libsecp256k1 decides, on the fields that the protobuf package reads.

The payload may be signed for another static key or by another key, or hold another kind of key. -/
def authenticates (oracle : Oracle) : Property IO := propertyM do
  let (sk, other) ← forAll (Gen.zip genSecret genSecret)
  let static ← forAllWith hexv (genVector 32)
  let exts ← forAll genExts
  let fault ← forAll (Gen.frequency [(3, pure "none"), (4, Gen.element faults)])
  let form ← forAll (Gen.element ["plain", "reversed", "split", "unknown"])
  pure do
    let signer := if fault == "otherSigner" then other else sk
    let signed : Vector UInt8 32 :=
      if fault == "otherStatic" then static.set! 31 (static[31]! ^^^ 1) else static
    let expected ← oracle.ask ["noise_expect", secretHex signer, hexv signed]
    let [_, sig] := words expected | failWith s!"oracle: {expected}"
    let [key, _] := words (← oracle.ask ["noise_expect", secretHex sk, hexv static])
      | failWith "oracle"
    let key := match fault with
      | "ed25519" => "08011220" ++ String.ofList (key.toList.drop 10)
      | "noPoint" => String.ofList (key.toList.take 10 ++ List.replicate 64 'f')
      | "noKey" => "-"
      | "longKey" => key ++ "00"
      | _ => key
    let sig := match fault with
      | "flip" => String.ofList (sig.toList.mapIdx fun j c =>
          if j == 20 then (if c == '0' then '1' else '0') else c)
      | "noSig" => "-"
      | _ => sig
    let made ← oracle.ask ["noise_make", key, sig, exts, form]
    let some payload := unhex? made | failWith s!"oracle: {made}"
    annotate s!"payload: {hex payload}"
    let want ← oracle.ask ["noise_verify", key, hexv static, sig]
    match Noise.authenticatePayload static payload with
    | .ok remote =>
      want === "1"
      hex remote.publicKey === key
      hex remote.signature === sig
      hexv remote.staticKey === hexv static
      ensure (remote.key == publicOf sk) "the remote has another identity key"
      let ext ← match remote.extensions with
        | some bytes => oracle.ask ["noise_ext", hex bytes]
        | none => pure "none"
      let want ← extBytes oracle exts
      ext === optional want
    | .error _ => want === "0"
    cover 7 "valid as generated" (fault == "none" && want == "1")
    cover 5 "refused by the reference" (want == "0")
    classify "mutated and still accepted by the reference" (fault != "none" && want == "1")

/-! ## The handshake -/

/-- The keys of one side of a handshake: Noise static, Noise ephemeral, and the identity. -/
structure Peer where
  static : Vector UInt8 32
  ephemeral : Vector UInt8 32
  identity : Nat

instance : Repr Peer where
  reprPrec p _ :=
    s!"static {hexv p.static} ephemeral {hexv p.ephemeral} identity {secretHex p.identity}"

/-- A peer with any keys. -/
def genPeer : Gen Peer := do
  pure ⟨← genVector 32, ← genVector 32, ← genSecret⟩

/-- The three messages of a libp2p handshake by EthLib are read by the noiseprotocol package.

The payloads of messages 2 and 3 hold the identity key of their sender.

Their signatures verify for the Noise static key of the sender, which `cryptography` derives.

Each side of EthLib completes with the identity and the extensions of the other. -/
def handshake (oracle : Oracle) : Property IO := propertyM do
  let i ← forAll genPeer
  let r ← forAll genPeer
  let (extsI, extsR) ← forAll (Gen.zip genExts genExts)
  pure do
    let extI ← extBytes oracle extsI
    let extR ← extBytes oracle extsR
    let step {α : Type} (name : String) (x : Except Noise.NoiseError α) : TestT IO α :=
      match x with
      | .ok a => pure a
      | .error e => failWith s!"{name}: {repr e}"
    let a := Noise.initializeLibp2p true i.static i.ephemeral
    let b := Noise.initializeLibp2p false r.static r.ephemeral
    let (a, m1) ← step "write 1" (Noise.writeLibp2p a (Fin.ofNat _ i.identity) none)
    let b ← step "read 1" (Noise.readLibp2p b m1)
    let (b, m2) ← step "write 2" (Noise.writeLibp2p b (Fin.ofNat _ r.identity) extR)
    let a ← step "read 2" (Noise.readLibp2p a m2)
    let (a, m3) ← step "write 3" (Noise.writeLibp2p a (Fin.ofNat _ i.identity) extI)
    let b ← step "read 3" (Noise.readLibp2p b m3)
    let read ← oracle.ask ["noise_libp2p", hexv i.static, hexv i.ephemeral, hexv r.static,
      hexv r.ephemeral, hex m1, hex m2, hex m3]
    let keyOf (identity : Nat) : String := hex (Libp2p.encodePublicKey (publicOf identity))
    read === s!"{keyOf r.identity} 1 {optional extR} {keyOf i.identity} 1 {optional extI}"
    let (remoteOfA, _, _) ← step "the initiator completes" (Noise.complete a)
    let (remoteOfB, _, _) ← step "the responder completes" (Noise.complete b)
    ensure (remoteOfA.key == publicOf r.identity) "the initiator has another identity"
    ensure (remoteOfB.key == publicOf i.identity) "the responder has another identity"
    optional remoteOfA.extensions === optional extR
    optional remoteOfB.extensions === optional extI
    hexv remoteOfA.staticKey === hexv (Cryptography.X25519.publicKey r.static)
    hexv remoteOfB.staticKey === hexv (Cryptography.X25519.publicKey i.static)
    cover 15 "the responder sends extensions" extR.isSome
    cover 15 "the initiator sends extensions" extI.isSome

/-- The first message carries no extensions: EthLib writes none, and refuses to read some.

The Noise specification of libp2p says that the initiator must not send them there. -/
def firstMessage (oracle : Oracle) : Property IO := propertyM do
  let i ← forAll genPeer
  let r ← forAll genPeer
  let exts ← forAll genExts
  let withKey ← forAll Gen.bool
  pure do
    let ext ← extBytes oracle exts
    let a := Noise.initializeLibp2p true i.static i.ephemeral
    if ext.isSome then
      ensure (Noise.writeLibp2p a (Fin.ofNat _ i.identity) ext).toOption.isNone
        "EthLib writes extensions in the first message"
    -- A first message with a payload, written below the libp2p layer.
    let made ← oracle.ask ["noise_make", if withKey then "0802" else "-", "-", exts, "plain"]
    let some payload := unhex? made | failWith s!"oracle: {made}"
    let .ok (_, m1) := Noise.writeMessage a.handshake payload | failWith "writeMessage"
    let b := Noise.initializeLibp2p false r.static r.ephemeral
    (Noise.readLibp2p b m1).toOption.isSome === (exts == "none")
    cover 20 "extensions in the first message" (exts != "none")
    cover 13 "no extensions in the first message" (exts == "none")

/-! ## Frames -/

/-- A message behind its 16-bit length is the frame of the "Wire Format" section.

A message of more than 65535 bytes has no frame. -/
def frames (oracle : Oracle) : Property IO := propertyM do
  let size ← forAll (Gen.frequency [(1, pure 0), (6, Gen.nat (.linear 1 300)),
    (1, Gen.element [255, 256, 65535]), (1, Gen.element [65536, 65537])])
  let fill ← forAll genByte
  pure do
    let message : ByteArray := ⟨Array.replicate size fill⟩
    let want ← oracle.ask ["noise_frame", hex message]
    match Noise.frame message with
    | .ok framed =>
      hex framed === want
      (Noise.unframe framed).toOption.map hex === some (hex message)
    | .error _ => ensure (refused want) "EthLib refuses a message that has a frame"
    cover 3 "a message too long for a frame" (refused want)
    cover 3 "an empty message" (size == 0)

/-- Bytes are one frame exactly when their first two bytes count the bytes after them. -/
def unframes (oracle : Oracle) : Property IO := propertyM do
  let message ← forAllWith hex (genBytes (.linear 0 300))
  let delta ← forAll (Gen.frequency [(4, pure 0), (1, Gen.element [(1 : Int), -1, 256, -256])])
  let cut ← forAll (Gen.frequency [(6, pure none), (1, some <$> Gen.nat (.constant 0 3))])
  pure do
    let declared := ((message.size : Int) + delta).toNat % 65536
    let bytes : ByteArray := ⟨(Base.natToBytes 2 declared).toArray⟩ ++ message
    let bytes := match cut with
      | some n => bytes.extract 0 n
      | none => bytes
    let want ← oracle.ask ["noise_unframe", hex bytes]
    let got := match Noise.unframe bytes with
      | .ok message => hex message
      | .error _ => "error"
    got === verdict want
    cover 7 "valid as generated" (delta == 0 && cut.isNone)
    cover 5 "refused by the reference" (refused want)
    classify "mutated and still accepted by the reference"
      (!(delta == 0 && cut.isNone) && !refused want)

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  let slow := min cases 300
  [("noise: the payload is the protobuf package's", (makes oracle).withTests slow),
   ("noise: a payload in every form of the encoding", (reads oracle).withTests cases),
   ("noise: a payload with a changed byte", (readsChanged oracle).withTests cases),
   ("noise: field number 0 in a group is refused, as documented",
     (groupZero oracle).withTests (min cases 100)),
   ("noise: a payload authenticates as the specification says",
     (authenticates oracle).withTests slow),
   ("noise: noiseprotocol reads a libp2p handshake", (handshake oracle).withTests (min cases 100)),
   ("noise: no extensions in the first message", (firstMessage oracle).withTests (min cases 100)),
   ("noise: a message behind its length", (frames oracle).withTests cases),
   ("noise: bytes read as one frame", (unframes oracle).withTests cases)]

end DecodersProperty.Devp2p.NoiseId
