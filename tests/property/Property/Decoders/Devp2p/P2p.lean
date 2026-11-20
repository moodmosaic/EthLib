import Hedgehog
import Support
import Property.Decoders.Devp2p.Common
import EthLib.Networking.Devp2p.Session

/-!
# The "p2p" capability of devp2p, on generated inputs

The reference is written from `rlpx.md`, with the `rlp` package for the bytes.

Its Snappy reader is written from `format_description.txt`, and its writer is cramjam.
-/

open Hedgehog Support EthLib EthLib.Networking
open EthLib.Networking.Devp2p
open EthLib.Serialization.Rlp (Item)

namespace DecodersProperty.Devp2p.P2p

open DecodersProperty DecodersProperty.Devp2p

/-! ## Messages as text and as items -/

/-- A capability as the oracle writes it. -/
def capText (c : Capability) : String := s!"{hex c.name}/{c.version}"

/-- A list of capabilities as the oracle writes it. -/
def capsText (cs : List Capability) : String :=
  if cs.isEmpty then "-" else ";".intercalate (cs.map capText)

/-- A message as the oracle writes it. -/
def describe : Message → String
  | .hello h => "|".intercalate ["hello", toString h.protocolVersion, hex h.clientId,
      capsText h.capabilities, toString h.listenPort, hexv h.nodeId]
  | .disconnect none => "disconnect|none"
  | .disconnect (some r) => s!"disconnect|{r}"
  | .ping => "ping"
  | .pong => "pong"

/-- The RLP list of a Hello, written here from `rlpx.md`. -/
def helloItem (h : Hello) (extra : List Item := []) : Item :=
  .list ([natItem h.protocolVersion, .bytes h.clientId,
    .list (h.capabilities.map fun c => .list [.bytes c.name, natItem c.version]),
    natItem h.listenPort, .bytes ⟨h.nodeId.toArray⟩] ++ extra)

/-- The RLP list of a message, written here from `rlpx.md`. -/
def bodyItem : Message → Item
  | .hello h => helloItem h
  | .disconnect none => .list []
  | .disconnect (some r) => .list [natItem r]
  | .ping | .pong => .list []

/-! ## Generators -/

/-- A name of a capability: names that share a prefix, differ in case, or are empty. -/
def genName : Gen ByteArray :=
  String.toUTF8 <$> Gen.element ["eth", "snap", "les", "Eth", "et", "ethh", "", "wit"]

/-- A version: small ones that collide, the versions of eth, and ones past a byte and a word. -/
def genVersion : Gen Nat :=
  Gen.frequency [(6, Gen.nat (.constant 0 3)), (2, Gen.nat (.constant 66 69)),
    (1, Gen.element [127, 128, 255, 256, 2 ^ 64])]

/-- A capability. -/
def genCapability : Gen Capability := Gen.zipWith Capability.mk genName genVersion

/-- A version of the "p2p" capability: around 5, where Snappy starts, and far from it. -/
def genP2pVersion : Gen Nat :=
  Gen.frequency [(8, Gen.nat (.constant 3 6)), (1, Gen.element [0, 1, 127, 128, 255, 256, 2 ^ 64])]

/-- A Hello. -/
def genHello : Gen Hello := do
  let version ← genP2pVersion
  let client ← genBytes (.linear 0 20)
  let caps ← Gen.list (.linear 0 5) genCapability
  let port ← Gen.element [0, 1, 127, 128, 30303, 65535, 65536, 2 ^ 64]
  pure ⟨version, client, caps, port, ← genVector 64⟩

/-- A reason of Disconnect: none, one of the table, one near it, one far from it. -/
def genReason : Gen (Option Nat) :=
  Gen.frequency [(1, pure none), (5, some <$> Gen.nat (.constant 0 17)),
    (1, some <$> Gen.element [0x7f, 0x80, 0xff, 0x100, 2 ^ 64])]

/-- A message of each of the four kinds. -/
def genMessage : Gen Message :=
  Gen.frequency [(4, Message.hello <$> genHello), (3, Message.disconnect <$> genReason),
    (1, pure .ping), (1, pure .pong)]

/-! ## Encoding -/

/-- What EthLib writes is what the reference reads, and uncompressed it is the reference's bytes.

EthLib then reads its own bytes back. -/
def encodes (oracle : Oracle) : Property IO := propertyM do
  let m ← forAllWith describe genMessage
  let snappy ← forAll Gen.bool
  pure do
    let .ok bytes := encodeMessage snappy m | failWith "encodeMessage refuses"
    annotate s!"frame data: {hex bytes}"
    (← oracle.ask ["p2p_dec", flag snappy, hex bytes]) === describe m
    let compressed := snappy && m.id != 0
    if !compressed then
      hex bytes === (← oracle.ask ["p2p_frame", "0", itemText (natItem m.id),
        itemText (bodyItem m), "-"])
    match decodeMessage snappy bytes with
    | .ok back => describe back === describe m
    | .error _ => failWith "EthLib refuses its own bytes"
    cover 14 "hello" (m.id == 0)
    cover 10 "disconnect" (m.id == 1)
    cover 5 "ping or pong" (m.id ≥ 2)
    cover 9 "compressed" compressed

/-- The Hello of the test vectors of EIP-8, which holds additional list elements.

EthLib reads its five fields as the reference does, and ignores the rest. -/
def eip8Hello (oracle : Oracle) : Property IO := propertyM do
  pure do
    let vector :=
      "f87137916b6e6574682f76302e39312f706c616e39cdc5836574683dc6846d6f726b1682270fb840" ++
      "fda1cff674c90c9a197539fe3dfb53086ace64f83ed7c6eabec741f7f381cc803e52ab2cd55d5569" ++
      "bce4347107a310dfd5f88a010cd2ffd1005ca406f1842877c883666f6f836261720304"
    -- The ID 0 is the empty byte string, then the message follows.
    let some frame := unhex? ("80" ++ vector) | failWith "the vector is not hexadecimal"
    let want := "hello|55|" ++ hex "kneth/v0.91/plan9".toUTF8 ++ "|" ++ hex "eth".toUTF8 ++
      "/61;" ++ hex "mork".toUTF8 ++ "/22|9999|" ++
      "fda1cff674c90c9a197539fe3dfb53086ace64f83ed7c6eabec741f7f381cc803e52ab2cd55d5569" ++
      "bce4347107a310dfd5f88a010cd2ffd1005ca406f1842877"
    (← oracle.ask ["p2p_dec", "0", hex frame]) === want
    match decodeMessage true frame with
    | .ok m => describe m === want
    | .error e => failWith s!"EthLib refuses the vector: {repr e}"

/-! ## Decoding -/

/-- Frame data to write, and how to read it. -/
structure Frame where
  id : Item
  body : Item
  tail : ByteArray
  written : Bool
  read : Bool
  change : Option (Nat × Nat × UInt8)
  tweaked : Bool

instance : Repr Frame where
  reprPrec f _ := s!"id {itemText f.id} body {itemText f.body} tail {hex f.tail} " ++
    s!"written {f.written} read {f.read} change {repr f.change}"

/-- An item of the wrong shape or size for some field. -/
def genOddItem : Gen Item :=
  Gen.element [.bytes .empty, .list [], .bytes ⟨#[0]⟩, .bytes ⟨#[0, 1]⟩, .bytes ⟨#[1]⟩,
    .bytes ⟨#[0x80]⟩, .bytes ⟨Array.replicate 63 1⟩, .bytes ⟨Array.replicate 64 1⟩,
    .bytes ⟨Array.replicate 65 1⟩, .list [.bytes ⟨#[1]⟩], .list [.list []],
    .list [.list [.bytes ⟨#[0x65]⟩, .bytes ⟨#[1]⟩]], .list [.list [.bytes ⟨#[0x65]⟩]],
    .list [.list [.bytes ⟨#[0x65]⟩, .bytes ⟨#[1]⟩, .bytes ⟨#[2]⟩]],
    .list [.list [.list [], .bytes ⟨#[1]⟩]], .list [.list [.bytes ⟨#[0x65]⟩, .bytes ⟨#[0, 1]⟩]]]

/-- An ID that names no message, or names one in another form. -/
def genOddId : Gen Item :=
  Gen.element [.bytes ⟨#[0]⟩, .bytes ⟨#[0, 1]⟩, .list [], .bytes ⟨#[4]⟩, .bytes ⟨#[0x10]⟩,
    .bytes ⟨#[0x7f]⟩, .bytes ⟨#[0x80]⟩, .bytes ⟨#[1, 0]⟩, .bytes ⟨#[1]⟩, .bytes ⟨#[2]⟩,
    .bytes ⟨#[3]⟩, .bytes .empty]

/-- The fields of a list, or the item alone. -/
def fieldsOf : Item → List Item
  | .list items => items
  | item => [item]

/-- Frame data of a message, as it is or with one thing changed. -/
def genFrame : Gen Frame := do
  let m ← genMessage
  let snappy ← Gen.bool
  let plain : Frame := ⟨natItem m.id, bodyItem m, .empty, snappy, snappy, none, false⟩
  let fields := fieldsOf plain.body
  Gen.frequency [
    (8, pure plain),
    (3, do
      let at_ ← Gen.nat (.constant 0 4)
      let odd ← genOddItem
      pure { plain with tweaked := true, body := .list (fields.mapIdx fun j f =>
        if j = at_ % fields.length then odd else f) }),
    (2, (fun odd => { plain with tweaked := true, body := .list (fields ++ [odd]) }) <$>
      genOddItem),
    (1, pure { plain with tweaked := true, body := .list fields.dropLast }),
    (2, (fun odd => { plain with tweaked := true, id := odd }) <$> genOddId),
    (1, (fun tail => { plain with tweaked := true, tail }) <$> genBytes (.linear 1 3)),
    (1, pure { plain with tweaked := true, read := !snappy }),
    (4, (fun change => { plain with tweaked := true, change := some change }) <$> genChange)]

/-- Frame data reads as `rlpx.md` says, or is refused.

The data is that of a message, as it is or with one thing changed.

The change is a field of another shape, an element more or less, or another ID.

It may also be bytes after the message, the other compression, or one changed byte. -/
def decodes (oracle : Oracle) : Property IO := propertyM do
  let f ← forAll genFrame
  pure do
    let made ← oracle.ask ["p2p_frame", flag f.written, itemText f.id, itemText f.body, hex f.tail]
    let some bytes := unhex? made | failWith s!"oracle: {made}"
    let bytes := match f.change with
      | some change => mutate change bytes
      | none => bytes
    annotate s!"frame data: {hex bytes}"
    let want ← oracle.ask ["p2p_dec", flag f.read, hex bytes]
    let got := match decodeMessage f.read bytes with
      | .ok m => describe m
      | .error _ => "error"
    got === verdict want
    let valid := !f.tweaked
    cover 7 "valid as generated" (valid && !refused want)
    cover 1 "mutated and still accepted by the reference" (!valid && !refused want)
    cover 5 "refused by the reference" (refused want)
    classify "hello accepted" (want.startsWith "hello")
    classify "disconnect accepted" (want.startsWith "disconnect")
    classify "read compressed" f.read

/-! ## The reasons of Disconnect -/

/-- The name of a reason as EthLib's constructor spells it. -/
def reasonName (r : DisconnectReason) : String :=
  ((reprStr r).splitOn ".").getLastD ""

/-- The table of reasons is that of `rlpx.md`, and a number outside it has no reason. -/
def reasons (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll (Gen.frequency [(6, Gen.nat (.constant 0 17)), (1, Gen.nat (.linear 18 300)),
    (1, Gen.element [0x7f, 0x80, 0xff, 0x100, 0x110, 2 ^ 64])])
  pure do
    let want ← oracle.ask ["p2p_reason", toString n]
    match DisconnectReason.ofNat? n with
    | some r =>
      reasonName r === want
      r.toNat === n
    | none => want === "none"
    cover 18 "in the table" (want != "none")
    cover 14 "outside the table" (want == "none")

/-! ## Shared capabilities -/

/-- The number of IDs of a capability: an entry of a table, chosen by its name and version.

The oracle computes the same number from the same table. -/
def lengthOf (lens : List Nat) (c : Capability) : Nat :=
  lens.getD ((c.name.data.foldl (fun sum b => sum + b.toNat) 0 + c.version) % lens.length) 0

/-- A table of lengths, in which a capability may need no ID at all. -/
def genLens : Gen (List Nat) :=
  Gen.list (.constant 1 5) (Gen.frequency [(5, Gen.nat (.constant 1 21)), (1, pure 0)])

/-- The table as the oracle reads it. -/
def lensText (lens : List Nat) : String := ",".intercalate (lens.map toString)

/-- A list of capabilities: versions collide, so that some name has two of them. -/
def genCaps : Gen (List Capability) :=
  Gen.list (.linear 0 7) (Gen.zipWith Capability.mk genName (Gen.frequency
    [(8, Gen.nat (.constant 0 2)), (1, Gen.element [255, 256, 2 ^ 64])]))

/-- A few capabilities with small versions, so that two lists of them often meet. -/
def genFewCaps (range : Range Nat) : Gen (List Capability) :=
  Gen.list range (Gen.zipWith Capability.mk genName (Gen.nat (.constant 0 2)))

/-- The lists of two peers: each holds a common part, and more, in any order. -/
def genPeers : Gen (List Capability × List Capability) := do
  let common ← genFewCaps (.constant 0 4)
  let side : Gen (List Capability) := do
    let more ← Gen.frequency [(2, pure []), (2, genFewCaps (.constant 1 3)), (1, genCaps)]
    Gen.shuffle (common ++ more)
  Gen.frequency [(6, Gen.zip side side), (1, Gen.zip genCaps genCaps)]

/-- Offsets as the oracle writes them. -/
def offsetsText (offsets : List (Capability × Nat)) : String :=
  if offsets.isEmpty then "-"
  else ";".intercalate (offsets.map fun (c, at_) => s!"{capText c}@{at_}")

/-- The shared capabilities and their first IDs are those of "Message ID-based Multiplexing".

Every ID then goes to the capability whose block holds it, or to none. -/
def negotiates (oracle : Oracle) : Property IO := propertyM do
  let (ours, theirs) ← forAllWith (fun (a, b) => s!"{capsText a} and {capsText b}") genPeers
  let lens ← forAll genLens
  let id ← forAll (Gen.frequency [(1, Gen.nat (.constant 0 15)), (4, Gen.nat (.constant 16 60))])
  pure do
    let offsets := negotiate (lengthOf lens) ours theirs
    let want ← oracle.ask ["p2p_negotiate", capsText ours, capsText theirs, lensText lens]
    offsetsText offsets === want
    let routed := match route (lengthOf lens) offsets id with
      | some (c, relative) => s!"{capText c}/{relative}"
      | none => "none"
    routed === (← oracle.ask ["p2p_route", capsText ours, capsText theirs, lensText lens,
      toString id])
    let names := offsets.map (·.1.name)
    let both (c : Capability) : Bool := decide (c ∈ ours) && decide (c ∈ theirs)
    cover 9 "none shared" offsets.isEmpty
    cover 6 "one shared" (offsets.length == 1)
    cover 16 "two or more shared" (offsets.length ≥ 2)
    cover 4 "two versions of one name shared"
      (ours.any fun c => both c && ours.any fun d => both d && d.name == c.name &&
        d.version != c.version)
    cover 5 "the ID is in a block" (routed != "none")
    classify "a name twice in the result" (names.eraseDups.length != names.length)

/-- Both peers use Snappy exactly when both versions are at least 5, as EIP-706 says. -/
def snappyVersions : Property IO := pureIO do
  let ours ← forAll genP2pVersion
  let theirs ← forAll genP2pVersion
  snappyEnabled ours theirs === (decide (ours ≥ 5) && decide (theirs ≥ 5))
  cover 9 "both compress" (ours ≥ 5 && theirs ≥ 5)
  cover 15 "one is older" ((ours ≥ 5) != (theirs ≥ 5))
  cover 5 "both are older" (ours < 5 && theirs < 5)

/-! ## The bound of 16 MiB -/

/-- A compressed message is refused as too large exactly when it declares more than 16 MiB.

The block holds only its preamble and a few bytes.

So a block within the bound is refused later, by the Snappy reader, and not as too large. -/
def declared (oracle : Oracle) : Property IO := propertyM do
  let size ← forAll (Gen.frequency [
    (4, (fun (d : Nat) => 2 ^ 24 + 5 - d) <$> Gen.nat (.constant 0 10)),
    (2, Gen.element [0, 1, 2 ^ 21 - 1, 2 ^ 21, 2 ^ 28, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 35]),
    (1, Gen.nat (.exponential 0 (2 ^ 33)))])
  let tail ← forAll (genBytes (.linear 0 3))
  pure do
    let made ← oracle.ask ["snappy_declare", toString size, hex tail]
    let some block := unhex? made | failWith s!"oracle: {made}"
    -- The ID of a Ping, then the block.
    let frame := (⟨#[2]⟩ : ByteArray) ++ block
    let want ← oracle.ask ["p2p_dec", "1", hex frame]
    let wantLarge := want.startsWith "error MalformedError too large"
    match decodeMessage true frame with
    | .error (.tooLarge n) =>
      ensure wantLarge s!"EthLib says too large, the reference says {want}"
      n === size
    | .error _ => ensure (refused want && !wantLarge) s!"the reference says {want}"
    | .ok m => describe m === want
    cover 11 "declares more than 16 MiB" wantLarge
    cover 20 "declares at most 16 MiB" (!wantLarge)
    classify "declares exactly 16 MiB" (size == 2 ^ 24)

/-- A message of a capability passes with 16 MiB of data, and not with one byte more.

The data is real: zero bytes as they are, or in a Snappy block that cramjam wrote.

The bound is that of "Message Encoding": more than 16 MiB of uncompressed data is rejected.

The one test case runs the three sizes around the bound, each plain and compressed. -/
def large (oracle : Oracle) : Property IO := propertyM do
  pure do
    for size in [2 ^ 24 - 1, 2 ^ 24, 2 ^ 24 + 1] do
      for snappy in [false, true] do
        let case := s!"{size} bytes, compressed {snappy}"
        let data ← if snappy then do
            let made ← oracle.ask ["snappy_zeros", toString size]
            let some block := unhex? made | failWith "oracle"
            pure block
          else pure ⟨Array.replicate size 0⟩
        let eth : Capability := ⟨"eth".toUTF8, 68⟩
        let hello : Hello := ⟨5, .empty, [eth], 0, Vector.replicate 64 1⟩
        let phase : Phase := .active hello hello snappy [(eth, 0x10)]
        match receive (fun _ => 17) hello phase ((⟨#[0x11]⟩ : ByteArray) ++ data) with
        | .ok (_, some (.capability c relative got), _) =>
          ensure (size ≤ 2 ^ 24) s!"{case}: a message of more than 16 MiB passes"
          ensure (c == eth && relative == 1 && got.size == size) s!"{case}: another message"
        | .ok _ => failWith s!"{case}: the frame carries no message of a capability"
        | .error (.tooLarge n) =>
          ensure (size > 2 ^ 24 && !snappy && n == size) s!"{case}: too large after reading"
        | .error (.message (.tooLarge n)) =>
          ensure (size > 2 ^ 24 && snappy && n == size) s!"{case}: too large as declared"
        | .error e => failWith s!"{case}: refused with {repr e}"

/-! ## A session -/

/-- The phase of a session, as the model holds it. -/
inductive ModelPhase where
  | await
  | active (theirs : List Capability) (snappy : Bool)
  | closed (reason : Option Nat) (after : Nat)

/-- A session: EthLib's phase, the model's, and what both sides fixed at the start. -/
structure Session where
  ours : Hello
  lens : List Nat
  phase : Phase
  model : ModelPhase
  /-- The frames delivered so far. -/
  count : Nat := 0

/-- The start of a session, with our Hello and the table of lengths. -/
def genSession : Gen Session := do
  let version ← Gen.frequency [(3, pure 5), (1, pure 4), (1, Gen.element [3, 6, 255])]
  let caps ← Gen.list (.constant 1 5) (Gen.zipWith Capability.mk
    (String.toUTF8 <$> Gen.element ["eth", "snap", "les"]) (Gen.nat (.constant 0 2)))
  let lens ← Gen.list (.constant 1 4) (Gen.nat (.constant 1 9))
  let ours : Hello := ⟨version, "ours".toUTF8, caps, 0, ← genVector 64⟩
  pure { ours, lens, phase := .awaitHello, model := .await }

/-- EthLib's phase in the words of the model. -/
def phaseText : Phase → String
  | .awaitHello => "await"
  | .active _ theirs snappy offsets =>
    s!"active {capsText theirs.capabilities} {snappy} {offsetsText offsets}"
  | .closed reason => s!"closed {reason}"

/-- The oracle and nothing else: a command holds what is its own. -/
abbrev Context := Oracle

/-- What the reference and EthLib say of one frame in the state, compared.

The model then moves as `rlpx.md` says, and EthLib's phase must be the model's. -/
def deliver (oracle : Oracle) (s : Session) (frame : ByteArray) : TestT IO Session := do
  annotate s!"frame data: {hex frame}"
  let (phase, theirs, snappy) : String × List Capability × Bool := match s.model with
    | .await => ("await", [], false)
    | .active theirs snappy => ("active", theirs, snappy)
    | .closed .. => ("closed", [], false)
  let want ← oracle.ask ["p2p_receive", phase, capsText s.ours.capabilities, capsText theirs,
    lensText s.lens, flag snappy, hex frame]
  let s := { s with count := s.count + 1 }
  match receive (lengthOf s.lens) s.ours s.phase frame with
  | .error e =>
    ensure (refused want) s!"EthLib refuses with {repr e}, the reference reads {want}"
    classify "a frame before the Hello is refused" (phase == "await")
    classify "a frame after a Disconnect is refused" (phase == "closed")
    classify "a frame of an active session is refused" (phase == "active")
    match s.model with
    | .closed reason after => pure { s with model := .closed reason (after + 1) }
    | _ => pure s
  | .ok (next, event, actions) =>
    let got := match event with
      | some (.p2p m) => describe m
      | some (.capability c relative data) => s!"cap|{capText c}/{relative}|{hex data}"
      | none => "nothing"
    got === want
    actions === (if want == "ping" then [Action.sendPong] else [])
    let model : ModelPhase := match event, s.model with
      | some (.p2p (.hello theirs)), .await =>
        .active theirs.capabilities
          (decide (s.ours.protocolVersion ≥ 5) && decide (theirs.protocolVersion ≥ 5))
      | some (.p2p (.disconnect reason)), _ => .closed reason 0
      | _, model => model
    let expected ← match model with
      | .await => pure "await"
      | .active theirs snappy =>
        let offsets ← oracle.ask ["p2p_negotiate", capsText s.ours.capabilities, capsText theirs,
          lensText s.lens]
        pure s!"active {capsText theirs} {snappy} {offsets}"
      | .closed reason _ => pure s!"closed {reason}"
    phaseText next === expected
    cover 22 "a Hello opens the session" (want.startsWith "hello")
    cover 7 "a Disconnect closes the session" (want.startsWith "disconnect")
    cover 9 "a Ping asks for a Pong" (want == "ping")
    cover 10 "a capability gets its message" (want.startsWith "cap")
    cover 9 "a compressed message is read" (snappy && phase == "active")
    pure { s with phase := next, model }

/-- Frame data by the reference, compressed as the session asks unless the command says. -/
def frameOf (oracle : Oracle) (s : Session) (compress : Option Bool) (id : Nat) (body : Item) :
    TestT IO ByteArray := do
  let snappy := match s.model with
    | .active _ snappy => snappy && id != 0
    | _ => false
  let made ← oracle.ask ["p2p_frame", flag (compress.getD snappy), itemText (natItem id),
    itemText body, "-"]
  let some bytes := unhex? made | failWith s!"oracle: {made}"
  pure bytes

/-- At most two frames go to a closed session: each must be refused. -/
def open_ (s : Session) : Bool :=
  match s.model with
  | .closed _ after => after < 2
  | _ => true

/-- The peer sends its Hello, now and then with elements that a later version would add. -/
structure SendHello where
  hello : Hello
  extra : List Item

instance : Command SendHello Session Context IO where
  check _ _ s := open_ s
  apply oracle c s := do
    deliver oracle s (← frameOf oracle s none 0 (helloItem c.hello c.extra))
  label c := s!"HELLO({describe (.hello c.hello)}, {c.extra.length} more)"
  build _ := do
    let extra ← Gen.frequency [(4, pure []), (1, Gen.list (.constant 1 2) genOddItem)]
    pure ⟨← genHello, extra⟩
  buildIn _ s := do
    -- The peer shares a part of our capabilities, and has some of its own.
    let version ← Gen.frequency [(3, pure 5), (1, pure 4), (1, Gen.element [3, 6, 255])]
    let part ← Gen.subsequence s.ours.capabilities
    let more ← Gen.list (.constant 0 3) (Gen.zipWith Capability.mk
      (String.toUTF8 <$> Gen.element ["eth", "snap", "les", "wit"]) (Gen.nat (.constant 0 2)))
    let caps ← Gen.shuffle (part ++ more)
    let extra ← Gen.frequency [(4, pure []), (1, Gen.list (.constant 1 2) genOddItem)]
    pure ⟨⟨version, "theirs".toUTF8, caps, 30303, ← genVector 64⟩, extra⟩
  next _ c s :=
    let snappy := decide (s.ours.protocolVersion ≥ 5) && decide (c.hello.protocolVersion ≥ 5)
    match s.model with
    | .await => { s with model := .active c.hello.capabilities snappy }
    | _ => s

/-- The peer sends a Disconnect, once the session has seen some frames.

A session that closes at once tests little, so most commands of this type wait. -/
structure SendDisconnect where
  reason : Option Nat
  patience : Nat

instance : Command SendDisconnect Session Context IO where
  check _ c s := open_ s && c.patience ≤ s.count
  apply oracle c s := do
    deliver oracle s (← frameOf oracle s none 1 (bodyItem (.disconnect c.reason)))
  label c := s!"DISCONNECT({c.reason}, after {c.patience})"
  build _ := Gen.zipWith SendDisconnect.mk genReason
    (Gen.frequency [(1, pure 0), (4, Gen.nat (.constant 5 30))])
  next _ c s := { s with model := .closed c.reason 0 }

/-- The peer sends a Ping or a Pong. -/
structure SendPing where
  pong : Bool

instance : Command SendPing Session Context IO where
  check _ _ s := open_ s
  apply oracle c s := do
    deliver oracle s (← frameOf oracle s none (if c.pong then 3 else 2) (.list []))
  label c := if c.pong then "PONG" else "PING"
  build _ := SendPing.mk <$> Gen.bool

/-- The peer sends a message of a capability: its ID is in a block, or just outside the blocks.

The command is generated for the state that the commands before it lead to.

So it knows how many capabilities the peer's Hello shares with ours. -/
structure SendCapability where
  id : Nat
  data : Item

instance : Command SendCapability Session Context IO where
  check _ _ s := open_ s
  apply oracle c s := do
    deliver oracle s (← frameOf oracle s none c.id c.data)
  label c := s!"CAPABILITY({c.id}, {itemText c.data})"
  build _ := Gen.zipWith SendCapability.mk (Gen.nat (.constant 0x10 0x30)) genOddItem
  buildIn _ s := do
    -- The blocks end where the lengths of the shared capabilities end.
    let span := match s.model with
      | .active theirs _ =>
        ((s.ours.capabilities.filter (· ∈ theirs)).map (lengthOf s.lens)).sum
      | _ => 8
    let id ← Gen.frequency [(6, Gen.nat (.constant 0x10 (0x10 + span))),
      (1, Gen.nat (.constant 4 0x0f)), (1, pure (0x10 + span + 1))]
    SendCapability.mk id <$> genOddItem

/-- The peer sends frame data with the other compression than the session's. -/
structure SendMiscompressed where
  id : Nat

instance : Command SendMiscompressed Session Context IO where
  check _ _ s := open_ s
  apply oracle c s := do
    let snappy := match s.model with
      | .active _ snappy => snappy
      | _ => false
    deliver oracle s (← frameOf oracle s (some !snappy) c.id (.list []))
  label c := s!"MISCOMPRESSED({c.id})"
  build _ := SendMiscompressed.mk <$> Gen.element [1, 2, 3, 0x10, 0x11]

/-- The peer sends a frame of the session with one byte changed.

EthLib must refuse it, or read what the reference reads. -/
structure SendCorrupt where
  id : Nat
  body : Item
  change : Nat × Nat × UInt8

instance : Command SendCorrupt Session Context IO where
  check _ _ s := open_ s
  apply oracle c s := do
    deliver oracle s (mutate c.change (← frameOf oracle s none c.id c.body))
  label c := s!"CORRUPT({c.id}, {itemText c.body}, {repr c.change})"
  build _ := do
    let (id, body) ← Gen.frequency [
      (2, (fun h => (0, helloItem h)) <$> genHello),
      (1, pure (2, .list [])),
      (3, Gen.zip (Gen.nat (.constant 0x10 0x18)) genOddItem)]
    SendCorrupt.mk id body <$> genChange

/-- A session of the "p2p" capability, against a model written from `rlpx.md`.

Each frame carries what the reference reads in the phase of the model, or is refused.

The phase of EthLib after it is that of the model, with the offsets of the reference. -/
def session (oracle : Oracle) : Property IO :=
  scenarioFrom genSession .madhouse oracle [
    Command.gen SendHello, Command.gen SendHello, Command.gen SendPing, Command.gen SendPing,
    Command.gen SendCapability, Command.gen SendCapability, Command.gen SendCapability,
    Command.gen SendCapability, Command.gen SendDisconnect, Command.gen SendMiscompressed,
    Command.gen SendCorrupt, Command.gen SendCorrupt] (.linear 1 40)
    fun s => do
      annotate s!"ours: {describe (.hello s.ours)}, lengths {s.lens}"
      pure s

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("devp2p: the reference reads EthLib's message", (encodes oracle).withTests cases),
  ("devp2p: the Hello of EIP-8 with additional elements", (eip8Hello oracle).withTests 1),
  ("devp2p: frame data reads as rlpx.md says", (decodes oracle).withTests cases),
  ("devp2p: the reasons of Disconnect", (reasons oracle).withTests cases),
  ("devp2p: shared capabilities and their message IDs", (negotiates oracle).withTests cases),
  ("devp2p: Snappy from version 5 of both peers", snappyVersions.withTests cases),
  ("devp2p: a message that declares more than 16 MiB", (declared oracle).withTests cases),
  ("devp2p: 16 MiB of data pass, and one byte more does not",
    (large oracle).withTests 1),
  ("devp2p: a session against its model (Command, madhouse)",
    (session oracle).withTests cases)]

end DecodersProperty.Devp2p.P2p
