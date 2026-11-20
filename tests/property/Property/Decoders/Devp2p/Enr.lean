import Hedgehog
import Support
import Property.Decoders.Devp2p.Common
import EthLib.Networking.Enr.Consensus
import EthLib.Networking.Enr.Eth

/-!
# The entries of a node record, on generated inputs

The consensus entries are those of the `p2p-interface.md` of phase0, altair and fulu.

The reference reads them with remerkleable, beside a reader written from the SSZ rules.

The "eth" entry is that of `enr-entries/eth.md`, read with the `rlp` package.
-/

open Hedgehog Support EthLib EthLib.Networking
open EthLib.Networking.Enr
open EthLib.Base (Fork)
open EthLib.Serialization.Rlp (Item)

namespace DecodersProperty.Devp2p.Enr

open DecodersProperty DecodersProperty.Devp2p

/-- Every fork, in the order of the type. -/
def allForks : List Fork :=
  [.frontier, .homestead, .daoFork, .tangerineWhistle, .spuriousDragon, .byzantium,
    .constantinople, .petersburg, .istanbul, .muirGlacier, .phase0, .berlin, .london, .altair,
    .arrowGlacier, .grayGlacier, .bellatrix, .paris, .shapella, .dencun, .pectra, .fusaka, .bpo1,
    .bpo2, .bpo3, .bpo4, .bpo5, .glamsterdam, .hegota]

/-- The forks at which a consensus layer exists. -/
def consensusForks : List Fork := allForks.filter (Fork.phase0 ≤ ·)

/-! ## The consensus entries -/

/-- Bits as the bytes of an SSZ bitvector: bit `i` is bit `i % 8` of byte `i / 8`. -/
def bitBytes (bits : List Bool) : ByteArray :=
  ⟨Array.ofFn (n := (bits.length + 7) / 8) fun i =>
    (List.range 8).foldl (fun byte j =>
      if bits.getD (8 * i.val + j) false then byte ||| (1 <<< UInt8.ofNat j) else byte) 0⟩

/-- A value of an entry: what it is in the record, and whether the generator meant it valid. -/
structure Value where
  item : Option Item
  valid : Bool

/-- The value of a key: mostly a valid one, now and then none or a malformed one. -/
def genValue (valid : Gen ByteArray) (bad : Gen Item) (absent : Nat := 1) (malformed : Nat := 1) :
    Gen Value :=
  Gen.frequency [(12, (fun b => ⟨some (.bytes b), true⟩) <$> valid),
    (absent, pure ⟨none, false⟩), (malformed, (fun i => ⟨some i, false⟩) <$> bad)]

/-- Bytes of one of the sizes, or a list. -/
def genWrongSize (sizes : List Nat) : Gen Item :=
  Gen.frequency [(4, Gen.element sizes >>= fun n => Item.bytes <$> genBytes (.singleton n)),
    (1, pure (.list [.bytes ⟨#[1]⟩]))]

/-- An attestation bitfield of `count` bits, or one of another size, or with a bit past its end. -/
def genAttnets (count : Nat) : Gen Value :=
  let size := (count + 7) / 8
  let valid := (fun bits => bitBytes bits) <$> Gen.list (.singleton count) Gen.bool
  let padded : Gen Item := do
    let bytes ← valid
    let bit ← Gen.nat (.constant (count % 8) 7)
    pure (.bytes (bytes.set! (size - 1) (bytes[size - 1]! ||| (1 <<< UInt8.ofNat bit))))
  genValue valid (Gen.frequency [(2, genWrongSize [0, size - 1, size + 1]),
    (if count % 8 == 0 then 0 else 4, padded)]) (absent := 2) (malformed := 2)

/-- A sync committee bitfield: one byte below 16, or a byte with a bit past the fourth. -/
def genSyncnets : Gen Value :=
  genValue ((fun (n : Nat) => ⟨#[UInt8.ofNat n]⟩) <$> Gen.nat (.constant 0 15))
    (Gen.frequency [(2, genWrongSize [0, 2]),
      (3, (fun (n : Nat) => Item.bytes ⟨#[UInt8.ofNat n]⟩) <$> Gen.nat (.constant 16 255))])
    (absent := 2)

/-- A custody group count: a scalar below 2^64, or one with a leading zero, or one too large. -/
def genCgc : Gen Value :=
  genValue ((fun n => ⟨(natBytes n).toArray⟩) <$> Gen.frequency [
      (3, Gen.element [0, 1, 4, 8, 127, 128, 255, 256, 2 ^ 63, 2 ^ 64 - 1]), (2, genNatBits 64)])
    (Gen.element [.bytes ⟨#[0]⟩, .bytes ⟨#[0, 1]⟩, .bytes ⟨#[0, 0, 0, 0, 0, 0, 0, 1]⟩,
      .bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩, .bytes ⟨Array.replicate 9 0xff⟩, .list [],
      .list [.bytes ⟨#[4]⟩]])

/-- The pairs of a record with the consensus entries, and whether each is as it should be. -/
structure Entries where
  count : Nat
  fork : Fork
  eth2 : Value
  attnets : Value
  syncnets : Value
  cgc : Value
  nfd : Value
  /-- Whether the consensus pairs come after the other pairs of the record. -/
  last : Bool

/-- The pairs of the record: the entries that are present, among pairs of other keys. -/
def Entries.pairs (e : Entries) : List (ByteArray × Item) :=
  let consensus := [("eth2", e.eth2), ("attnets", e.attnets), ("syncnets", e.syncnets),
    ("cgc", e.cgc), ("nfd", e.nfd)].filterMap fun (key, value) =>
      value.item.map fun item => (key.toUTF8, item)
  let others : List (ByteArray × Item) := [("id".toUTF8, .bytes "v4".toUTF8),
    ("eth".toUTF8, .list [.list [.bytes ⟨#[1, 2, 3, 4]⟩, .bytes .empty]])]
  if e.last then others ++ consensus else consensus.reverse ++ others

/-- The pairs as the oracle reads them. -/
def pairsText (pairs : List (ByteArray × Item)) : String :=
  if pairs.isEmpty then "-"
  else ";".intercalate (pairs.map fun (key, item) => s!"{hex key}={itemText item}")

instance : Repr Entries where
  reprPrec e _ := s!"count {e.count} fork {e.fork.name} pairs {pairsText e.pairs}"

/-- A number of attestation subnets: 64 as on mainnet, and every other length of the bitfield. -/
def genCount : Gen Nat :=
  Gen.frequency [(3, pure 64), (3, Gen.nat (.constant 1 24)), (2, Gen.nat (.constant 57 72)),
    (1, Gen.element [128, 255, 256, 257, 1000])]

/-- A record with the consensus entries, at a fork of the consensus layer. -/
def genEntries : Gen Entries := do
  let count ← genCount
  let fork ← Gen.element consensusForks
  let eth2 ← genValue (genBytes (.singleton 16)) (genWrongSize [0, 15, 17]) (absent := 1)
  let attnets ← genAttnets count
  let syncnets ← genSyncnets
  let cgc ← genCgc
  let nfd ← genValue (genBytes (.singleton 4)) (genWrongSize [0, 3, 5])
  pure ⟨count, fork, eth2, attnets, syncnets, cgc, nfd, ← Gen.bool⟩

/-- Bits as the oracle writes them. -/
def bitsText {n : Nat} (b : Serialization.Ssz.Bitvector n) : String :=
  String.ofList (b.bits.toList.map fun bit => if bit then '1' else '0')

/-- An optional value as the oracle writes it. -/
def optional {α : Type} (text : α → String) : Option α → String
  | some a => text a
  | none => "none"

/-- The entries that EthLib reads, as the oracle writes them. -/
def entriesText {count : UInt64} (e : ConsensusEntries count) : String :=
  s!"eth2={hexv e.eth2.forkDigest}/{hexv e.eth2.nextForkVersion}/{e.eth2.nextForkEpoch.toNat} " ++
  s!"attnets={optional bitsText e.attnets} syncnets={optional bitsText e.syncnets} " ++
  s!"cgc={optional (fun (n : UInt64) => toString n.toNat) e.cgc} nfd={optional hexv e.nfd}"

/-- The consensus entries of a record read as the specification of the fork says, or are refused.

The record holds each entry, lacks it, or holds it malformed.

The bitfield of attestation subnets has every length, and every bit of it is set in some case. -/
def entries (oracle : Oracle) : Property IO := propertyM do
  let e ← forAll genEntries
  pure do
    let record : Enr := ⟨.empty, 0, e.pairs⟩
    let want ← oracle.ask ["enr_entries", toString e.count, e.fork.name, pairsText e.pairs]
    let got := match readEntries (UInt64.ofNat e.count) e.fork record with
      | .ok entries => entriesText entries
      | .error _ => "error"
    got === verdict want
    let fulu := Fork.fusaka ≤ e.fork
    let altair := Fork.altair ≤ e.fork
    let fine (v : Value) (required : Bool) : Bool := v.valid || (!required && v.item.isNone)
    let asMeant := e.eth2.valid && fine e.attnets false && fine e.syncnets false &&
      fine e.cgc fulu && fine e.nfd fulu
    cover 7 "valid as generated" (asMeant && !refused want)
    -- An entry that the fork does not read may be anything.
    cover 1 "mutated and still accepted by the reference" (!asMeant && !refused want)
    cover 5 "refused by the reference" (refused want)
    cover 5 "before Altair" (!altair)
    cover 13 "from Altair to before Fulu" (altair && !fulu)
    cover 8 "from Fulu on" fulu
    cover 7 "accepted from Fulu on" (fulu && !refused want)
    cover 10 "a bitfield of another length than 64 is read"
      (e.count != 64 && e.attnets.valid && !refused want)
    cover 1 "a bitfield of the wrong size or with a bit past its end"
      (e.attnets.item.isSome && !e.attnets.valid)
    classify "no attnets" e.attnets.item.isNone

/-- The consensus keys that exist at each fork are those of the specifications. -/
def keys (oracle : Oracle) : Property IO := propertyM do
  let fork ← forAllWith Fork.name (Gen.element allForks)
  pure do
    let got := (keysAt fork).map (·.name)
    (if got.isEmpty then "-" else ",".intercalate got) === (← oracle.ask ["enr_keys", fork.name])
    cover 11 "before the beacon chain" (fork < Fork.phase0)
    cover 8 "from Fulu on" (Fork.fusaka ≤ fork)

/-! ## The "eth" entry -/

/-- The value of an "eth" entry, as it should be or with one thing changed. -/
def genEthEntry : Gen Item := do
  let hash ← genBytes (.singleton 4)
  let next ← Gen.frequency [(1, pure 0), (3, genNatBits 64)]
  let id : Item := .list [.bytes hash, natItem next]
  Gen.frequency [
    (5, pure (.list [id])),
    (2, (fun more => .list (id :: more)) <$> Gen.list (.constant 1 2)
      (Gen.element [.bytes .empty, .list [], id, .bytes ⟨#[1, 2]⟩])),
    (1, pure (.list [.list [.bytes hash, natItem next, .bytes ⟨#[1]⟩]])),
    (1, pure (.list [.list [.bytes hash]])),
    (1, (fun n => .list [.list [.bytes ⟨Array.replicate n 9⟩, natItem next]]) <$>
      Gen.element [0, 3, 5]),
    (1, (fun bad => .list [.list [.bytes hash, bad]]) <$> Gen.element [.bytes ⟨#[0]⟩,
      .bytes ⟨#[0, 1]⟩, .bytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩, .list []]),
    (1, Gen.element [.list [], .bytes hash, .list [.bytes hash], id])]

/-- The "eth" entry reads as `enr-entries/eth.md` says: the first element is the fork identifier.

The elements after it are ignored, and a record without the key has no identifier. -/
def ethReads (oracle : Oracle) : Property IO := propertyM do
  let item ← forAll genEthEntry
  let present ← forAll (Gen.frequency [(5, pure true), (1, pure false)])
  pure do
    let want ← oracle.ask ["enr_eth", itemText item]
    let text (id : Devp2p.ForkId) : String := s!"{hexv id.hash} {id.next.toNat}"
    let got := match readEthEntry item with
      | .ok id => text id
      | .error _ => "error"
    got === verdict want
    let pairs : List (ByteArray × Item) := [("eth2".toUTF8, .bytes .empty)] ++
      (if present then [("eth".toUTF8, item)] else []) ++ [("id".toUTF8, .bytes "v4".toUTF8)]
    let inRecord := match readEth ⟨.empty, 0, pairs⟩ with
      | .ok (some id) => text id
      | .ok none => "none"
      | .error _ => "error"
    inRecord === (if present then verdict want else "none")
    cover 7 "valid as generated" (!refused want && item == .list (fieldsFirst item))
    cover 1 "mutated and still accepted by the reference" (!refused want &&
      item != .list (fieldsFirst item))
    cover 5 "refused by the reference" (refused want)
    classify "no entry in the record" (!present)
where
  /-- The first element of a list, as a list of one, for the label of a plain entry. -/
  fieldsFirst : Item → List Item
    | .list (first :: _) => [first]
    | _ => []

/-- EthLib's entry is the RLP of `[[forkHash, forkNext]]`, and it reads back. -/
def ethWrites (oracle : Oracle) : Property IO := propertyM do
  let hash ← forAllWith hexv (genVector 4)
  let next ← forAll (Gen.frequency [(1, pure 0), (3, genUInt64)])
  pure do
    let id : Devp2p.ForkId := ⟨hash, next⟩
    let .ok bytes := Serialization.Rlp.encode (ethEntry id) | failWith "the entry does not encode"
    hex bytes === (← oracle.ask ["enr_eth_make", hexv hash, toString next.toNat])
    ensure (readEthEntry (ethEntry id) == .ok id) "the entry does not read back"
    classify "no next fork" (next == 0)

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  [("enr: the consensus entries at every fork and length", (entries oracle).withTests cases),
   ("enr: the consensus keys of a fork", (keys oracle).withTests cases),
   ("enr: the eth entry reads as eth.md says", (ethReads oracle).withTests cases),
   ("enr: the eth entry is written as eth.md says", (ethWrites oracle).withTests cases)]

end DecodersProperty.Devp2p.Enr
