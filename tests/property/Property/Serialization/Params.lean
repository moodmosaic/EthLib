import Hedgehog
import Support
import Property.Serialization.Common
import Property.Serialization.Classes
import Property.Serialization.Merkle

/-!
# The general functions of RLP and of merkleization, at every value of their parameters

A function that takes a length, a width, a depth, a level or a hash is called here directly.

So each parameter is generated over its whole range.

An encoding of a real value reaches only a part of that range.

The references are in `oracle/serialization_params.py`, written from the texts.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Serialization

namespace SerializationProperty

/-! ## RLP -/

/-- A length at the edges of each count of bytes that writes it, up to nine bytes. -/
def genLength : Gen Nat := do
  let k ← Gen.nat (.constant 0 8)
  Gen.frequency [
    (2, Gen.element [0, 1, 55, 56, 57, 255, 256, 65535, 65536]),
    (2, pure (256 ^ k)),
    (2, pure (256 ^ (k + 1) - 1)),
    (1, pure (256 ^ k + 1)),
    (2, Gen.nat (.constant (256 ^ k) (256 ^ (k + 1) - 1))),
    (1, (2 ^ 64 + ·) <$> Gen.nat (.exponential 0 (2 ^ 80)))]

/-- The forms of the prefix of a length. -/
def prefixForms : List String :=
  ["in the first byte"] ++ (List.range 8).map (fun k => s!"on {k + 1}") ++ ["2^64 or more"]

/-- The form of the prefix of a length. -/
def prefixForm (length : Nat) : String :=
  if length < 56 then "in the first byte"
  else if length < 2 ^ 64 then s!"on {byteLength length}" else "2^64 or more"

/-- The prefix of a payload of any length is the one of the Yellow Paper.

A length of `2 ^ 64` or more has none. -/
def rlpLengthPrefix (oracle : Oracle) : Property IO := propertyM do
  let list ← forAll Gen.bool
  let length ← forAll genLength
  pure do
    classifyOne "length" prefixForms (prefixForm length)
    classify "kind: list" list
    classify "kind: byte string" (!list)
    let kind := if list then Rlp.PayloadKind.list else .bytes
    let expected ← oracle.ask ["rlpprefix", if list then "list" else "bytes", toString length]
    match Rlp.lengthPrefix kind length with
    | .ok bytes => hex bytes === expected
    | .error e =>
      expected === "error"
      ensure (e == .payloadTooLong length) s!"another error: {repr e}"

/-- The digits of a number on exactly a count of bytes, most significant first. -/
def digitsOn (count n : Nat) : List UInt8 :=
  (List.range count).reverse.map fun i => UInt8.ofNat (n / 256 ^ i)

/-- An input built from its first byte: a prefix of every form, then the bytes of a length.

The length is whole, cut short, small behind zero bytes, or any. -/
def genHeaded : Gen ByteArray := do
  let list ← Gen.bool
  let base := if list then 0xc0 else 0x80
  let k ← Gen.frequency [(1, pure 0), (10, Gen.nat (.constant 1 8))]
  let filler : UInt8 ← Gen.element [0, 1, 0x7f]
  let whole (length : Nat) : ByteArray :=
    let count := byteLength length
    ⟨(UInt8.ofNat (base + 55 + count) :: digitsOn count length ++
      List.replicate length filler).toArray⟩
  let tail ← genByteList (.linear 0 70)
  let direct (digits : List UInt8) : ByteArray :=
    ⟨(UInt8.ofNat (if k == 0 then base + digits.length else base + 55 + k) ::
      (if k == 0 then [] else digits) ++ tail).toArray⟩
  Gen.frequency [
    -- An item whose payload is all there, with the length on one, two or three bytes.
    (3, whole <$> Gen.frequency [(3, Gen.element [56, 57, 255, 256, 257]),
      (2, Gen.nat (.constant 56 600)), (2, Gen.element [65535, 65536, 65537])]),
    (4, direct <$> genByteList (.singleton k)),
    (3, do
      let top : UInt8 ← Gen.integral (.constant 1 255)
      let rest ← Gen.list (.singleton (k - 1)) (Gen.element [0, 1, 0xff])
      pure (direct (top :: rest))),
    (2, do
      let small ← Gen.frequency [(1, Gen.nat (.constant 0 55)), (1, Gen.nat (.constant 56 300))]
      pure (direct (digitsOn k small))),
    -- A length below 56 on one byte: the long form for a short length.
    (1, (fun short => ⟨(UInt8.ofNat (base + 56) :: UInt8.ofNat short :: tail).toArray⟩) <$>
      Gen.nat (.constant 0 55)),
    (2, do
      let digits ← genByteList (.constant 0 (k - 1))
      pure ⟨(UInt8.ofNat (base + 55 + k) :: digits).toArray⟩)]

/-- The prefix of a list payload of a length, written here apart from the encoder. -/
def listPrefix (length : Nat) : ByteArray :=
  if length < 56 then ⟨#[UInt8.ofNat (0xc0 + length)]⟩
  else ⟨(UInt8.ofNat (0xf7 + byteLength length) :: digitsOn (byteLength length) length).toArray⟩

/-- An input that the encoder never writes: one of the longer forms, at the root or in a list.

- A byte below `0x80` behind a prefix.
- A length below 56 in the long form.
- A length behind a zero byte.
- An item that runs past the end of the list that holds it.
- The valid encoding cut, or with a byte after it. -/
def genRlpNear (valid : ByteArray) : Gen ByteArray := do
  let low : UInt8 ← Gen.integral (.constant 0 0x7f)
  let short ← Gen.nat (.constant 0 55)
  let length ← Gen.element [56, 57, 255, 256, 300]
  let list ← Gen.bool
  let base := if list then 0xc0 else 0x80
  let payload (count : Nat) : List UInt8 := List.replicate count 1
  let count := byteLength length
  let fault : ByteArray ← Gen.element [
    ⟨#[0x81, low]⟩,
    ⟨(UInt8.ofNat (base + 56) :: UInt8.ofNat short :: payload short).toArray⟩,
    ⟨(UInt8.ofNat (base + 56 + count) :: 0 :: digitsOn count length ++ payload length).toArray⟩,
    ⟨(UInt8.ofNat (base + 57) :: 0 :: UInt8.ofNat short :: payload short).toArray⟩,
    -- A string of `short + 2` bytes in a list whose payload ends one byte before it does.
    ⟨(UInt8.ofNat (0xc0 + short + 2) :: UInt8.ofNat (0x80 + short + 2) :: payload (short + 2)
      ).toArray⟩]
  let inList := listPrefix (fault.size + 1) ++ ⟨#[low]⟩ ++ fault
  let deeper := listPrefix inList.size ++ inList
  Gen.frequency [(4, pure fault), (3, pure inList), (1, pure deeper),
    (1, pure (valid.extract 0 (valid.size - 1))), (1, pure (valid.push low))]

/-- The name of a kind of payload, as the oracle writes it. -/
def kindName : Rlp.PayloadKind → String
  | .bytes => "bytes"
  | .list => "list"

/-- The first bytes of an encoding announce the kind and the length of the Yellow Paper.

This holds for a length on every count of bytes, from one to eight.

The decoder then asks for exactly the bytes announced. -/
def rlpReadPrefix (oracle : Oracle) : Property IO := propertyM do
  let input ← forAllWith hex genHeaded
  pure do
    let first := input.data[0]!
    let got := Rlp.readPrefix input first 1 input.size (Nat.le_refl _)
    classifyOne "input" (inputForms.drop 2) (inputForm input)
    classifyOne "verdict" ["read", "input too short", "long form for a short length",
        "leading zero in a length"]
      (match got with
        | .ok _ => "read"
        | .error e => rlpVerdict (.error e : Except Rlp.RlpError Unit))
    let expected ← oracle.ask ["rlphead", hex input]
    annotate s!"the model: {expected}"
    match got with
    | .ok (kind, k, length) => s!"{kindName kind} {k} {length}" === expected
    | .error (.inputTooShort needed available) => s!"error short {needed} {available}" === expected
    | .error .leadingZeroInLength =>
      ensure ((expected.splitOn " ").contains "zero") "no leading zero in the model"
    | .error (.longFormForShortLength _) =>
      ensure ((expected.splitOn " ").contains "shortform") "no short length in the model"
    | .error e => failWith s!"another error: {repr e}"
    -- The whole decoder accepts and refuses these inputs as the strict references do.
    let cited ← oracle.ask ["rlpdec", hex input]
    match Rlp.decode input with
    | .ok item => itemText item === cited
    | .error _ => cited === "error"
    match got, Rlp.decodeItem input 0 input.size (Nat.le_refl _) with
    | .ok (_, k, length), .ok (_, next) =>
      label "the item is all there"
      -- No input holds the `2 ^ 24` bytes of a payload whose length is on four bytes or more.
      classifyAny "all there, the length" (prefixForms.take 4) [prefixForm length]
      next.val === 1 + k + length
    | .ok (_, k, length), .error (.inputTooShort needed available) =>
      if 1 + k + length > input.size then
        label "the payload is cut short"
        (needed, available) === (length, input.size - 1 - k)
    | _, _ => pure ()

/-- An item is read between two positions of an input, and the reader stops after it. -/
def rlpDecodeAt (oracle : Oracle) : Property IO := propertyM do
  let front ← forAllWith hex (genBytes (.linear 0 5))
  let item ← forAllWith itemText genItem
  let back ← forAllWith hex (genBytes (.linear 0 5))
  let valid := (Rlp.encode item).toOption.getD .empty
  let middle ← forAllWith hex (Gen.frequency [(3, pure valid), (1, genMutation valid),
    (2, genRlpNear valid)])
  let input := front ++ middle ++ back
  let pos ← forAll (Gen.frequency [(4, pure front.size), (1, Gen.nat (.constant 0 input.size))])
  let stop ← forAll (Gen.frequency [(3, pure (front.size + middle.size)), (1, pure input.size),
    (1, Gen.nat (.constant 0 input.size))])
  pure do
    let expected ← oracle.ask ["rlpitem", hex input, toString pos, toString stop]
    if bounded : stop ≤ input.size then
      let got := Rlp.decodeItem input pos stop bounded
      -- The reader of one item leaves the bytes after it, so it has no refusal for them.
      classifyOne "verdict" rlpVerdicts.dropLast (rlpVerdict got)
      classify "from a position past the start" (pos > 0)
      classify "to a position before the end" (stop < input.size)
      classify "the item ends before the stop"
        (match got with
          | .ok (_, next) => next.val < stop
          | .error _ => false)
      match got with
      | .ok (read, next) => s!"{itemText read} {next.val}" === expected
      | .error _ => expected === "error"

/-- A number in base 256 has the bytes of the reference, and reads back from any position. -/
def rlpBigEndian (oracle : Oracle) : Property IO := propertyM do
  let bits ← forAll (Gen.frequency [(1, Gen.element [0, 1, 7, 8, 9, 63, 64, 65, 255, 256, 257]),
    (1, Gen.nat (.linear 0 600))])
  let n ← forAll (genNatBits bits)
  let acc ← forAll (Gen.nat (.linear 0 1000))
  pure do
    let bytes := Rlp.bigEndian n
    classifyOne "bytes" ["0", "1", "2 to 8", "9 to 32", "33 or more"]
      (if bytes.size ≤ 1 then toString bytes.size else if bytes.size ≤ 8 then "2 to 8"
        else if bytes.size ≤ 32 then "9 to 32" else "33 or more")
    hex bytes === (← oracle.ask ["be", toString n])
    Rlp.ofBigEndian bytes.toList === n
    let input := (ByteArray.mk #[0xaa]) ++ bytes ++ (ByteArray.mk #[0xbb])
    if inside : 1 + bytes.size ≤ input.size then
      Rlp.readBigEndian input 1 bytes.size acc inside === acc * 256 ^ bytes.size + n

/-- A scalar reads as a value of a width exactly when it is below `2 ^ bits`, at every width. -/
def rlpScalarBelow : Property Id := property do
  let bits ← forAll (Gen.frequency [(2, Gen.element [0, 1, 8, 16, 32, 64, 256]),
    (1, Gen.nat (.linear 0 300))])
  let near ← forAll (Gen.int (.linearFrom 0 (-3) 3))
  let n ← forAll (Gen.frequency [(3, pure ((2 : Int) ^ bits + near).toNat),
    (1, genNatBits (bits + 8))])
  let item := Rlp.Item.scalar n
  classify "below 2 ^ bits" (n < 2 ^ bits)
  classify "exactly 2 ^ bits - 1" (n + 1 == 2 ^ bits)
  classify "exactly 2 ^ bits" (n == 2 ^ bits)
  classifyOne "bits" ["0", "1", "8", "16", "32", "64", "256", "another width"]
    (if [0, 1, 8, 16, 32, 64, 256].contains bits then toString bits else "another width")
  (item.toScalarBelow bits).toOption === (if n < 2 ^ bits then some n else none)
  let within (width : Nat) : Option Nat := if n < 2 ^ width then some n else none
  (Rlp.Codec.ofItem (α := U256) item).toOption.map (·.toNat) === within 256
  (Rlp.Codec.ofItem (α := UInt64) item).toOption.map (·.toNat) === within 64
  (Rlp.Codec.ofItem (α := UInt32) item).toOption.map (·.toNat) === within 32
  (Rlp.Codec.ofItem (α := UInt16) item).toOption.map (·.toNat) === within 16
  (Rlp.Codec.ofItem (α := UInt8) item).toOption.map (·.toNat) === within 8
  (Rlp.Codec.ofItem (α := Bool) item).toOption.map (·.toNat) === within 1
  (Rlp.Codec.ofItem (α := Nat) item).toOption === some n

/-- Every fork, in order. -/
def allForks : List Fork :=
  [.frontier, .homestead, .daoFork, .tangerineWhistle, .spuriousDragon, .byzantium,
    .constantinople, .petersburg, .istanbul, .muirGlacier, .phase0, .berlin, .london, .altair,
    .arrowGlacier, .grayGlacier, .bellatrix, .paris, .shapella, .dencun, .pectra, .fusaka, .bpo1,
    .bpo2, .bpo3, .bpo4, .bpo5, .glamsterdam, .hegota]

/-- A fork, and its place in the order. -/
def genFork : Gen (Fork × Nat) := Gen.element allForks.zipIdx

/-- The typed readers of an item: a byte string of every length, fields, a field of a fork. -/
def rlpCodecShapes : Property Id := property do
  let n ← forAll (Gen.frequency [(1, Gen.element [0, 1, 20, 32]), (1, Gen.nat (.linear 0 64))])
  let size ← forAll (Gen.frequency [(3, pure n), (1, pure (n + 1)), (1, pure (n - 1)),
    (1, Gen.nat (.linear 0 70)), (1, pure 0)])
  let bytes ← forAllWith hex (genBytesN size)
  let asList ← forAll (Gen.frequency [(5, pure false), (1, pure true)])
  let item := if asList then Rlp.Item.list [.bytes bytes] else .bytes bytes
  classify "a byte string of the length of the type" (!asList && size == n)
  classify "a byte string of another length" (!asList && size != n)
  classify "a list" asList
  classify "the type has no byte" (n == 0)
  classify "no byte, for a type that has some" (!asList && size == 0 && n != 0)
  (Rlp.Codec.ofItem (α := Vector UInt8 n) item).toOption.map (fun v => hex ⟨v.toArray⟩) ===
    (if !asList && size == n then some (hex bytes) else none)
  (Rlp.Codec.ofItem (α := ByteArray) item).toOption.map hex ===
    (if asList then none else some (hex bytes))
  ensure (Rlp.Codec.ofItem (α := Rlp.Item) item == .ok item) "an item is not itself"
  -- An optional byte string: the empty one is none, and the type must have a byte.
  match n with
  | 0 => pure ()
  | more + 1 =>
    (Rlp.Codec.ofItem (α := Option (Vector UInt8 (more + 1))) item).toOption.map
        (·.map fun v => hex ⟨v.toArray⟩) ===
      (if asList then none else if size == more + 1 then some (some (hex bytes))
        else if size == 0 then some none else none)
  -- The fields of a structure: a list of exactly the count.
  let count ← forAll (Gen.nat (.linear 0 6))
  let items ← forAll (Gen.list (.linear 0 6) (Gen.nat (.linear 0 300)))
  let fields := Rlp.Item.list (items.map Rlp.Item.scalar)
  classify "fields: as many as the structure has" (items.length == count)
  ensure ((Rlp.Item.fields count fields).toOption.isSome == (items.length == count))
    "the count of fields"
  ensure ((Rlp.Item.fields count (.bytes bytes)).toOption.isNone) "a byte string has no fields"
  (Rlp.Codec.ofItem (α := List UInt8) fields).toOption.map (·.map (·.toNat)) ===
    (if items.all (· < 256) then some items else none)
  -- A field that holds no value is refused with its index.
  match Rlp.Item.readField (α := UInt8) count (items.map Rlp.Item.scalar) with
  | .ok (value, rest) =>
    (value.toNat, rest.length + 1) === (items.headD 0, items.length)
  | .error (.inField index _) =>
    ensure (items.headD 0 ≥ 256) "a byte was refused"
    index === count - items.length
  | .error e => ensure items.isEmpty s!"another error: {repr e}"
  -- A field that a fork adds: one item from the fork on, none before.
  let (first, firstAt) ← forAllWith (fun f => toString f.2) genFork
  let (fork, forkAt) ← forAllWith (fun f => toString f.2)
    (Gen.frequency [(4, genFork), (1, pure (first, firstAt))])
  let present := firstAt ≤ forkAt
  classify "a field of a fork: present" present
  classify "a field of a fork: absent" (!present)
  classify "a field of a fork: at its first fork" (firstAt == forkAt)
  Rlp.Item.sinceCount first fork === (if present then 1 else 0)
  match Rlp.Item.readSince (f := first) (fork := fork) (α := UInt16) count
      (items.map Rlp.Item.scalar) with
  | .ok (value, rest) =>
    rest.length === items.length - (if present then 1 else 0)
    (Rlp.Item.ofSince value).length === (if present then 1 else 0)
    if present then
      ensure (Rlp.Item.ofSince value == [Rlp.Item.scalar (items.headD 0)]) "the field differs"
  | .error _ =>
    ensure (present && (items.isEmpty || items.headD 0 ≥ 65536)) "a field was refused"

/-! ## Merkleization, with the hash as a parameter -/

/-- A hash that is not a hash: cheap, and unlike SHA-256.

`oracle/serialization_params.py` has the same one, as `toy`. -/
def toyHash (data : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.mk (Array.replicate 32 0)
  for i in [0:data.size] do
    let byte := data.data[i]!
    let spot := (7 * i + byte.toNat) % 32
    out := out.set! spot (out.data[spot]! ^^^ UInt8.ofNat ((byte.toNat + i) % 256))
  return out

/-- A hash by the name the oracle gives it. -/
def namedHash (name : String) (data : ByteArray) : ByteArray :=
  if name == "twice" then
    Cryptography.Hash.Sha256.hash (Cryptography.Hash.Sha256.hash data)
  else if name == "toy" then toyHash data
  else Cryptography.Hash.Sha256.hash data

/-- The hashers under test: the one of SHA-256 with its table of zero roots, and three more.

The others fold their zero roots, as `Hasher.ofHash` does. -/
def hasherNames : List String := ["the table of SHA-256", "sha256", "twice", "toy"]

/-- A hasher by its name. -/
def namedHasher (name : String) : Ssz.Hasher Id :=
  if name == "the table of SHA-256" then Ssz.sha256Hasher
  else Ssz.Hasher.ofHash (m := Id) (namedHash name)

/-- The name of the hash of a hasher, for the oracle. -/
def hashName (name : String) : String :=
  if name == "the table of SHA-256" then "sha256" else name

/-- The depth of the zero subtrees beside a count of chunks under a capacity. -/
def zeroClass (count capacity : Nat) : String :=
  let zeros := Ssz.depthFor capacity - Ssz.depthFor (max count 1)
  if capacity < count then "none: the capacity is under the count"
  else if zeros == 0 then "none" else if zeros < 8 then "1 to 7"
  else if zeros < 32 then "8 to 31" else if zeros < 64 then "32 to 63"
  else if zeros == 64 then "64" else "65 or more"

/-- The classes of the depth of a zero subtree. -/
def zeroClasses : List String :=
  ["none: the capacity is under the count", "none", "1 to 7", "8 to 31", "32 to 63", "64",
    "65 or more"]

/-- The root of chunks under a capacity is the one of `merkleize`, for every hasher.

The capacity is none, the count, a power of two up to `2 ^ 80`, one over it, or any. -/
def merkleizeLimits (oracle : Oracle) : Property IO := propertyM do
  let count ← forAll (Gen.frequency [(2, Gen.element [0, 1, 2, 3, 4, 5, 8, 9, 16, 17]),
    (1, Gen.nat (.linear 0 40))])
  let chunks ← forAllWith nodesText (genNodes count)
  let limit ← forAll (Gen.frequency [(1, pure none), (2, pure (some count)),
    (1, pure (some (count + 1))), (1, pure (some (count - 1))),
    (2, (fun k => some (2 ^ k)) <$> Gen.nat (.constant 0 80)),
    (2, (fun k => some (2 ^ k)) <$> Gen.element [63, 64, 65, 66, 70, 80]),
    (1, (fun k => some (2 ^ k + 1)) <$> Gen.nat (.constant 0 80)),
    (1, (fun k => some (2 ^ k + 1)) <$> Gen.element [63, 64, 65, 66, 70, 80]),
    (1, some <$> Gen.nat (.linear 0 100))])
  let name ← forAll (Gen.element hasherNames)
  pure do
    let capacity := limit.getD count
    classifyOne "hasher" hasherNames name
    classifyOne "zero subtree" zeroClasses (zeroClass count capacity)
    classifyOne "capacity" ["none given", "under the count", "the count", "a power of two",
        "one over a power of two", "another"]
      (if limit.isNone then "none given" else if capacity < count then "under the count"
        else if capacity == count then "the count" else if isPow2 capacity then "a power of two"
        else if isPow2 (capacity - 1) then "one over a power of two" else "another")
    classify "chunks: none" (count == 0)
    let expected ← oracle.ask ["merkle", hashName name,
      (limit.map toString).getD "-", nodesText chunks]
    match (Ssz.merkleizeBoundedUncheckedM (namedHasher name) chunks.toArray limit).run with
    | .ok root => hex ⟨root⟩ === expected
    | .error e =>
      expected === "error"
      e.reason === "MERKLEIZE_LIMIT"

/-- A count of chunks at the ends of the runs of a spine that starts at a level. -/
def genRunCount (level : Nat) : Gen Nat := do
  let ends := (List.range 4).map fun runs =>
    (List.range runs).foldl (fun total i => total + 4 ^ (level + i)) 0
  let reachable := ends.filter (· ≤ 400)
  let near ← Gen.element [0, 0, 1]
  Gen.frequency [(3, (· + near) <$> Gen.element reachable),
    (1, (· - 1) <$> Gen.element reachable), (2, Gen.nat (.linear 0 90))]

/-- The root of a progressive spine is the one of EIP-7916, from every level, for every hasher.

A spine that starts at a level opens with a tree of `4 ^ level` chunks. -/
def merkleizeProgressiveLevels (oracle : Oracle) : Property IO := propertyM do
  let level ← forAll (Gen.nat (.constant 0 4))
  let count ← forAll (genRunCount level)
  let chunks ← forAllWith nodesText (genNodes count)
  let name ← forAll (Gen.element hasherNames)
  pure do
    classifyOne "level" ((countClasses 5).take 5) (toString level)
    classifyOne "hasher" hasherNames name
    let runs := (List.range 6).find? (fun r =>
      count ≤ (List.range r).foldl (fun total i => total + 4 ^ (level + i)) 0) |>.getD 6
    classifyOne "runs" (countClasses 4) (countClass 4 runs)
    classify "the last run is full" (count > 0 &&
      count == (List.range runs).foldl (fun total i => total + 4 ^ (level + i)) 0)
    let expected ← oracle.ask ["progressive", hashName name, toString level, nodesText chunks]
    let root := (Ssz.merkleizeProgressiveUncheckedM (namedHasher name) chunks level).run
    hex ⟨root⟩ === expected
    -- The same spine named by the width of its first tree, under SHA-256.
    if name == "sha256" then
      hex ⟨Ssz.merkleizeProgressiveFrom chunks.toArray (4 ^ level)⟩ === expected

/-- The root of a zero subtree of every depth, from the table and folded, and the mixed words. -/
def zeroSubtrees (oracle : Oracle) : Property IO := propertyM do
  let depth ← forAll (Gen.frequency [(2, Gen.element [0, 1, 62, 63, 64, 65, 66]),
    (3, Gen.nat (.constant 0 100))])
  let count ← forAll (Gen.frequency [(1, genNatBits 64), (1, genNatBits 256),
    (1, Gen.nat (.linear 0 300))])
  let active ← forAll (Gen.list (.linear 0 256) Gen.bool)
  pure do
    classifyOne "depth" ["0 to 63", "64", "65 or more"]
      (if depth < 64 then "0 to 63" else if depth == 64 then "64" else "65 or more")
    let expected ← oracle.ask ["zeroroot", "sha256", toString depth]
    hex ⟨Ssz.zeroSubtree depth⟩ === expected
    hex ⟨Ssz.zeroRoot Ssz.combine Ssz.zeroChunk depth⟩ === expected
    hex ⟨(Ssz.sha256Hasher.zeroSubtree depth).run⟩ === expected
    hex ⟨((Ssz.Hasher.ofHash (m := Id) (namedHash "sha256")).zeroSubtree depth).run⟩ === expected
    Ssz.zeroRoots.size === Ssz.maxZeroDepth + 1
    -- The word of a count: 32 bytes, least significant first.
    let word := Ssz.lengthWord count
    word.size === 32
    (List.range 32).foldl (fun total i => total + (word.getD i 0).toNat * 256 ^ i) 0 === count
    -- The word of a layout: bit `i` of byte `i / 8` is position `i`.
    let layout := Ssz.activeFieldsWord active
    layout.size === 32
    (List.range 256).map (fun i => (layout.getD (i / 8) 0).toNat >>> (i % 8) % 2 == 1) ===
      (List.range 256).map (fun i => active.getD i false)
    -- The depth of a tree is the least that holds the count.
    let size ← pure (count % 2 ^ 70)
    ensure (size ≤ 2 ^ Ssz.depthFor size) "the tree is too small"
    ensure (size ≤ 1 || 2 ^ (Ssz.depthFor size - 1) < size) "the tree is too deep"
    Ssz.nextPow2 size === 2 ^ Ssz.depthFor size

end SerializationProperty
