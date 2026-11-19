import Property.Engine.Common
import EthLib.Serialization.JsonRpc

/-!
# The base types of the Engine API, as JSON

`DATA` and `QUANTITY` against the patterns of `base-types.yaml`, which EthLib cites.

Also against the two patterns of the section Encoding of `common.md`, the Engine API's own text.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Serialization.JsonRpc

namespace EngineProperty

/-- A base type of the schema, by its name there. -/
inductive Kind where
  | address | bytes | bytesMax32 | bytes4 | bytes8 | bytes16 | bytes32 | bytes48 | bytes256
  | uint | uint64 | uint256
  deriving Repr, BEq

/-- The name of a type in `base-types.yaml`. -/
def Kind.name : Kind → String
  | .address => "address" | .bytes => "bytes" | .bytesMax32 => "bytesMax32" | .bytes4 => "bytes4"
  | .bytes8 => "bytes8" | .bytes16 => "bytes16" | .bytes32 => "bytes32" | .bytes48 => "bytes48"
  | .bytes256 => "bytes256" | .uint => "uint" | .uint64 => "uint64" | .uint256 => "uint256"

/-- Text that is almost a value of a type. -/
def Kind.genText : Kind → Gen String
  | .address => genHexText 20 | .bytes => Gen.nat (.linear 0 40) >>= genHexText
  | .bytesMax32 => Gen.element [0, 1, 31, 32, 33, 34] >>= genHexText
  | .bytes4 => genHexText 4 | .bytes8 => genHexText 8 | .bytes16 => genHexText 16
  | .bytes32 => genHexText 32 | .bytes48 => genHexText 48 | .bytes256 => genHexText 256
  | .uint => genQuantityText 300 | .uint64 => genQuantityText 64 | .uint256 => genQuantityText 256

/-- What EthLib reads of a type: its verdict, and the value as the oracle writes it. -/
def Kind.read (kind : Kind) (j : Lean.Json) : String × String :=
  let data {n : Nat} (r : Read (Vector UInt8 n)) : String × String :=
    match r with
    | .ok v => ("ok", hex ⟨v.toArray⟩)
    | .error _ => ("error", "-")
  let raw (r : Read ByteArray) : String × String :=
    match r with
    | .ok b => ("ok", hex b)
    | .error _ => ("error", "-")
  let number (r : Read Nat) : String × String :=
    match r with
    | .ok n => ("ok", toString n)
    | .error _ => ("error", "-")
  match kind with
  | .address => data (Serialization.JsonRpc.address "x" j)
  | .bytes => raw (Serialization.JsonRpc.bytes "x" j)
  | .bytesMax32 => raw (Serialization.JsonRpc.bytesMax "x" 32 j)
  | .bytes4 => data (Serialization.JsonRpc.fixed "x" 4 j)
  | .bytes8 => data (Serialization.JsonRpc.fixed "x" 8 j)
  | .bytes16 => data (Serialization.JsonRpc.fixed "x" 16 j)
  | .bytes32 => data (Serialization.JsonRpc.fixed "x" 32 j)
  | .bytes48 => data (Serialization.JsonRpc.fixed "x" 48 j)
  | .bytes256 => data (Serialization.JsonRpc.fixed "x" 256 j)
  | .uint => number (Serialization.JsonRpc.uint "x" j)
  | .uint64 => number (UInt64.toNat <$> Serialization.JsonRpc.uint64 "x" j)
  | .uint256 => number (Serialization.JsonRpc.quantity "x" 256 j)

/-- A type and a JSON value that is almost one of it: a string mostly, or another JSON value. -/
def genWire : Gen (Kind × Lean.Json) := do
  let kind ← Gen.element [Kind.uint64, .uint256, .uint, .bytes32, .address, .bytes, .bytesMax32,
    .bytes4, .bytes8, .bytes16, .bytes48, .bytes256]
  let value ← Gen.frequency [(30, Lean.Json.str <$> kind.genText), (1, pure .null),
    (1, pure (.num 1)), (1, pure (.arr #[])), (1, pure (.bool true))]
  pure (kind, value)

/-- A reader of a base type accepts exactly what the pattern of `base-types.yaml` matches.

The value read is the one the text names. -/
def wireSchema (oracle : Oracle) : Property IO := propertyM do
  let (kind, value) ← forAllWith (fun (k, j) => s!"{k.name} {j.compress}") genWire
  pure do
    let words := (← oracle.ask ["wire", kind.name, jsonHex value]).splitOn " "
    let (got, shown) := kind.read value
    got === words[0]!
    if got == "ok" then shown === words[2]!

/-- A reader of a base type accepts exactly what the section Encoding of `common.md` allows.

That section lets a digit of `DATA` and of `QUANTITY` be upper case. -/
def wireEncoding (oracle : Oracle) : Property IO := propertyM do
  let (kind, value) ← forAllWith (fun (k, j) => s!"{k.name} {j.compress}") genWire
  pure do
    let words := (← oracle.ask ["wire", kind.name, jsonHex value]).splitOn " "
    (kind.read value).1 === words[1]!

/-- A quantity that the writer writes is one that both patterns match, and it reads back. -/
def quantityWrites (oracle : Oracle) : Property IO := propertyM do
  let n ← forAll (genNatBits 256)
  pure do
    let j := quantityJson n
    (← oracle.ask ["wire", "uint256", jsonHex j]) === s!"ok ok {n}"
    (Serialization.JsonRpc.quantity "x" 256 j).toOption === some n

/-- Data that the writer writes is data that both patterns match, and it reads back. -/
def dataWrites (oracle : Oracle) : Property IO := propertyM do
  let payload ← forAll (genBytes (.linear 0 70))
  pure do
    let j := dataJson payload.toList
    (← oracle.ask ["wire", "bytes", jsonHex j]) === s!"ok ok {hex payload}"
    ((Serialization.JsonRpc.bytes "x" j).toOption.map hex) === some (hex payload)

end EngineProperty
