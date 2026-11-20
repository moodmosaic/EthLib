import Hedgehog
import Support
import EthLib.Base.Bytes

/-!
# What the modules of the decoders driver share
-/

open Hedgehog Support EthLib

namespace DecodersProperty

/-- The words of an answer of the oracle, which separates them with spaces. -/
def words (s : String) : List String := s.splitOn " "

/-- Whether the reference refused the input. -/
def refused (s : String) : Bool := s.startsWith "error"

/-- An answer of the oracle with the reason of an error dropped. -/
def verdict (s : String) : String :=
  if refused s then "error" else s

/-- A byte array of a list. -/
def packed (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

/-- The bytes of a vector in hexadecimal. -/
def hexv {n : Nat} (v : Vector UInt8 n) : String := hex ⟨v.toArray⟩

/-- A vector of `n` bytes. -/
def genVector (n : Nat) : Gen (Vector UInt8 n) :=
  (fun (l : List UInt8) => Vector.ofFn fun i => l.getD i.val 0) <$> genByteList (.singleton n)

/-- One byte of the input changed, one dropped, one added, or the input cut. -/
def genMutation (bytes : List UInt8) : Gen (List UInt8) := do
  let at_ ← Gen.nat (.constant 0 (bytes.length - 1))
  let byte ← genByte
  Gen.element [
    bytes.set at_ byte,
    bytes.set at_ ((bytes.getD at_ 0) ^^^ (1 <<< (byte % 8))),
    bytes.eraseIdx at_,
    bytes.take at_ ++ [byte] ++ bytes.drop at_,
    bytes.take at_]

/-- The three kinds of input of a decode property, by what the reference says of it.

The name of the kind is the label of the case. -/
def kind (mutated : Bool) (reference : String) : String :=
  if refused reference then "refused by the reference"
  else if mutated then "mutated and still accepted by the reference"
  else "valid as generated"

/-- A minimum share that only a long run is asked for; a short run counts the cases.

A kind of a few percent may be absent from a run of a hundred cases, whatever the generator. -/
def coverLong (long : Bool) (minimum : Nat) (name : String) (holds : Bool) : TestT IO Unit :=
  if long then cover minimum name holds else classify name holds

end DecodersProperty
