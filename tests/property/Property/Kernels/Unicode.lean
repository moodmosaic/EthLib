import Property.Kernels.Common
import EthLib.Base.Unicode

/-!
# NFKD over every code point

`Base/Unicode.lean` decomposes by tables of Unicode 16.0.0 and orders by combining class.

One test asks the decomposition and the class of all 1,114,112 code points, not a sample.

The reference is the host's `unicodedata`, or the `UnicodeData.txt` that `ETHLIB_UCD` names.

The host of Python 3.13 has Unicode 15.1.0, so it does not know what 16.0.0 added.

A code point that it does not assign is counted, and compared only against the file.
-/

open Hedgehog Support EthLib EthLib.Base

namespace KernelsProperty.Uni

/-- A number in hexadecimal. -/
def hexOf (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The entry of a code point, or none when it has class 0 and decomposes to itself. -/
def entry (code : Nat) : Option String :=
  let c := Char.ofNat code
  let parts := (Unicode.decompose c).map (·.toNat)
  let rank := Unicode.combiningClass c
  if rank == 0 && parts == [code] then none
  else some s!"{hexOf code}:{hexOf rank}:{".".intercalate (parts.map hexOf)}"

/-- The decomposition and the combining class of every code point are the reference's.

The answer of each range is `ok`, the count compared, and the count the reference does not know.

The labels of the report give both counts. -/
def everyCodePoint (oracle : Oracle) : Property IO := propertyM do
  pure do
    let chunk := 4096
    let mut compared := 0
    let mut unknown := 0
    let mut version := ""
    for i in List.range (0x110000 / chunk) do
      let start := i * chunk
      let entries := (List.range chunk).filterMap fun d =>
        let code := start + d
        if 0xD800 ≤ code && code < 0xE000 then none else entry code
      let answer ← oracle.ask (["uni", toString start, toString chunk] ++ entries)
      match words answer with
      | "ok" :: n :: k :: rest =>
        compared := compared + n.toNat!
        unknown := unknown + k.toNat!
        version := " ".intercalate rest
      | _ => failWith s!"from {hexOf start}: {answer}"
    label s!"{compared} code points compared with {version}"
    -- Every code point but the 2,048 surrogates is compared, or is unknown to the reference.
    ensure (compared + unknown ≤ 0x110000 - 2048) "more code points than exist"
    ensure (compared ≥ 149000) s!"only {compared} code points compared with {version}"
    -- An older reference lacks what Unicode 16.0.0 added: counted here, compared with the file.
    if unknown > 0 then label s!"{unknown} entries are of code points unknown to {version}"

/-- A non-starter of the tables, by its index. -/
def genMark : Gen Char :=
  (fun i => Char.ofNat (Unicode.Data.combiningClasses[i]!).1) <$>
    Gen.nat (.constant 0 (Unicode.Data.combiningClasses.size - 1))

/-- A code point with a decomposition in the tables, by its index. -/
def genDecomposing : Gen Char :=
  (fun i => Char.ofNat (Unicode.Data.decompositions[i]!).1) <$>
    Gen.nat (.constant 0 (Unicode.Data.decompositions.size - 1))

/-- NFKD of a string of marks and starters: decomposed, and each run of marks in order.

Marks of one class keep their order, and no mark crosses a starter. -/
def ordering (oracle : Oracle) : Property IO := propertyM do
  let chars ← forAllWith (fun cs => " ".intercalate (cs.map fun c => hexOf c.toNat))
    (Gen.list (.linear 0 12) (Gen.frequency [
      (6, genMark), (2, Gen.char (.constant 'a' 'e')), (2, genDecomposing),
      (1, Gen.char (.constant (Char.ofNat 0xAC00) (Char.ofNat 0xD7A3)))]))
  pure do
    let ranks := chars.map Unicode.combiningClass
    let pairs := ranks.zip (ranks.drop 1)
    classify "two marks are out of order" (pairs.any fun (x, y) => y != 0 && y < x)
    classify "two marks have one class" (pairs.any fun (x, y) => x != 0 && x == y)
    classify "a starter sits between marks" ((ranks.zip (ranks.drop 2)).zip (ranks.drop 1)
      |>.any fun ((x, z), y) => x != 0 && y == 0 && z != 0)
    let expected ← oracle.ask ("uniorder" :: chars.map fun c => hexOf c.toNat)
    classify "the reference does not know a code point" (expected == "skip")
    if expected != "skip" then
      let got := (Unicode.nfkd (String.ofList chars)).toList.map fun c => hexOf c.toNat
      (if got.isEmpty then "-" else " ".intercalate got) === expected

end KernelsProperty.Uni
