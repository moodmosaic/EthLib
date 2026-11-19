import Property.Evm.Program

/-!
# The functions under the instructions

The arithmetic of the instructions against `Nat` and `Int`, written from Appendix H of the Yellow
Paper and from EIP-145 and EIP-7939, and the jump destinations, the addresses of new contracts
and the growth of memory against the reference.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution.Evm

namespace EvmProperty

/-- A word as a signed number in two's complement. -/
def signedOf (n : Nat) : Int := if n < 2 ^ 255 then n else (n : Int) - 2 ^ 256

/-- A signed number as a word. -/
def wordOf (v : Int) : Nat := (v % 2 ^ 256).toNat

/-- Division that truncates toward zero, as SDIV does. -/
def truncDiv (a b : Int) : Int :=
  (if (a < 0) != (b < 0) then -1 else 1) * (a.natAbs / b.natAbs : Nat)

/-- A word for arithmetic: the edges, powers of two and their neighbours, or any word. -/
def genArith : Gen Nat :=
  Gen.frequency [(3, genWord),
    (2, (fun (k, d) => 2 ^ k + d - 1) <$>
      Gen.zip (Gen.nat (.constant 0 255)) (Gen.nat (.constant 0 2))),
    (1, (2 ^ 256 - 1 - ·) <$> Gen.nat (.linear 0 300))]

/-- Each arithmetic and bitwise instruction computes what the Yellow Paper defines on integers.

DIV, SDIV, MOD and SMOD by zero give zero, SDIV of `-2^255` by `-1` gives `-2^255`, ADDMOD and
MULMOD do not wrap at `2^256`, and a shift of 256 or more gives zero, or all ones for SAR of a
negative word. -/
def arithmetic : Property IO := pureIO do
  let (x, y, z) ← forAll (Gen.zip genArith (Gen.zip genArith genArith))
  let small ← forAll (Gen.frequency [(4, Gen.nat (.constant 0 40)),
    (2, Gen.element [255, 256, 257]),
    (1, genArith)])
  let (a, b, c, s) : U256 × U256 × U256 × U256 :=
    (BitVec.ofNat 256 x, BitVec.ofNat 256 y, BitVec.ofNat 256 z, BitVec.ofNat 256 small)
  let m := 2 ^ 256
  let (sx, sy) := (signedOf x, signedOf y)
  (add a b).toNat === (x + y) % m
  (sub a b).toNat === (x + m - y) % m
  (mul a b).toNat === x * y % m
  (div a b).toNat === (if y = 0 then 0 else x / y)
  (mod a b).toNat === (if y = 0 then 0 else x % y)
  (sdiv a b).toNat === (if y = 0 then 0 else wordOf (truncDiv sx sy))
  (smod a b).toNat === (if y = 0 then 0 else
    wordOf ((if sx < 0 then -1 else 1) * ((sx.natAbs % sy.natAbs : Nat) : Int)))
  (addmod a b c).toNat === (if z = 0 then 0 else (x + y) % z)
  (mulmod a b c).toNat === (if z = 0 then 0 else x * y % z)
  (signextend s a).toNat === (if small ≥ 31 then x else
    let bits := 8 * (small + 1)
    let low := x % 2 ^ bits
    if low ≥ 2 ^ (bits - 1) then low + (m - 2 ^ bits) else low)
  (getByte s a).toNat === (if small ≥ 32 then 0 else x / 2 ^ (8 * (31 - small)) % 256)
  (bitwiseShl s a).toNat === (if small ≥ 256 then 0 else x * 2 ^ small % m)
  (bitwiseShr s a).toNat === (if small ≥ 256 then 0 else x / 2 ^ small)
  (bitwiseSar s a).toNat === (if small ≥ 256 then (if sx < 0 then m - 1 else 0)
    else wordOf (sx / (2 ^ small : Int)))
  (bitwiseAnd a b).toNat === Nat.land x y
  (bitwiseOr a b).toNat === Nat.lor x y
  (bitwiseXor a b).toNat === Nat.xor x y
  (bitwiseNot a).toNat === m - 1 - x
  (countLeadingZeros a).toNat === (if x = 0 then 256 else 255 - Nat.log2 x)

/-- A power modulo `2^256`, by repeated squaring over the bits of the exponent, lowest first. -/
def powWord (x y : Nat) : Nat :=
  ((List.range 256).foldl (init := (1, x % 2 ^ 256)) fun (result, square) i =>
    (if y / 2 ^ i % 2 = 1 then result * square % 2 ^ 256 else result,
      square * square % 2 ^ 256)).1

/-- EXP is the power modulo `2^256`: the plain power for a small exponent, and for any exponent
the product of the squares that its bits select. -/
def exponent : Property IO := pureIO do
  let x ← forAll (Gen.frequency [(3, Gen.nat (.linear 0 5)), (2, genArith),
    (1, (2 * · + 1) <$> genNatBits 255)])
  let y ← forAll (Gen.frequency [(4, Gen.nat (.linear 0 300)), (1, genArith)])
  let got := (exp (BitVec.ofNat 256 x) (BitVec.ofNat 256 y)).toNat
  if y ≤ 300 then got === x ^ y % 2 ^ 256
  got === powWord x y

/-- Code that is mostly PUSH instructions and JUMPDEST bytes, some of them inside push data. -/
def genJumpCode : Gen ByteArray :=
  (fun bytes => ⟨bytes.toArray⟩) <$> Gen.list (.linear 0 80) (Gen.frequency [
    (4, pure 0x5b), (4, Gen.integral (.constant 0x5f 0x7f)), (1, pure 0x00), (2, genByte)])

/-- The valid jump destinations of code are the reference's: no JUMPDEST inside push data. -/
def jumpDests (oracle : Oracle) : Property IO := propertyM do
  let code ← forAllWith hex genJumpCode
  let fork ← forAllWith (·.2) (Gen.element forks)
  pure do
    let flags := validJumpDestinations code
    flags.size === code.size
    let found := (List.range code.size).filter fun i => isValidJumpDest flags i
    ensure (!isValidJumpDest flags code.size) "the position after the code is valid"
    let want ← oracle.ask ["jumpdests", fork.2, hex code]
    (if found.isEmpty then "-" else ",".intercalate (found.map toString)) === want

/-- The addresses of CREATE and CREATE2 are the reference's, for any sender, nonce and salt. -/
def contractAddress (oracle : Oracle) : Property IO := propertyM do
  let sender ← forAllWith hex (Gen.frequency [(1, genBytesN 20),
    (1, (fun n => ⟨(List.replicate 20 (UInt8.ofNat n)).toArray⟩) <$>
      Gen.element [0, 1, 0x7f, 0x80])])
  let nonce ← forAll (Gen.frequency [(2, Gen.nat (.linear 0 300)),
    (2, Gen.element [0, 1, 0x7f, 0x80, 0xff, 0x100, 2 ^ 64 - 2, 2 ^ 64 - 1]), (1, genNatBits 64)])
  let salt ← forAll genWord
  let code ← forAllWith hex (genBytes (.linear 0 70))
  pure do
    if h : sender.size = 20 then
      let address : Address := ⟨sender.data, h⟩
      let want ← oracle.ask ["create", "osaka", hex sender, toString nonce]
      (match createAddress address nonce with
        | .ok made => hexVec made
        | .error _ => "error") === want
      let want2 ← oracle.ask ["create2", "osaka", hex sender, hexVec (word32 salt), hex code]
      hexVec (create2Address address (BitVec.ofNat 256 salt) code) === want2
    else failWith "the sender is not 20 bytes"

/-- The growth of memory for a list of ranges costs and adds what the reference says.

A range of size zero grows nothing, whatever its start. -/
def memoryGrowth (oracle : Oracle) : Property IO := propertyM do
  let size ← forAll ((32 * ·) <$> Gen.nat (.linear 0 40))
  let ranges ← forAll (Gen.list (.linear 0 3) (Gen.zip
    (Gen.frequency [(4, genOperand .offset), (1, Gen.nat (.exponential 0 (2 ^ 24)))])
    (Gen.frequency [(4, genOperand .length), (1, Gen.nat (.exponential 0 (2 ^ 24)))])))
  -- The reference allocates nothing here, but a start or a size past 2^64 has no price to compare.
  let ranges := ranges.filter fun (start, length) => start < 2 ^ 40 && length < 2 ^ 40 || length = 0
  pure do
    let got := extendMemory size (ranges.map fun (s, l) => (BitVec.ofNat 256 s, BitVec.ofNat 256 l))
    let want ← oracle.ask (["extend", "osaka", toString size] ++
      ranges.map fun (s, l) => s!"{s}:{l}")
    s!"{got.cost} {got.expandBy}" === want

end EvmProperty
