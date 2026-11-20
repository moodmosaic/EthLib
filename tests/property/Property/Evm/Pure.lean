import Property.Evm.Program

/-!
# The functions under the instructions

The arithmetic of the instructions against `Nat` and `Int`.

It is written from Appendix H of the Yellow Paper and from EIP-145 and EIP-7939.

The jump destinations, the addresses of new contracts and the growth of memory are the reference's.
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

DIV, SDIV, MOD and SMOD by zero give zero.

SDIV of `-2^255` by `-1` gives `-2^255`.

ADDMOD and MULMOD do not wrap at `2^256`.

A shift of 256 or more gives zero, or all ones for SAR of a negative word. -/
def arithmetic (asked : Bool) : Property IO := pureIO do
  -- The words where an instruction has a rule of its own come as often as any other word.
  let (x, y, z) ← forAll (Gen.frequency [
    (10, Gen.zip genArith (Gen.zip genArith genArith)),
    (1, (fun (x, z) => (x, 0, z)) <$> Gen.zip genArith genArith),
    (1, (fun (x, y) => (x, y, 0)) <$> Gen.zip genArith genArith),
    (1, (fun (y, z) => (0, y, z)) <$> Gen.zip genArith genArith),
    (1, (fun z => (2 ^ 255, 2 ^ 256 - 1, z)) <$> genArith),
    (1, (fun (x, z) => (x, x, z)) <$> Gen.zip genArith genArith)])
  let small ← forAll (Gen.frequency [(1, pure 0), (4, Gen.nat (.constant 0 40)),
    (2, Gen.element [255, 256, 257]), (1, Gen.element [30, 31, 32, 33]),
    (1, genArith)])
  let least (percent : Nat) : Nat := if asked then percent else 0
  cover (least 2) "a divisor of 0" (y = 0)
  cover (least 2) "a modulus of 0" (z = 0)
  cover (least 1) "SDIV of -2^255 by -1" (x = 2 ^ 255 ∧ y = 2 ^ 256 - 1)
  cover (least 1) "a shift of 0" (small = 0)
  cover (least 1) "CLZ of 0" (x = 0)
  cover (least 1) "equal operands" (x = y)
  let (a, b, c, s) : U256 × U256 × U256 × U256 :=
    (BitVec.ofNat 256 x, BitVec.ofNat 256 y, BitVec.ofNat 256 z, BitVec.ofNat 256 small)
  let m := 2 ^ 256
  let (sx, sy) := (signedOf x, signedOf y)
  classify "ADD wraps" (x + y ≥ m)
  classify "SUB borrows" (x < y)
  classify "MUL wraps" (x * y ≥ m)
  classify "ADDMOD has a sum of 2^256 or more, and a modulus" (x + y ≥ m ∧ z ≠ 0)
  classify "MULMOD has a product of 2^256 or more, and a modulus" (x * y ≥ m ∧ z ≠ 0)
  classify "SDIV of signs that differ" ((sx < 0) != (sy < 0) ∧ y ≠ 0 ∧ x ≠ 0)
  classify "SMOD of a negative dividend" (sx < 0 ∧ y ≠ 0)
  classify "SMOD of a negative divisor" (sy < 0)
  classify "SIGNEXTEND of byte 0 to 30, sign set"
    (small < 31 ∧ x / 2 ^ (8 * small + 7) % 2 = 1)
  classify "SIGNEXTEND of byte 0 to 30, sign clear"
    (small < 31 ∧ x / 2 ^ (8 * small + 7) % 2 = 0)
  classify "SIGNEXTEND of byte 31 or more" (small ≥ 31)
  classify "BYTE of index 0 to 31" (small < 32)
  classify "BYTE of index 32 or more" (small ≥ 32)
  classify "a shift of 1 to 255" (0 < small ∧ small < 256)
  classify "a shift of 256" (small = 256)
  classify "a shift above 256" (small > 256)
  classify "SAR of a negative word" (sx < 0)
  classify "CLZ of a word with its top bit" (x ≥ 2 ^ 255)
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

/-- EXP is the power modulo `2^256`.

For a small exponent it is the plain power.

For any exponent it is the product of the squares that its bits select. -/
def exponent (asked : Bool) : Property IO := pureIO do
  let x ← forAll (Gen.frequency [(3, Gen.nat (.linear 0 5)), (2, genArith),
    (1, (2 * · + 1) <$> genNatBits 255)])
  -- An exponent of each length in bytes, from none to 32.
  let y ← forAll (Gen.frequency [(3, Gen.nat (.linear 0 300)), (1, genArith),
    (3, do
      let length ← Gen.nat (.constant 0 32)
      if length = 0 then pure 0
      else Gen.frequency [(1, Gen.element [256 ^ (length - 1), 256 ^ length - 1]),
        (2, Gen.nat (.constant (256 ^ (length - 1)) (256 ^ length - 1)))])])
  let got := (exp (BitVec.ofNat 256 x) (BitVec.ofNat 256 y)).toNat
  let bytes := if y = 0 then 0 else byteLength y
  let least (percent : Nat) : Nat := if asked then percent else 0
  cover (least 1) "exponent 0" (y = 0)
  cover (least 4) "an exponent of 2 to 8 bytes" (2 ≤ bytes ∧ bytes ≤ 8)
  cover (least 10) "an exponent of 9 to 31 bytes" (9 ≤ bytes ∧ bytes ≤ 31)
  cover (least 1) "an exponent of 32 bytes" (bytes = 32)
  label (if x = 0 then "base 0" else if x = 1 then "base 1" else if x % 2 = 0 then "an even base"
    else "an odd base")
  classify "the power wraps" (y ≤ 300 ∧ x ^ y ≥ 2 ^ 256)
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
    let jumpdests := (List.range code.size).filter fun i => code[i]! = 0x5b
    classify "no code" code.isEmpty
    classify "a valid destination" (!found.isEmpty)
    classify "a JUMPDEST byte in push data" (found.length < jumpdests.length)
    classify "no JUMPDEST byte" jumpdests.isEmpty
    -- The last push is cut when its data would end past the code.
    let cut := (List.range code.size).any fun i =>
      0x60 ≤ code[i]! ∧ code[i]! ≤ 0x7f ∧ i + (code[i]!.toNat - 0x5f) ≥ code.size ∧
        (i = 0 ∨ !(0x60 ≤ code[i - 1]! ∧ code[i - 1]! ≤ 0x7f))
    classify "a PUSH whose data may run past the code" cut
    classify "a PUSH32" (code.toList.contains 0x7f)
    classify "a PUSH0" (code.toList.contains 0x5f)
    ensure (!isValidJumpDest flags code.size) "the position after the code is valid"
    let want ← oracle.ask ["jumpdests", fork.2, hex code]
    (if found.isEmpty then "-" else ",".intercalate (found.map toString)) === want

/-- The addresses of CREATE and CREATE2 are the reference's, for any sender, nonce and salt. -/
def contractAddress (oracle : Oracle) (asked : Bool) : Property IO := propertyM do
  let sender ← forAllWith hex (Gen.frequency [(1, genBytesN 20),
    (1, (fun n => ⟨(List.replicate 20 (UInt8.ofNat n)).toArray⟩) <$>
      Gen.element [0, 1, 0x7f, 0x80])])
  -- A nonce of each length of its RLP form: itself below 0x80, then one to eight bytes.
  let nonce ← forAll (Gen.frequency [(2, Gen.nat (.linear 0 300)),
    (2, Gen.element [0, 1, 0x7f, 0x80, 0xff, 0x100, 2 ^ 64 - 2, 2 ^ 64 - 1]), (1, genNatBits 64),
    (3, do
      let length ← Gen.nat (.constant 1 8)
      Gen.frequency [(1, Gen.element [256 ^ (length - 1), 256 ^ length - 1]),
        (1, Gen.nat (.constant (256 ^ (length - 1)) (256 ^ length - 1)))])])
  let salt ← forAll genWord
  let code ← forAllWith hex (genBytes (.linear 0 70))
  pure do
    if h : sender.size = 20 then
      let address : Address := ⟨sender.data, h⟩
      label (if nonce = 0 then "nonce 0" else if nonce < 0x80 then "nonce of one byte, itself"
        else "a nonce with a length byte")
      classify "a nonce of 2^64 - 1" (nonce = 2 ^ 64 - 1)
      let least (percent : Nat) : Nat := if asked then percent else 0
      for length in [2, 3, 4, 5, 6, 7, 8] do
        cover (least 1) s!"a nonce of {length} bytes" (byteLength nonce = length)
      cover (least 1) "a nonce of 0x7f or 0x80" (nonce = 0x7f ∨ nonce = 0x80)
      classify "a sender that starts with a zero byte" (sender[0]! = 0)
      classify "no init code" code.isEmpty
      classify "init code over 55 bytes" (code.size > 55)
      let want ← oracle.ask ["create", "osaka", hex sender, toString nonce]
      (match createAddress address nonce with
        | .ok made => hexVec made
        | .error _ => "error") === want
      let want2 ← oracle.ask ["create2", "osaka", hex sender, hexVec (word32 salt), hex code]
      hexVec (create2Address address (BitVec.ofNat 256 salt) code) === want2
    else failWith "the sender is not 20 bytes"

/-- The growth of memory for a list of ranges costs and adds what the reference says.

A range of size zero grows nothing, whatever its start. -/
def memoryGrowth (oracle : Oracle) (asked : Bool) : Property IO := propertyM do
  let size : Nat ← forAll ((fun (words : Nat) => 32 * words) <$> Gen.frequency [
    (3, Gen.nat (.linear 0 40)), (1, Gen.element [0, 1, 22, 23, 724, 725])])
  -- A range that ends around the size, around a word, around 2^32 and 2^64, or anywhere.
  let genRange : Gen (Nat × Nat) := Gen.frequency [
    (4, do
      let stop ← Gen.frequency [(3, (size + ·) <$> Gen.element [0, 1]),
        (2, (fun (d : Int) => ((size : Int) + d).toNat) <$> Gen.element [-1, 31, 32, 33, -32, -33]),
        (2, (fun ((k, d) : Nat × Nat) => 32 * k + d) <$>
          Gen.zip (Gen.nat (.linear 0 60)) (Gen.nat (.constant 0 2))),
        (1, Gen.element [32 * 23 - 1, 32 * 23, 32 * 23 + 1]),
        (1, (fun ((k, d) : Nat × Nat) => 2 ^ k + d - 1) <$>
          Gen.zip (Gen.element [16, 22, 32, 64, 255]) (Gen.nat (.constant 0 2)))]
      let length ← Gen.frequency [(3, Gen.nat (.linear 1 (min stop 70))), (1, pure (min stop 1)),
        (1, pure stop), (1, pure 0)]
      pure (stop - length, length)),
    (2, Gen.zip (genOperand .offset) (genOperand .length)),
    (1, Gen.zip genHuge (Gen.element [0, 0, 1, 2 ^ 256 - 1])),
    (1, Gen.zip (Gen.nat (.exponential 0 (2 ^ 24))) (Gen.nat (.exponential 0 (2 ^ 24))))]
  let ranges ← forAll (Gen.list (.constant 0 3) genRange)
  let least (percent : Nat) : Nat := if asked then percent else 0
  let stops (rule : Nat → Bool) : Bool := ranges.any fun (start, length) =>
    length ≠ 0 ∧ rule (start + length)
  cover (least 2) "a range that ends at the size" (size > 0 ∧ stops (· = size))
  cover (least 2) "a range that ends one byte past the size" (stops (· = size + 1))
  cover (least 5) "a range that ends at a word" (stops (· % 32 = 0))
  cover (least 5) "a range that ends one byte past a word" (stops (· % 32 = 1))
  cover (least 1) "a range that ends at 2^32 or beyond" (stops (· ≥ 2 ^ 32))
  cover (least 1) "a range that ends at 2^64 or beyond" (stops (· ≥ 2 ^ 64))
  cover (least 1) "a range of no byte at a huge start"
    (ranges.any fun (start, length) => length = 0 ∧ start ≥ 2 ^ 32)
  cover (least 10) "two ranges or more" (ranges.length ≥ 2)
  pure do
    let got := extendMemory size (ranges.map fun (s, l) => (BitVec.ofNat 256 s, BitVec.ofNat 256 l))
    label s!"{ranges.length} ranges"
    label (if got.expandBy = 0 then "no growth" else if got.expandBy = 32 then "growth of a word"
      else if got.expandBy < 2 ^ 16 then "growth of words" else "growth of 2^16 bytes or more")
    cover (least 3) "growth of one word" (got.expandBy = 32)
    cover (least 5) "no growth from a range with bytes"
      (got.expandBy = 0 ∧ ranges.any fun (_, l) => l ≠ 0)
    classify "an empty memory before" (size = 0)
    classify "a range of size 0" (ranges.any fun (_, l) => l = 0)
    classify "a range inside the memory" (ranges.any fun (s, l) => l ≠ 0 ∧ s + l < size)
    classify "a later range grows more" (got.expandBy > 0 ∧ ranges.length ≥ 2 ∧
      (ranges.head?.map fun (s, l) => l = 0 ∨ s + l < size + got.expandBy - 31).getD false)
    classify "the quadratic part is above 0" (size + got.expandBy ≥ 32 * 23)
    classify "a size of 2^22 or more" (size + got.expandBy ≥ 2 ^ 22)
    let want ← oracle.ask (["extend", "osaka", toString size] ++
      ranges.map fun (s, l) => s!"{s}:{l}")
    s!"{got.cost} {got.expandBy}" === want

end EvmProperty
