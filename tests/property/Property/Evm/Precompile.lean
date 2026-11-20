import Property.Evm.Program

/-!
# The precompiles beside the reference

The call data is near valid.

A reference library builds a valid input from a few numbers.

Then one rule of the precompile is broken, or the length is changed.

The answer is that of the precompile of the Python execution-specs at the same fork.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution.Evm

namespace EvmProperty

/-- What EthLib answers to a call of a precompile, in the text form of the oracle.

The answer is `none` for an address that is no precompile at the fork, and `halt` for a failure.

Else it is the gas left and the output. -/
def precompileEthLib (fork : Fork) (address : Nat) (data : ByteArray) (gas : Nat) : String :=
  if !Precompiles.isPrecompile fork address then "none"
  else match Precompiles.run fork address data gas with
    | none => "none"
    | some (.error _) => "halt"
    | some (.ok output) =>
      let price := (Precompiles.price fork address data).getD 0
      if gas < price then "halt" else s!"ok {gas - price} {hex output}"

/-- The name of a precompile, for the shares of a report. -/
def precompileName (address : Nat) : String :=
  match address with
  | 1 => "ECRECOVER" | 2 => "SHA256" | 3 => "RIPEMD160" | 4 => "IDENTITY" | 5 => "MODEXP"
  | 6 => "BN_ADD" | 7 => "BN_MUL" | 8 => "BN_PAIRING" | 9 => "BLAKE2F" | 10 => "POINT_EVALUATION"
  | 11 => "G1ADD" | 12 => "G1MSM" | 13 => "G2ADD" | 14 => "G2MSM" | 15 => "BLS_PAIRING"
  | 16 => "MAP_FP_TO_G1" | 17 => "MAP_FP2_TO_G2" | 256 => "P256VERIFY"
  | other => s!"address {other}"

/-- How EthLib ends a call of a precompile: the class of the case, for the shares of a report.

A refusal is named by the constructor of its error. -/
def precompileOutcome (fork : Fork) (address : Nat) (data : ByteArray) (gas : Nat) : String :=
  if !Precompiles.isPrecompile fork address then "no precompile at the fork"
  else match Precompiles.run fork address data gas with
    | none => "no precompile at the fork"
    | some (.error e) =>
      let name := (((reprStr e).splitOn "Error.").getD 2 "").takeWhile Char.isAlphanum
      s!"refuses, {name}"
    | some (.ok output) =>
      if gas < (Precompiles.price fork address data).getD 0 then "refuses at the charge"
      else if output.isEmpty then "answers nothing"
      else if output.data.all (· = 0) then "answers zero"
      else "answers"

/-- The gas of a call: around the price, since the charge is where an off-by-one sits.

The price is EthLib's, which only places the draw: the reference decides what the gas buys. -/
def gasAround (fork : Fork) (address : Nat) (data : ByteArray) (choice : Nat) : Nat :=
  let price := min ((Precompiles.price fork address data).getD 100000) 3000000
  match choice with
  | 0 => price
  | 1 => price - 1
  | 2 => price + 1
  | 3 => 0
  | _ => price + 100000

/-- The draw of the gas: mostly enough, so the body of the precompile runs. -/
def genGasChoice : Gen Nat := Gen.frequency [(3, pure 0), (2, pure 1), (1, pure 2), (1, pure 3),
  (4, pure 4)]

/-- EthLib and the reference agree on one call. -/
def samePrecompile (oracle : Oracle) (fork : Fork × String) (address : Nat) (data : ByteArray)
    (choice : Nat) : TestT IO Unit := do
  let gas := gasAround fork.1 address data choice
  label s!"{precompileName address}: {precompileOutcome fork.1 address data gas}"
  label (["gas: the price", "gas: one less than the price", "gas: one more than the price",
    "gas: none", "gas: plenty"].getD choice "gas: plenty")
  let answer ← oracle.ask ["pre", fork.2, toString address, toString gas, hex data]
  -- The reference names its error after `halt`, and EthLib's has another name.
  --
  -- Its fixed-width integers overflow on a length near 2^256, where the price is out of reach.
  let want := if answer.startsWith "halt" || answer.startsWith "crash OverflowError" then "halt"
    else answer
  annotate s!"address {address} at {fork.2} with gas {gas} on {hex data}: the reference says \
    {answer}"
  precompileEthLib fork.1 address data gas === want

/-- A recipe of call data: see `oracle/evm_inputs.py`. -/
structure Recipe where
  kind : String
  address : Nat
  a : Nat
  b : Nat
  c : Nat
  mutation : Nat
  cut : Nat
  deriving Repr

/-- The precompiles with a recipe that the reference answers fast. -/
def fastKinds : List (String × Nat) := [("ecrecover", 1), ("bnadd", 6), ("bnmul", 7),
  ("g1add", 11), ("p256", 256)]

/-- The precompiles of BLS12-381 that the reference answers in a tenth of a second or more. -/
def mediumKinds : List (String × Nat) := [("g1msm", 12), ("g2add", 13), ("g2msm", 14),
  ("mapfp", 16), ("mapfp2", 17)]

/-- The precompiles that pair points, which the reference computes slowly. -/
def slowKinds : List (String × Nat) := [("bnpairing", 8), ("blspairing", 15), ("pointeval", 10)]

/-- A number that a scalar or a seed is made of: small, or at an edge of 256 bits. -/
def genSeed : Gen Nat := Gen.frequency [(3, Gen.nat (.linear 0 50)), (2, genNatBits 256)]

/-- A recipe of one precompile: one time in five valid, else one of fourteen mutations.

Two in ten change the length of the call data. -/
def genRecipe (kind : String) (address : Nat) : Gen Recipe := do
  let (a, b, c) ← Gen.zip genSeed (Gen.zip genSeed genSeed)
  let mutation ← Gen.frequency [(3, pure 0), (12, Gen.nat (.constant 1 14))]
  let cut ← Gen.frequency [(8, pure 0), (2, Gen.nat (.constant 1 5))]
  pure ⟨kind, address, a, b, c, mutation, cut⟩

/-- A fork for a precompile: mostly one that has it, each as often as another. -/
def genPrecompileFork (address : Nat) : Gen (Fork × String) :=
  let having := forks.filter fun (fork, _) => Precompiles.isPrecompile fork address
  if having.isEmpty then Gen.element forks
  else Gen.frequency [(9, Gen.element having), (1, Gen.element forks)]

/-- A precompile answers a near-valid input as the reference does: output, price and failure.

The report names each mutation with what the precompile made of it, where its body ran. -/
def precompileRecipe (oracle : Oracle) (kind : String) (address : Nat) (asked : Bool) :
    Property IO := propertyM do
  let recipe ← forAll (genRecipe kind address)
  let fork ← forAllWith (·.2) (genPrecompileFork address)
  let choice ← forAll genGasChoice
  pure do
    let made ← oracle.ask ["mk", recipe.kind, toString recipe.a, toString recipe.b,
      toString recipe.c, toString recipe.mutation, toString recipe.cut]
    match unhex? made with
    | none => failWith s!"the oracle built no input: {made}"
    | some data =>
      -- Whether a mutation reaches the rule it breaks shows only where the body runs.
      let runs := Precompiles.isPrecompile fork.1 recipe.address && choice ≠ 1 && choice ≠ 3
      let outcome := precompileOutcome fork.1 recipe.address data
        (gasAround fork.1 recipe.address data 4)
      if runs then
        label s!"mutation {recipe.mutation}{if recipe.cut = 0 then "" else ", cut"}: {outcome}"
      let least (percent : Nat) : Nat := if asked then percent else 0
      cover (least 10) "the body runs on an input that it accepts"
        (runs ∧ outcome.startsWith "answers")
      cover (least 3) "the body runs on a valid input"
        (runs ∧ recipe.mutation = 0 ∧ recipe.cut = 0)
      cover (least 15) "the body runs on a mutated input" (runs ∧ recipe.mutation ≠ 0)
      samePrecompile oracle fork recipe.address data choice

/-- A length field of MODEXP: zero, around a word, around the limit of EIP-7823, and huge. -/
def genModexpLength : Gen Nat :=
  Gen.frequency [
    (6, Gen.nat (.linear 0 40)),
    (3, Gen.element [0, 1, 31, 32, 33, 64, 96, 1023, 1024, 1025]),
    (1, Gen.element [2 ^ 32, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 255, 2 ^ 256 - 1])]

/-- Call data of MODEXP: three lengths, then a body that may be shorter or longer than they say. -/
def genModexp : Gen ByteArray := do
  let (baseLen, expLen, modLen) ← Gen.zip genModexpLength (Gen.zip genModexpLength genModexpLength)
  let said := min 2200 (baseLen + expLen + modLen)
  let fill (byte : UInt8) (n : Nat) : ByteArray := ⟨(List.replicate n byte).toArray⟩
  let body ← Gen.frequency [
    (5, genBytes (.singleton said)),
    (2, genBytes (.linear 0 (said + 8))),
    -- A longer body, whose tail the precompile must not read.
    (1, genBytes (.singleton (said + 40))),
    (1, fill 0 <$> Gen.nat (.linear 0 said)), (1, pure (fill 0 said)),
    (1, fill 0xff <$> Gen.nat (.linear 0 said)), (1, pure (fill 0xff said)),
    -- An exponent of zero, or of one, under a base and a modulus of any bytes.
    (2, (fun (base, low, modulus) => base ++ fill 0 (min 1100 expLen - 1) ++ fill low
        (min 1 expLen) ++ modulus) <$>
      Gen.zip (genBytes (.singleton (min 1100 baseLen))) (Gen.zip (Gen.element [0, 1, 2])
        (genBytes (.singleton (min 1100 modLen)))))]
  let header := beBytes 32 baseLen ++ beBytes 32 expLen ++ beBytes 32 modLen
  let cut ← Gen.frequency [(12, pure 96), (1, Gen.nat (.constant 0 96))]
  pure ⟨((header.take cut) ++ (if cut = 96 then body.toList else [])).toArray⟩

/-- Call data of BLAKE2F: the rounds, the state, the message, the offsets and the final flag. -/
def genBlake2f : Gen ByteArray := do
  let rounds ← Gen.frequency [(12, Gen.nat (.linear 0 24)), (1, Gen.element [300, 2 ^ 32 - 1])]
  let body ← Gen.frequency [(4, genBytes (.singleton 208)),
    (1, (fun (b : UInt8) => ⟨(List.replicate 208 b).toArray⟩) <$> Gen.element [0x00, 0xff])]
  let flag ← Gen.frequency [(4, Gen.element [0, 1]), (1, Gen.element [2, 255, 128])]
  let data := beBytes 4 rounds ++ body.toList ++ [flag]
  let size ← Gen.frequency [(10, pure 213), (1, Gen.element [0, 212, 214, 426])]
  pure ⟨((data ++ data).take size).toArray⟩

/-- Call data for a hash precompile: a length around a word and around a block of the hash. -/
def genHashInput : Gen ByteArray := do
  let size ← Gen.frequency [(4, Gen.nat (.linear 0 200)),
    (6, Gen.element [0, 1, 31, 32, 33, 55, 56, 57, 63, 64, 65, 95, 96, 97, 119, 120, 127, 128,
      129])]
  Gen.frequency [(3, genBytes (.singleton size)),
    (1, pure ⟨(List.replicate size (0 : UInt8)).toArray⟩)]

/-- Call data with no structure, at any address that is or was to be a precompile. -/
def genRawCall : Gen (Nat × ByteArray) :=
  Gen.zip (Gen.element [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 256, 0, 18, 255,
    257]) (Gen.frequency [
      (3, genBytes (.linear 0 300)),
      (1, (fun n => ⟨(List.replicate n (0 : UInt8)).toArray⟩) <$>
        Gen.element [0, 31, 32, 33, 64, 96, 128, 160, 192, 213, 256, 288, 384, 512])])

/-- The class of the length of call data, against a word of 32 bytes. -/
def lengthClass (size : Nat) : String :=
  if size = 0 then "no byte" else if size < 32 then "under a word" else if size = 32 then "a word"
  else if size % 32 = 0 then "whole words" else if size % 32 = 1 then "words and one byte"
  else "words and a part"

/-- Name the classes of call data of MODEXP, and require the ones that matter. -/
def labelModexp (fork : Fork) (data : ByteArray) (asked : Bool) : TestT IO Unit := do
  let lengths := (List.range 3).map fun i =>
    (data.toList.drop (32 * i)).take 32 |>.foldl (fun n b => 256 * n + b.toNat) 0
  let sizeClass (n : Nat) : String :=
    if n = 0 then "0" else if n ≤ 32 then "1 to 32" else if n ≤ 1024 then "33 to 1024"
    else if n < 2 ^ 32 then "1025 to 2^32" else "2^32 or more"
  for (field, n) in ["base", "exponent", "modulus"].zip lengths do
    label s!"{field} length: {sizeClass n}"
  let said := lengths.foldl (· + ·) 0
  let head := Precompiles.Modexp.exponentHead data (Precompiles.Modexp.parseLengths data)
  let least (percent : Nat) : Nat := if asked then percent else 0
  classify "the header is cut short" (data.size < 96)
  cover (least 5) "a body shorter than the lengths say" (data.size ≥ 96 ∧ data.size - 96 < said)
  cover (least 3) "a body longer than the lengths say" (data.size ≥ 96 ∧ data.size - 96 > said)
  cover (least 10) "a body as long as the lengths say" (data.size ≥ 96 ∧ data.size - 96 = said)
  cover (least 3) "an exponent whose first 32 bytes are zero" (head = 0 ∧ lengths[1]! > 0)
  cover (least 2) "an exponent over 32 bytes whose first 32 are zero" (head = 0 ∧ lengths[1]! > 32)
  cover (least 5) "an exponent over 32 bytes" (lengths[1]! > 32 ∧ lengths[1]! ≤ 1024)
  cover (least 3) "a length over 1024 and under 2^32"
    (lengths.any fun n => n > 1024 ∧ n < 2 ^ 32)
  label (if fork ≥ .fusaka then "the gas of EIP-7883, with the limit of EIP-7823"
    else if fork ≥ .berlin then "the gas of EIP-2565"
    else if fork ≥ .byzantium then "the gas of EIP-198" else "before Byzantium")

/-- A precompile answers any bytes as the reference does: output, price and failure.

`input` draws the address and the call data, and `forkOf` the fork for an address. -/
def precompileBytes (oracle : Oracle) (asked : Bool) (input : Gen (Nat × ByteArray)) :
    Property IO := propertyM do
  let (address, data) ← forAllWith (fun (a, d) => s!"{a} {hex d}") input
  let fork ← forAllWith (·.2) (genPrecompileFork address)
  let choice ← forAll genGasChoice
  pure do
    if address = 5 then labelModexp fork.1 data asked
    else if address = 2 ∨ address = 3 ∨ address = 4 then
      label s!"call data of {lengthClass data.size}"
      let least (percent : Nat) : Nat := if asked then percent else 0
      cover (least 3) "call data that ends at a word" (data.size % 32 = 0 ∧ data.size > 0)
      cover (least 3) "call data that ends one byte past a word" (data.size % 32 = 1)
      cover (least 10) "it answers" ((precompileOutcome fork.1 address data
        (gasAround fork.1 address data choice)).startsWith "answers")
    else if address = 9 then
      let rounds := (data.toList.take 4).foldl (fun n b => 256 * n + b.toNat) 0
      label (if data.size ≠ 213 then "not 213 bytes" else if rounds = 0 then "no round"
        else if rounds ≤ 10 then "1 to 10 rounds" else if rounds ≤ 24 then "11 to 24 rounds"
        else "over 24 rounds")
    samePrecompile oracle fork address data choice

/-- The properties of the precompiles: one for each, so each has its own cases.

The three that pair points are slow in the reference, and run a tenth of the cases. -/
def precompileProperties (oracle : Oracle) (cases : Nat) (asked : Bool) :
    List (String × Property IO) :=
  [("MODEXP answers any bytes as the reference",
    (precompileBytes oracle asked ((5, ·) <$> genModexp)).withTests cases),
   ("BLAKE2F answers any bytes as the reference",
    (precompileBytes oracle asked ((9, ·) <$> genBlake2f)).withTests cases),
   ("SHA-256, RIPEMD-160 and IDENTITY answer any bytes as the reference",
    (precompileBytes oracle asked (Gen.zip (Gen.element [2, 3, 4]) genHashInput)).withTests cases),
   ("any address answers any bytes as the reference",
    (precompileBytes oracle false genRawCall).withTests cases)] ++
  (fastKinds.map fun (kind, address) =>
    (s!"{precompileName address} answers a near-valid input as the reference",
      (precompileRecipe oracle kind address asked).withTests cases)) ++
  (mediumKinds.map fun (kind, address) =>
    (s!"{precompileName address} answers a near-valid input as the reference",
      (precompileRecipe oracle kind address (asked && cases ≥ 2500)).withTests (cases / 5))) ++
  slowKinds.map fun (kind, address) =>
    (s!"{precompileName address} answers a near-valid input as the reference",
      (precompileRecipe oracle kind address (asked && cases ≥ 5000)).withTests (cases / 10))

end EvmProperty
