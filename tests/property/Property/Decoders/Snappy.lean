import Hedgehog
import Support
import Property.Decoders.Common
import EthLib.Cryptography.Hash.Sha256
import EthLib.Networking.Snappy.Block
import EthLib.Networking.Snappy.Compress

/-!
# Snappy blocks of more than 64 KiB, on generated inputs

A copy may reach more than 65535 bytes back only in an output that long.

So each block here starts with a literal of 65536 bytes or more, and copies follow it.

The references are a reader written from `format_description.txt`, and cramjam.

The compressor is given a repeat at each distance around 65536, the bound of a two-byte offset.
-/

open Hedgehog Support EthLib
open EthLib.Networking

namespace DecodersProperty.Snappy

open DecodersProperty

/-- A number in `n` bytes, little-endian. -/
def le (n v : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (v / 256 ^ i)

/-- The preamble of a block: the length of its output as a varint. -/
def preamble (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (n % 128 + 128) :: preamble (n / 128)
termination_by n
decreasing_by omega

/-- The header of a literal of `n` bytes, section 2.1. -/
def literalHeader (n : Nat) : List UInt8 :=
  if n ≤ 60 then [UInt8.ofNat ((n - 1) * 4)]
  else
    let width := if n - 1 < 2 ^ 8 then 1 else if n - 1 < 2 ^ 16 then 2 else if n - 1 < 2 ^ 24 then 3
      else 4
    UInt8.ofNat ((59 + width) * 4) :: le width (n - 1)

/-- A copy with an offset of four bytes, section 2.2.3. -/
def copyFour (offset len : Nat) : List UInt8 := UInt8.ofNat (3 + (len - 1) * 4) :: le 4 offset

/-- A copy with an offset of two bytes, section 2.2.2. -/
def copyTwo (offset len : Nat) : List UInt8 := UInt8.ofNat (2 + (len - 1) * 4) :: le 2 offset

/-- A copy with an offset of one byte and three bits, section 2.2.1. -/
def copyOne (offset len : Nat) : List UInt8 :=
  [UInt8.ofNat (1 + (len - 4) * 4 + offset / 256 * 32), UInt8.ofNat (offset % 256)]

/-- Bytes with no pattern, from a seed: a generated list of this length would not shrink in time. -/
def noise (seed count : Nat) : List UInt8 :=
  ((List.range count).foldl (fun (state, out) _ =>
    let next := (state * 1103515245 + 12345) % 2 ^ 31
    (next, out.push (UInt8.ofNat (next / 2 ^ 16)))) (seed, (#[] : Array UInt8))).2.toList

/-- An element after the first literal: its name, its bytes, and the bytes it adds to the output.

`size` is the length of the output before it, 65536 at least. -/
def genElement (size : Nat) : Gen (String × List UInt8 × Nat) := do
  let len ← Gen.frequency [(1, pure 1), (1, pure 64), (3, Gen.nat (.constant 1 64))]
  let far ← Gen.frequency [(2, pure 65536), (1, pure 65537), (2, pure size), (1, pure (size - 1)),
    (2, Gen.nat (.constant 65536 size))]
  let near ← Gen.frequency [(1, pure 65535), (1, pure 1), (2, Gen.nat (.constant 1 65535))]
  let short ← Gen.nat (.constant 1 2047)
  let data ← genByteList (.linear 1 5)
  Gen.frequency [
    (6, pure ("a copy from more than 65535 bytes back", copyFour far len, len)),
    (2, pure ("a four-byte offset of 65535 or less", copyFour near len, len)),
    (2, pure ("a two-byte offset", copyTwo near len, len)),
    (1, pure ("a one-byte offset", copyOne short (4 + len % 8), 4 + len % 8)),
    (1, pure ("a literal", literalHeader data.length ++ data, data.length))]

/-- Elements one after another, each generated for the output that the ones before leave. -/
def genElements : Nat → Nat → Gen (List (String × List UInt8 × Nat))
  | 0, _ => pure []
  | n + 1, size => do
    let element ← genElement size
    pure (element :: (← genElements n (size + element.2.2)))

/-- A way to break a block, or none. -/
def genBreak : Gen String :=
  Gen.frequency [(6, pure "none"), (1, pure "an offset one past the output"),
    (1, pure "an offset far past the output"), (1, pure "an offset of zero"),
    (1, pure "a declared length one short"), (1, pure "a declared length one long")]

/-- The output of a block as the oracle writes it: its length and its SHA-256, or `error`. -/
def showOutput {ε : Type} (result : Except ε ByteArray) : String :=
  match result with
  | .ok out => s!"{out.size}:{hexv (Cryptography.Hash.Sha256.hash32 out)}"
  | .error _ => "error"

/-- A block whose copies reach more than 65535 bytes back decompresses as the format says.

An offset equal to the length of the output is the first byte, and one more is refused. -/
def farCopies (oracle : Oracle) : Property IO := propertyM do
  let seed ← forAll (Gen.nat (.constant 0 (2 ^ 31 - 1)))
  let first ← forAll (Gen.frequency [(2, pure 65536), (1, pure 65537), (1, pure 65535),
    (2, Gen.nat (.constant 65536 70000))])
  let elements ← forAllWith (fun es => ", ".intercalate (es.map fun (name, bytes, _) =>
    s!"{name} {hex (packed bytes)}")) (do genElements (← Gen.nat (.constant 1 4)) first)
  let broken ← forAll genBreak
  let len ← forAll (Gen.nat (.constant 1 64))
  pure do
    let size := first + (elements.map (·.2.2)).sum
    let last := match broken with
      | "an offset one past the output" => copyFour (size + 1) len
      | "an offset far past the output" => copyFour (2 ^ 32 - 1) len
      | "an offset of zero" => copyFour 0 len
      | _ => []
    let declared := match broken with
      | "a declared length one short" => size - 1
      | "a declared length one long" => size + 1
      | "none" => size
      | _ => size + len
    let block := preamble declared ++ literalHeader first ++ noise seed first ++
      (elements.map (·.2.1)).flatten ++ last
    let answer := words (← oracle.ask ["snappy_block", hex (packed block)])
    let model := answer.headD ""
    let got := showOutput (Snappy.decompress (packed block))
    cover 17 "valid as generated" (broken == "none" && !refused model)
    cover 16 "refused by the reference" (refused model)
    cover 12 "a valid copy from more than 65535 bytes back"
      (!refused model && elements.any (·.1 == "a copy from more than 65535 bytes back"))
    classify "a first literal of 65535 bytes, so no copy can reach that far" (first == 65535)
    if broken != "none" then label broken
    got === model
    -- cramjam reads the same block the same way.
    answer.getD 1 "" === model
    if broken != "none" then model === "error"

/-- The compressor writes a block that both references read back, for inputs of more than 64 KiB.

A repeat lies 65535 bytes back or one or two more, where a two-byte offset ends. -/
def farRepeats (oracle : Oracle) : Property IO := propertyM do
  let seed ← forAll (Gen.nat (.constant 0 (2 ^ 31 - 1)))
  let distance ← forAll (Gen.element [65533, 65534, 65535, 65536, 65537, 65538, 70000, 131072])
  let run ← forAll (Gen.element [4, 5, 16, 64, 65, 300])
  let tail ← forAll (Gen.nat (.linear 0 40))
  let zeros ← forAll (Gen.frequency [(3, pure true), (1, pure false)])
  pure do
    -- A run of bytes, then a filler, then the run again at the distance, then a little noise.
    --
    -- A filler of zeros leaves the table entry of the run in place, so the run is proposed again.
    let run' := noise (seed + 1) run
    let filler := if zeros then List.replicate (distance - run) 0 else noise seed (distance - run)
    let data := packed (run' ++ filler ++ run' ++ noise (seed + 2) tail)
    let block := Snappy.compress data
    cover 13 "a repeat within a two-byte offset" (distance ≤ 65535)
    cover 20 "a repeat past a two-byte offset" (distance > 65535)
    cover 25 "a filler of zeros, which keeps the run in the table" zeros
    classify "a filler of noise" (!zeros)
    (← oracle.ask ["snappy_check", hex block, hex data]) === "1 1"
    match Snappy.decompress block with
    | .ok out => ensure (out == data) "EthLib does not read its own block back"
    | .error e => failWith s!"EthLib refuses its own block: {repr e}"

/-- The properties that must pass. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("snappy: copies from more than 65535 bytes back", (farCopies oracle).withTests (min cases 200)),
  ("snappy: the compressor at the end of a two-byte offset",
    (farRepeats oracle).withTests (min cases 100))]

/-- The properties that fail by design: each is a finding. -/
def findings (_oracle : Oracle) (_cases : Nat) : List (String × Property IO) := []

end DecodersProperty.Snappy
