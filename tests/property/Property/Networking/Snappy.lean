import Hedgehog
import Support
import Property.Networking.Common
import EthLib.Networking.Snappy.Block
import EthLib.Networking.Snappy.Compress
import EthLib.Networking.Snappy.Frame
import EthLib.Networking.Snappy.FrameEncode

/-!
# Snappy, on generated blocks and streams

A decoder's bugs sit in inputs that are almost valid.

So the generators here write blocks element by element.

The blocks have every form the format allows and some it forbids.

Then the properties ask two references whether each block is valid.

They are cramjam (the Rust `snap` crate) and a decoder written from `format_description.txt`.
-/

open Hedgehog Support EthLib EthLib.Networking

namespace NetworkingProperty.Snappy

/-! ## Blocks -/

open NetworkingProperty

/-- How far back a copy reaches, relative to the output written so far. -/
inductive Reach where
  /-- This many bytes back. -/
  | exact (n : Nat)
  /-- To the first byte of the output. -/
  | first
  /-- One byte before the first byte of the output. -/
  | beforeFirst
  deriving Repr

/-- An element as a generator writes it: a form of the format, with its fields free. -/
inductive Element where
  /-- A literal whose length takes `extra` bytes after the tag; 0 keeps it in the tag. -/
  | literal (extra : Nat) (data : List UInt8)
  /-- A copy with an offset of `width` bytes: 1, 2 or 4. -/
  | copy (width : Nat) (reach : Reach) (len : Nat)
  deriving Repr

/-- The low `n` bytes of a number, little-endian. -/
def le (n value : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (value / 256 ^ i)

/-- The bytes of an element after `written` bytes of output, and the bytes it adds. -/
def Element.encode (written : Nat) : Element → List UInt8 × Nat
  | .literal extra data =>
    let n := data.length - 1
    if extra = 0 then (UInt8.ofNat (n % 60 * 4) :: data, data.length)
    else (UInt8.ofNat ((59 + extra) * 4) :: le extra n ++ data, data.length)
  | .copy width reach len =>
    let offset := match reach with
      | .exact n => n
      | .first => written
      | .beforeFirst => written + 1
    if width = 1 then
      ([UInt8.ofNat (1 + (len - 4) % 8 * 4 + offset / 256 % 8 * 32), UInt8.ofNat offset], len)
    else
      (UInt8.ofNat ((if width = 2 then 2 else 3) + (len - 1) % 64 * 4) :: le width offset, len)

/-- The bytes of the elements in order, and the length of their output. -/
def encodeElements (elements : List Element) : List UInt8 × Nat :=
  elements.foldl (fun (bytes, written) e =>
    let (b, n) := e.encode written
    (bytes ++ b, written + n)) ([], 0)

/-- A varint of `value` in exactly `width` bytes when `width` is not 0, else the shortest. -/
def preamble (width value : Nat) : List UInt8 :=
  if width = 0 then
    if value < 128 then [UInt8.ofNat value]
    else UInt8.ofNat (value % 128 + 128) :: preamble 0 (value / 128)
  else
    (List.range width).map fun i =>
      UInt8.ofNat (value / 128 ^ i % 128 + if i + 1 < width then 128 else 0)
termination_by value
decreasing_by omega

/-- A literal: mostly short, with its length in the tag or in 1 to 4 bytes after it. -/
def genLiteral : Gen Element := do
  let extra ← Gen.frequency [(4, pure 0), (1, Gen.nat (.constant 1 4))]
  let size ← if extra = 0 then Gen.nat (.linear 1 60)
    else Gen.frequency [(3, Gen.nat (.linear 1 70)), (1, Gen.element [60, 61, 255, 256, 257])]
  .literal extra <$> genByteList (.singleton size)

/-- A copy: every width, with offsets at and past the two ends of what is legal. -/
def genCopy : Gen Element := do
  let width ← Gen.element [1, 2, 4]
  let reach ← Gen.frequency [
    (6, Reach.exact <$> Gen.nat (.linear 1 20)),
    (2, pure .first),
    (1, pure .beforeFirst),
    (1, pure (.exact 0)),
    (1, Reach.exact <$> Gen.element [255, 256, 2047, 2048, 65535, 65536, 2 ^ 32 - 1])]
  let len ← if width = 1 then Gen.nat (.constant 4 11) else Gen.nat (.linear 1 64)
  pure (.copy width reach len)

/-- A block as a generator writes it. -/
structure Block where
  /-- The width of the preamble in bytes; 0 for the shortest. -/
  preambleWidth : Nat
  /-- What the preamble declares, as a difference from the length of the output. -/
  delta : Int
  /-- The elements. -/
  elements : List Element
  /-- Bytes cut from the end. -/
  cut : Nat
  deriving Repr

/-- The bytes of a block. -/
def Block.bytes (b : Block) : ByteArray :=
  let (body, written) := encodeElements b.elements
  let all := preamble b.preambleWidth ((written : Int) + b.delta).toNat ++ body
  ⟨(all.take (all.length - b.cut)).toArray⟩

/-- A block that is valid more often than not, and almost valid otherwise. -/
def genBlock : Gen Block := do
  let elements ← Gen.list (.linear 0 12) (Gen.frequency [(3, genLiteral), (2, genCopy)])
  let width ← Gen.frequency [(6, pure 0), (1, Gen.nat (.constant 1 5)), (1, pure 6)]
  let delta ← Gen.frequency [(8, pure 0), (1, Gen.int (.constant (-2) 2)),
    (1, Gen.element [(2 : Int) ^ 32 - 1, 2 ^ 32, 2 ^ 35 - 1])]
  let cut ← Gen.frequency [(8, pure 0), (1, Gen.nat (.linear 0 5))]
  pure ⟨width, delta, elements, cut⟩

/-- Decompression is the one of a decoder written from `format_description.txt`. -/
def decompressModel (oracle : Oracle) : Property IO := propertyM do
  let block ← forAll genBlock
  pure do
    let bytes := block.bytes
    annotate s!"block: {hex bytes}"
    answer (Snappy.decompress bytes) === verdict (← oracle.ask ["snappy_model_dec", hex bytes])

/-- Whether cramjam reads the block as the format says.

cramjam reads a preamble of more than five bytes, which the C++ reference and EthLib refuse.

It also loads four bytes for a literal length of one to four bytes.

So it refuses such a literal when fewer than four bytes follow its tag. -/
def Block.snapReads (b : Block) : Bool :=
  let rec go : List Element → Bool
    | [] => true
    | .literal extra data :: rest =>
      (extra = 0 || 4 + b.cut ≤ extra + data.length + (encodeElements rest).1.length) && go rest
    | _ :: rest => go rest
  b.preambleWidth ≤ 5 && go b.elements

/-- Decompression is cramjam's, on the blocks that cramjam reads as the format says. -/
def decompressCramjam (oracle : Oracle) : Property IO := propertyM do
  let block ← forAll (genBlock.filter Block.snapReads)
  pure do
    let bytes := block.bytes
    annotate s!"block: {hex bytes}"
    answer (Snappy.decompress bytes) === verdict (← oracle.ask ["snappy_raw_dec", hex bytes])

/-- Any bytes: uniform ones reach the error paths of the first element. -/
def decompressBytes (oracle : Oracle) : Property IO := propertyM do
  let bytes ← forAllWith hex (genBytes (.linear 0 24))
  pure do
    answer (Snappy.decompress bytes) === verdict (← oracle.ask ["snappy_model_dec", hex bytes])

/-- Data that compresses: runs, repeats of an earlier part, and noise between them. -/
def genCompressible : Gen ByteArray := do
  let parts ← Gen.list (.linear 0 12) (Gen.frequency [
    (3, genByteList (.linear 0 20)),
    (2, (fun (b, n) => List.replicate n b) <$> Gen.zip genByte (Gen.nat (.linear 1 200))),
    (2, (fun (xs, n) => (List.replicate n xs).flatten) <$>
      Gen.zip (genByteList (.linear 1 9)) (Gen.nat (.linear 1 40)))])
  let all := parts.flatten
  -- A repeat of the start, far enough back to need a two-byte offset.
  let again ← Gen.bool
  pure ⟨(if again then all ++ all.take 80 else all).toArray⟩

/-- What EthLib compresses, cramjam decompresses to the input, and EthLib does too. -/
def compressRoundTrip (oracle : Oracle) : Property IO := propertyM do
  let data ← forAllWith hex genCompressible
  pure do
    let block := Snappy.compress data
    annotate s!"block: {hex block}"
    (← oracle.ask ["snappy_raw_dec", hex block]) === hex data
    answer (Snappy.decompress block) === hex data

/-- What cramjam compresses, EthLib decompresses to the input. -/
def decompressReference (oracle : Oracle) : Property IO := propertyM do
  let data ← forAllWith hex genCompressible
  pure do
    let some block := unhex? (← oracle.ask ["snappy_raw_enc", hex data]) | failWith "oracle"
    answer (Snappy.decompress block) === hex data

/-- A block never grows past the bound that the consensus layer takes from `snappy.cc`. -/
def compressBound : Property IO := pureIO do
  let data ← forAllWith hex genCompressible
  let n := data.size
  ensure ((Snappy.compress data).size ≤ 32 + n + n / 6) "the block is past 32 + n + n / 6"

/-! ## Frames -/

/-- A chunk as a generator writes it. -/
inductive Chunk where
  /-- An uncompressed chunk of the data, its checksum changed by `tweak`. -/
  | plain (data : ByteArray) (tweak : UInt32)
  /-- A compressed chunk: the block, and the data whose checksum it stores. -/
  | packed (block : Block) (tweak : UInt32)
  /-- A stream identifier, with any body. -/
  | identifier (body : List UInt8)
  /-- A chunk of another type, with any body. -/
  | other (type : UInt8) (body : List UInt8)
  /-- Bytes that are no chunk. -/
  | raw (bytes : List UInt8)
  deriving Repr

/-- A chunk header and its body. -/
def chunkBytes (type : UInt8) (body : List UInt8) : List UInt8 :=
  type :: le 3 body.length ++ body

/-- The bytes of a chunk; a compressed chunk stores the checksum of what its block holds. -/
def Chunk.bytes : Chunk → List UInt8
  | .plain data tweak =>
    chunkBytes 1 (le 4 (Snappy.maskedCrc data + tweak).toNat ++ data.toList)
  | .packed block tweak =>
    let data := (Snappy.decompress block.bytes).toOption.getD .empty
    chunkBytes 0 (le 4 (Snappy.maskedCrc data + tweak).toNat ++ block.bytes.toList)
  | .identifier body => chunkBytes 0xff body
  | .other type body => chunkBytes type body
  | .raw bytes => bytes

/-- The body of a stream identifier. -/
def magic : List UInt8 := [0x73, 0x4e, 0x61, 0x50, 0x70, 0x59]

/-- A chunk: mostly a valid data chunk, and every other kind now and then. -/
def genChunk : Gen Chunk :=
  let tweak : Gen UInt32 := Gen.frequency [(12, pure 0), (1, Gen.element [1, 0x80000000])]
  Gen.frequency [
    (4, Gen.zipWith Chunk.plain (genBytes (.linear 0 40)) tweak),
    (4, Gen.zipWith Chunk.packed genBlock tweak),
    (2, pure (.identifier magic)),
    (1, Chunk.identifier <$> Gen.element [[], magic.take 5, magic ++ [0], magic.set 0 0x53]),
    (2, Gen.zipWith Chunk.other (Gen.element [0x02, 0x7f, 0x80, 0xfd, 0xfe, 0x40, 0xc0])
      (genByteList (.linear 0 6))),
    (1, Chunk.raw <$> genByteList (.linear 1 5))]

/-- A stream: it starts with a stream identifier, nearly always. -/
def genStream : Gen (List Chunk) := do
  let head ← Gen.frequency [(9, pure [Chunk.identifier magic]), (1, pure [])]
  let chunks ← Gen.list (.linear 0 6) genChunk
  pure (head ++ chunks)

/-- The bytes of a stream. -/
def streamBytes (chunks : List Chunk) : ByteArray :=
  ⟨(chunks.flatMap Chunk.bytes).toArray⟩

/-- The masked checksum is the one of `framing_format.txt`, over the reference's CRC-32C. -/
def maskedCrcRef (oracle : Oracle) : Property IO := propertyM do
  let data ← forAllWith hex (genBytes (.linear 0 80))
  pure do
    toString (Snappy.maskedCrc data).toNat === (← oracle.ask ["masked_crc", hex data])

/-- A stream decodes as a decoder written from `framing_format.txt` decodes it. -/
def framesModel (oracle : Oracle) : Property IO := propertyM do
  let chunks ← forAll genStream
  pure do
    let bytes := streamBytes chunks
    annotate s!"stream: {hex bytes}"
    answer (Snappy.decodeFrames bytes) === verdict (← oracle.ask ["snappy_frame_model", hex bytes])

/-- Whether a chunk is one on which cramjam and the format agree.

cramjam reads a block preamble of more than five bytes, and stops at a truncated header. -/
def Chunk.plainCase : Chunk → Bool
  | .packed block _ => block.snapReads
  | .raw _ => false
  | _ => true

/-- A stream decodes as cramjam decodes it, where the two readings of the format agree. -/
def framesCramjam (oracle : Oracle) : Property IO := propertyM do
  let chunks ← forAll (genStream.filter fun cs => cs.all (·.plainCase) && !cs.isEmpty)
  pure do
    let bytes := streamBytes chunks
    annotate s!"stream: {hex bytes}"
    answer (Snappy.decodeFrames bytes) === verdict (← oracle.ask ["snappy_frame_dec", hex bytes])

/-- A chunk of more than 65536 bytes is refused, and one of exactly 65536 is read. -/
def framesLimit (oracle : Oracle) : Property IO := propertyM do
  let over ← forAll (Gen.element [0, 1, 2])
  let fill ← forAll genByte
  let packed ← forAll Gen.bool
  pure do
    let data : ByteArray := ⟨Array.replicate (65535 + over) fill⟩
    let body := if packed then (Snappy.compress data).toList else data.toList
    let bytes : ByteArray := ⟨(chunkBytes 0xff magic ++
      chunkBytes (if packed then 0 else 1) (le 4 (Snappy.maskedCrc data).toNat ++ body)).toArray⟩
    let got := (Snappy.decodeFrames bytes).toOption.map (·.size)
    got === (if over ≤ 1 then some (65535 + over) else none)
    let want ← oracle.ask ["snappy_frame_model", hex bytes]
    (got.isSome) === !(want.startsWith "error")

/-- What EthLib frames, cramjam and EthLib decode to the input; the same for the literal form. -/
def framesEncode (oracle : Oracle) : Property IO := propertyM do
  let data ← forAllWith hex genCompressible
  pure do
    for stream in [Snappy.encodeFrames data, Snappy.encodeFramesLiteral data] do
      (← oracle.ask ["snappy_frame_dec", hex stream]) === hex data
      answer (Snappy.decodeFrames stream) === hex data

/-- What cramjam frames, EthLib decodes to the input. -/
def framesReference (oracle : Oracle) : Property IO := propertyM do
  let data ← forAllWith hex (genCompressible.filter (!·.isEmpty))
  pure do
    let some stream := unhex? (← oracle.ask ["snappy_frame_enc", hex data]) | failWith "oracle"
    answer (Snappy.decodeFrames stream) === hex data

/-- cramjam frames no data as no bytes, and reads no bytes as no data; EthLib refuses them.

The stream of no chunks is the one in question: see the findings. -/
def framesEmpty (oracle : Oracle) : Property IO := propertyM do
  pure do
    let stream ← oracle.ask ["snappy_frame_enc", "-"]
    annotate s!"cramjam's stream of no data: {stream}"
    answer (Snappy.decodeFrames .empty) === verdict (← oracle.ask ["snappy_frame_dec", "-"])

/-- cramjam reads a block whose preamble pads the length to six bytes; EthLib refuses it. -/
def preambleSix (oracle : Oracle) : Property IO := propertyM do
  let block ← forAll ((fun b => { b with preambleWidth := 6, delta := 0, cut := 0 }) <$> genBlock)
  pure do
    let bytes := block.bytes
    annotate s!"block: {hex bytes}"
    answer (Snappy.decompress bytes) === verdict (← oracle.ask ["snappy_raw_dec", hex bytes])

/-- The properties of this module that disagree with a reference: see the findings. -/
def findings (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("snappy: the stream of no chunks (OPEN)", (framesEmpty oracle).withTests 1),
  ("snappy: a preamble of six bytes (OPEN)", (preambleSix oracle).withTests cases)]

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("snappy: a block decompresses as the format says", (decompressModel oracle).withTests cases),
  ("snappy: a block decompresses as cramjam's", (decompressCramjam oracle).withTests cases),
  ("snappy: any bytes decompress as the format says", (decompressBytes oracle).withTests cases),
  ("snappy: cramjam reads EthLib's block", (compressRoundTrip oracle).withTests cases),
  ("snappy: EthLib reads cramjam's block", (decompressReference oracle).withTests cases),
  ("snappy: a block stays within 32 + n + n / 6", compressBound.withTests cases),
  ("snappy: the masked CRC-32C", (maskedCrcRef oracle).withTests cases),
  ("snappy: a stream decodes as the format says", (framesModel oracle).withTests cases),
  ("snappy: a stream decodes as cramjam's", (framesCramjam oracle).withTests cases),
  ("snappy: the chunk limit of 65536 bytes", (framesLimit oracle).withTests (min cases 30)),
  ("snappy: cramjam reads EthLib's stream", (framesEncode oracle).withTests cases),
  ("snappy: EthLib reads cramjam's stream", (framesReference oracle).withTests cases)]

end NetworkingProperty.Snappy
