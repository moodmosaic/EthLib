import Hedgehog
import Support
import Property.Networking.Common
import Property.Networking.Snappy
import EthLib.Networking.Devp2p.ForkId
import EthLib.Networking.Gossip.MessageId
import EthLib.Networking.Gossip.Payload
import EthLib.Networking.Gossip.Subnet
import EthLib.Networking.Gossip.Topic
import EthLib.Networking.ReqResp.Encoding

/-!
# Gossip names and IDs, request and response payloads, and fork identifiers

Each against a reference in `oracle/networking_codecs.py` or `oracle/networking_snappy.py`,
written from the networking specification of the consensus layer, EIP-2124 and EIP-6122.
-/

open Hedgehog Support EthLib EthLib.Networking NetworkingProperty

namespace NetworkingProperty.Gossip

/-! ## Topics -/

/-- A topic string: the parts of a valid one, each replaced now and then. -/
def genTopic : Gen String := do
  let lead ← Gen.frequency [(8, pure "/eth2/"), (1, Gen.element ["/eth3/", "eth2/", "/ETH2/", ""])]
  let digest ← Gen.frequency [
    (6, Gen.string (.singleton 8) (Gen.element "0123456789abcdef".toList)),
    (1, Gen.string (.linear 0 9) (Gen.element "0123456789abcdef".toList)),
    (2, Gen.string (.singleton 8) (Gen.element "0123456789abcdefABCDEFg/ x".toList))]
  let name ← Gen.frequency [
    (4, Gen.element ["beacon_block", "beacon_attestation_3", "", "voluntary_exit"]),
    (2, Gen.string (.linear 0 6) (Gen.element "ab_/1é\n".toList))]
  let tail ← Gen.frequency [(8, pure "/ssz_snappy"),
    (1, Gen.element ["/ssz", "/ssz_snappy/", "ssz_snappy", "/SSZ_SNAPPY", ""])]
  pure (lead ++ digest ++ "/" ++ name ++ tail)

/-- A topic string is read as `/eth2/<8 lowercase hex digits>/<name>/ssz_snappy`, and written. -/
def topics (oracle : Oracle) : Property IO := propertyM do
  let text ← forAll genTopic
  pure do
    let want ← oracle.ask ["topic", hex text.toUTF8]
    match Gossip.parseTopic text with
    | .ok (digest, name) =>
      s!"{hexv digest} {hex name.toUTF8}" === want
      Gossip.topicString digest name === text
    | .error _ => ensure (want.startsWith "error") s!"EthLib refuses, the reference reads {want}"

/-- A subnet number in text: decimal digits, with the forms that are not canonical. -/
def genSubnetText : Gen String :=
  Gen.frequency [
    (4, toString <$> genNatBits 64),
    (1, Gen.element ["18446744073709551615", "18446744073709551616", "0", "00", "01", "", "-1",
      "+1", "1 ", " 1", "1_", "٣", "99999999999999999999999"]),
    (2, Gen.string (.linear 0 4) (Gen.element "0123456789a_".toList))]

/-- The name of a subnet topic is `base_N`, with `N` in canonical decimal below 2^64. -/
def subnetNames (oracle : Oracle) : Property IO := propertyM do
  let base ← forAll (Gen.element ["beacon_attestation", "sync_committee",
    "data_column_sidecar", ""])
  let sep ← forAll (Gen.frequency [(8, pure "_"), (1, Gen.element ["", "__", "-"])])
  let number ← forAll genSubnetText
  pure do
    let name := base ++ sep ++ number
    let want ← oracle.ask ["subnet_name", hex base.toUTF8, hex name.toUTF8]
    match Gossip.parseSubnetTopicName base name with
    | some id =>
      toString id.toNat === want
      Gossip.subnetTopicName base id === name
    | none => ensure (want.startsWith "error") s!"EthLib refuses, the reference reads {want}"

/-! ## Message IDs -/

/-- Data of a gossip message: a Snappy block that cramjam and the format read alike, or not one. -/
def genData : Gen ByteArray :=
  Gen.frequency [
    (4, Snappy.Block.bytes <$> Snappy.genBlock.filter Snappy.Block.snapReads),
    (1, genBytes (.linear 0 20))]

/-- The message ID is the specification's, with cramjam deciding what decompresses. -/
def messageIds (oracle : Oracle) : Property IO := propertyM do
  let fork ← forAll (Gen.element [Base.Fork.phase0, .altair, .bellatrix, .fusaka])
  let topic ← forAll (Gen.frequency [(3, genTopic), (1, pure "")])
  let data ← forAll genData
  pure do
    hexv (Gossip.messageId fork topic.toUTF8 data) ===
      (← oracle.ask ["message_id", if fork == .phase0 then "0" else "1", hex topic.toUTF8,
        hex data])

/-- A block with a padded preamble of six bytes gets another ID than the one cramjam gives. -/
def messageIdPreamble (oracle : Oracle) : Property IO := propertyM do
  pure do
    let data : ByteArray := ⟨#[0x80, 0x80, 0x80, 0x80, 0x80, 0x00]⟩
    hexv (Gossip.messageId .altair "t".toUTF8 data) ===
      (← oracle.ask ["message_id", "1", hex "t".toUTF8, hex data])

/-! ## Subnets -/

/-- The stand-in shuffle of both sides: a rotation by the first eight bytes of the seed. -/
def rotate (index count : UInt64) (seed : Base.Bytes32) : Except Unit UInt64 :=
  let shift := Base.bytesToNat (seed.toList.take 8).reverse
  .ok (UInt64.ofNat ((index.toNat + shift) % count.toNat))

/-- The subnets of a node are those of `compute_subscribed_subnets`, for any parameters. -/
def subnets (oracle : Oracle) : Property IO := propertyM do
  let node ← forAll (genNatBits 256)
  let epoch ← forAll (Gen.frequency [(4, UInt64.ofNat <$> genNatBits 40), (1, genUInt64)])
  let per ← forAll (Gen.element [(1 : UInt64), 2, 3, 255, 256, 257])
  let count ← forAll (Gen.element [(1 : UInt64), 2, 3, 4, 63, 64, 65, 128])
  let extra ← forAll (Gen.nat (.constant 0 6))
  let n ← forAll (Gen.nat (.constant 0 3))
  pure do
    let config : Gossip.SubnetParameters := ⟨per, UInt64.ofNat n, count, UInt64.ofNat extra⟩
    let got := Gossip.computeSubscribedSubnets config rotate (BitVec.ofNat 256 node) epoch
    let want ← oracle.ask ["subnets", toString node, toString epoch.toNat, toString per.toNat,
      toString count.toNat, toString extra, toString n]
    match got with
    | .ok ids =>
      (if ids.isEmpty then "-" else ",".intercalate (ids.map (toString ·.toNat))) === want
    -- The epoch plus the offset of the node does not fit 64 bits.
    | .error _ => ensure (n > 0 && epoch.toNat + node % per.toNat ≥ 2 ^ 64) s!"refused: {want}"

/-! ## Payloads -/

/-- A length prefix: the right one, one beside it, or one that is not minimal. -/
def genPrefix (size : Nat) : Gen (List UInt8) :=
  Gen.frequency [
    (8, pure (Snappy.preamble 0 size)),
    (1, (fun (d : Int) => Snappy.preamble 0 ((size : Int) + d).toNat) <$>
      Gen.int (.constant (-1) 1)),
    (1, pure (Snappy.preamble (2 + size / 128) size)),
    (1, Gen.element [[0x80], [], [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01]])]

/-- A payload of a request or a response reads as the consensus layer says, or is refused. -/
def reqResp (oracle : Oracle) : Property IO := propertyM do
  let chunks ← forAll (Snappy.genStream.filter fun cs => cs.all fun
    | .packed block _ => block.preambleWidth ≤ 5
    | _ => true)
  let stream := Snappy.streamBytes chunks
  let size := ((Networking.Snappy.decodeFrames stream).toOption.map (·.size)).getD 0
  let header ← forAll (genPrefix size)
  let (low, high) ← forAll (Gen.zip
    (Gen.frequency [(4, pure 0), (1, (size + ·) <$> Gen.nat (.constant 0 1))])
    (Gen.frequency [(4, pure (2 ^ 40)), (1, (size + 1 - ·) <$> Gen.nat (.constant 0 2))]))
  pure do
    let bytes := (⟨header.toArray⟩ : ByteArray) ++ stream
    annotate s!"payload: {hex bytes}"
    answer (ReqResp.decodePayload (UInt64.ofNat low) (UInt64.ofNat high) bytes) ===
      verdict (← oracle.ask ["reqresp_payload", toString low, toString high, hex bytes])

/-- What EthLib encodes, the reference reads back; the literal form too. -/
def reqRespEncode (oracle : Oracle) : Property IO := propertyM do
  let data ← forAllWith hex Snappy.genCompressible
  pure do
    for bytes in [ReqResp.encodePayload data, ReqResp.encodePayloadLiteral data] do
      (← oracle.ask ["reqresp_payload", "0", "1000000", hex bytes]) === hex data

/-- A payload of no bytes with no stream after its length: the reference's own encoder writes it. -/
def reqRespEmpty (oracle : Oracle) : Property IO := propertyM do
  pure do
    let stream ← oracle.ask ["snappy_frame_enc", "-"]
    annotate s!"cramjam frames no data as: {stream}"
    answer (ReqResp.decodePayload 0 100 ⟨#[0]⟩) === "-"

/-- The data of a gossip message is within its bounds, decompressed, or refused. -/
def gossipPayload (oracle : Oracle) : Property IO := propertyM do
  let block ← forAll (Snappy.genBlock.filter (·.preambleWidth ≤ 5))
  let bound ← forAll (Gen.frequency [(3, pure (2 ^ 30)), (2, Gen.nat (.linear 0 200))])
  pure do
    let data := block.bytes
    let want ← oracle.ask ["snappy_model_dec", hex data]
    let wanted := match unhex? want with
      | some out => if want.startsWith "error" || out.size > bound then "error" else want
      | none => "error"
    answer (Gossip.decodePayload (UInt64.ofNat bound) data) === wanted

/-! ## Fork identifiers -/

/-- A chain: fork blocks, fork times, and the time of genesis. -/
structure Chain where
  blocks : List Nat
  times : List Nat
  genesisTime : Nat
  genesis : Vector UInt8 32
  deriving Repr

/-- The forks to hang activations on; which fork an activation belongs to changes nothing. -/
def someForks : List Base.Fork :=
  [.homestead, .daoFork, .tangerineWhistle, .spuriousDragon, .byzantium, .constantinople,
    .petersburg, .istanbul, .berlin, .london, .shapella, .dencun, .pectra, .fusaka]

/-- The schedule of a chain. -/
def Chain.schedule (c : Chain) : Devp2p.Schedule where
  genesisHash := c.genesis
  genesisTime := c.genesisTime
  config := { Base.ChainConfig.mainnet with
    activations := (someForks.zip (c.blocks.map .block ++ c.times.map .time)) }
  mergeForkBlock := none

/-- A chain with a few forks: some at genesis, some twice, blocks and times apart as on mainnet. -/
def genChain : Gen Chain := do
  let genesisTime ← Gen.element [0, 1500000000]
  let blocks ← Gen.list (.linear 0 5) (Gen.frequency [(6, Gen.nat (.constant 1 40)), (1, pure 0)])
  let times ← Gen.list (.linear 0 4) (Gen.frequency [
    (6, (1500000000 + ·) <$> Gen.nat (.constant 1 40)), (1, pure genesisTime),
    (1, pure 1500000000)])
  pure ⟨blocks, times, genesisTime, ← genVector 32⟩

/-- A head: a block number among the fork blocks and a timestamp among the fork times. -/
def genHead : Gen (Nat × Nat) :=
  Gen.zip (Gen.nat (.constant 0 45)) ((1500000000 + ·) <$> Gen.nat (.constant 0 45))

/-- The words that name a chain to the oracle. -/
def Chain.words (c : Chain) : List String :=
  [hexv c.genesis, ",".intercalate (c.blocks.map toString) ++ ",",
    ",".intercalate (c.times.map toString) ++ ",", toString c.genesisTime]

/-- The fork identifier of a head is the one of EIP-2124 and EIP-6122, over the CRC-32 of zlib. -/
def forkId (oracle : Oracle) : Property IO := propertyM do
  let chain ← forAll genChain
  let (number, time) ← forAll genHead
  pure do
    let id := chain.schedule.forkId number time
    s!"{hexv id.hash} {id.next.toNat}" ===
      (← oracle.ask (["forkid"] ++ chain.words ++ [toString number, toString time]))

/-- Mainnet's identifier at a head is the one of the EIPs' tables. -/
def forkIdMainnet (oracle : Oracle) : Property IO := propertyM do
  let number ← forAll (Gen.frequency [
    (3, Gen.element [0, 1149999, 1150000, 1919999, 1920000, 2463000, 2675000, 4370000, 7280000,
      9069000, 9200000, 12244000, 12965000, 13773000, 15050000, 15537394, 20000000]),
    (1, Gen.nat (.constant 0 16000000))])
  let time ← forAll (Gen.frequency [
    (3, Gen.element [0, 1681338454, 1681338455, 1710338135, 1746612311, 1764798551, 1765290071,
      1767747671, 1800000000]),
    (1, Gen.nat (.constant 1681000000 1770000000))])
  pure do
    let id := Devp2p.Schedule.mainnet.forkId number time
    s!"{hexv id.hash} {id.next.toNat}" ===
      (← oracle.ask ["forkid_mainnet", toString number, toString time])

/-- A remote identifier: that of a head of this chain or of a chain near it, its next changed. -/
def genRemote (chain : Chain) : Gen Devp2p.ForkId := do
  let other ← Gen.frequency [
    (4, pure chain),
    (1, (fun n => { chain with blocks := chain.blocks.take n }) <$> Gen.nat (.constant 0 4)),
    (1, (fun n => { chain with times := chain.times.take n }) <$> Gen.nat (.constant 0 4)),
    (1, (fun b => { chain with blocks := b :: chain.blocks }) <$> Gen.nat (.constant 1 40))]
  let (number, time) ← genHead
  let id := other.schedule.forkId number time
  let next ← Gen.frequency [(5, pure id.next), (1, pure 0),
    (2, UInt64.ofNat <$> Gen.nat (.constant 0 45)),
    (2, (fun n => UInt64.ofNat (1500000000 + n)) <$> Gen.nat (.constant 0 45))]
  pure ⟨id.hash, next⟩

/-- A remote identifier is accepted or refused as the rules of EIP-2124 say.

The reference applies them as geth does. -/
def forkIdValidate (oracle : Oracle) : Property IO := propertyM do
  let chain ← forAll genChain
  let (number, time) ← forAll genHead
  let remote ← forAll (genRemote chain)
  pure do
    let got := match chain.schedule.validate number time remote with
      | .ok () => "ok"
      | .error .remoteStale => "remote stale"
      | .error .localIncompatibleOrStale => "local stale"
    got === (← oracle.ask (["forkid_validate"] ++ chain.words ++
      [toString number, toString time, hexv remote.hash, toString remote.next.toNat]))

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) := [
  ("gossip: a topic string", (topics oracle).withTests cases),
  ("gossip: the name of a subnet topic", (subnetNames oracle).withTests cases),
  ("gossip: the message ID", (messageIds oracle).withTests cases),
  ("gossip: the subnets of a node", (subnets oracle).withTests cases),
  ("gossip: the data of a message within its bounds", (gossipPayload oracle).withTests cases),
  ("reqresp: a payload reads as the consensus layer says", (reqResp oracle).withTests cases),
  ("reqresp: the reference reads EthLib's payload", (reqRespEncode oracle).withTests cases),
  ("forkid: the identifier of a head", (forkId oracle).withTests cases),
  ("forkid: mainnet's identifiers", (forkIdMainnet oracle).withTests cases),
  ("forkid: the validation of a remote identifier", (forkIdValidate oracle).withTests cases)]

/-- The properties of this module that disagree with a reference: see the findings. -/
def findings (oracle : Oracle) : List (String × Property IO) := [
  ("gossip: the message ID of a block with a padded preamble (OPEN)",
    (messageIdPreamble oracle).withTests 1),
  ("reqresp: an empty payload with no stream (OPEN)", (reqRespEmpty oracle).withTests 1)]

end NetworkingProperty.Gossip
