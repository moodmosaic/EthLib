import Property.Rpc.Wire

/-!
# The Status of eth and its fork identifier

A node accepts the Status of a peer by its version, its fork identifier and its block range.

The fork identifier is that of EIP-2124, with the forks by time of EIP-6122.

The reference is `oracle/rpc_wire.py`: the rules of EIP-2124 written out, with the CRC-32 of zlib.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Execution EthLib.Execution.Network
open EthLib.Networking.Devp2p

namespace RpcProperty

/-- A chain as a node knows it for its fork identifier. -/
structure ForkCase where
  genesis : Hash32
  genesisTime : Nat
  activations : List (Fork × Activation)
  merge : Option Nat
  deriving Repr

/-- The schedule of EthLib for the chain. -/
def ForkCase.schedule (c : ForkCase) : Schedule :=
  ⟨c.genesis, c.genesisTime, ⟨1, addressOf 0xde 0x90, c.activations, []⟩, c.merge⟩

/-- The words of the chain in a command of the oracle. -/
def ForkCase.words (c : ForkCase) : List String :=
  [hexVec c.genesis, toString c.genesisTime,
   joined "," (c.activations.map fun (fork, activation) =>
     match activation with
     | .block n => if fork = .paris then s!"p{n}" else s!"b{n}"
     | .time t => s!"t{t}"),
   (c.merge.map toString).getD "-"]

/-- A chain: forks by block at small numbers, some twice or at 0, then forks by time. -/
def genForkCase : Gen ForkCase := do
  let genesis ← Vector.ofFn (n := 32) <$> (fun (l : List UInt8) i => l.getD i.val 0) <$>
    Gen.list (.singleton 32) genByte
  let genesisTime ← Gen.element [0, 1500000000, 1500000500]
  let byBlock := [Fork.frontier, .homestead, .byzantium, .berlin, .london, .paris]
  let byTime := [Fork.shapella, .dencun, .pectra, .fusaka]
  let blocks ← Gen.list (.singleton byBlock.length) (Gen.element [0, 0, 5, 10, 10, 20])
  let times ← Gen.list (.singleton byTime.length)
    (Gen.element [1500000000, 1500000500, 1500001000, 1500002000, 1500002000, 1500003000])
  let kept ← Gen.nat (.constant 1 (byBlock.length + byTime.length))
  let activations := ((byBlock.zip ((blocks.mergeSort (· ≤ ·)).map Activation.block)) ++
    (byTime.zip ((times.mergeSort (· ≤ ·)).map Activation.time))).take kept
  let merge ← Gen.frequency [(2, pure none), (1, some <$> Gen.element [0, 7, 10, 25])]
  pure ⟨genesis, genesisTime, activations, merge⟩

/-- A head of the chain: a block number and a timestamp around its forks. -/
def genHead (c : ForkCase) : Gen (Nat × Nat) :=
  Gen.zip (Gen.element [0, 4, 5, 9, 10, 19, 20, 24, 25, 30])
    ((c.genesisTime + ·) <$> Gen.element [0, 499, 500, 999, 1000, 1999, 2000, 2999, 3000, 4000])

/-- The fork identifier of a head is the one of EIP-2124. -/
def forkIdOfHead (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genForkCase
  let (number, time) ← forAll (genHead c)
  pure do
    let want ← oracle.ask (["forkid"] ++ c.words ++ [toString number, toString time])
    let got := c.schedule.forkId number time
    s!"{hexVec got.hash},{got.next.toNat}" === want
    let forks := c.schedule.forks.length
    classify "a chain with a fork by block and a fork by time"
      (!c.schedule.blocks.isEmpty ∧ !c.schedule.times.isEmpty)
    classify "the head has passed a fork and not all" (0 < (c.schedule.passed number time).length ∧
      (c.schedule.passed number time).length < forks)
    classify "the head has passed every fork" (got.next = 0)

/-- A node accepts the Status of a peer exactly when the rules allow it.

The version must be the negotiated one, and from eth/69 the range must not start after its end.

The fork identifier must pass the rules of EIP-2124, which the reference applies. -/
def statusCheck (oracle : Oracle) : Property IO := propertyM do
  let c ← forAll genForkCase
  let (number, time) ← forAll (genHead c)
  let (remoteNumber, remoteTime) ← forAll (genHead c)
  let (versionNumber, version) ← forAll (Gen.element ethVersions)
  let announced ← forAll (Gen.frequency [(8, pure versionNumber),
    (1, Gen.element [67, 68, 69, 73])])
  let (earliest, latest) ← forAll (Gen.frequency [(6, Gen.element [(0, 0), (0, 10), (5, 5)]),
    (1, Gen.element [(1, 0), (10, 9)])])
  -- The identifier of a peer at its own head, mostly, and sometimes with one part changed.
  let honest := c.schedule.forkId remoteNumber remoteTime
  let other ← forAll (Gen.element [0, 5, 10, 20, 1500001000, 1500002000, 1500009999])
  let remote ← forAllWith (fun (id : ForkId) => s!"{hexVec id.hash},{id.next.toNat}")
    (Gen.frequency [(6, pure honest), (2, pure { honest with next := other.toUInt64 }),
      (1, pure { honest with hash := Vector.replicate 4 0x5a })])
  pure do
    let status : Network.Status := if version = .eth68 then
        .eth68 announced 1 0 c.genesis c.genesis remote
      else .eth69 announced 1 c.genesis remote ⟨earliest, latest, c.genesis⟩
    let rule ← oracle.ask (["validate"] ++ c.words ++ [toString number, toString time,
      hexVec remote.hash, toString remote.next.toNat])
    annotate s!"the reference: {rule}"
    let faults : List String := (if announced ≠ versionNumber then ["version"] else []) ++
      (if rule ≠ "ok" then [rule] else []) ++
      (if version ≠ .eth68 ∧ earliest > latest then ["range"] else [])
    let got := checkStatus version c.schedule number time status
    annotate s!"EthLib: {reprStr got}"
    match got with
    | .ok _ =>
      faults === []
      cover 30 "a Status is accepted" true
      classify "a peer on an earlier fork is accepted" (remoteNumber < number ∧
        honest.hash ≠ (c.schedule.forkId number time).hash)
      classify "a peer on a later fork is accepted" (remoteNumber > number ∧
        honest.hash ≠ (c.schedule.forkId number time).hash)
    | .error e =>
      let mine := match e with
        | .version _ => "version"
        | .forkId .remoteStale => "stale"
        | .forkId .localIncompatibleOrStale => "incompatible"
        | .range .. => "range"
      ensure (faults.contains mine) s!"EthLib refuses for {mine}, the rules for {faults}"
      classify s!"refused: {mine}" true

end RpcProperty
