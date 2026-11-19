# Networking: findings of the property tests

The driver is `Property/Networking.lean`, with its modules under `Property/Networking/`.
The references are `oracle/networking.py` and the `oracle/networking_*.py` it loads.
Their packages are in `oracle/requirements-networking.txt`.

```bash
cd tests/property
lake build networking-property
lake exe networking-property 1000
```

The last run was at 1,000 cases: 58 properties passed, 41,091 cases in all, in about 35 seconds.
Four properties of the group `networking: findings` fail by design, and their reports are the evidence below.
No property found a place where EthLib computes something other than its cited source.
Two inputs are refused by EthLib and read by the Rust `snap` crate; both are OPEN.

## What was tested

| Property | EthLib definitions | Reference | Cases | Result |
| --- | --- | --- | --- | --- |
| snappy: a block decompresses as the format says | `Snappy.decompress` | decoder written from `format_description.txt` | 1000 | pass |
| snappy: a block decompresses as cramjam's | `Snappy.decompress` | cramjam 2.14.0 (Rust `snap`) | 1000 | pass |
| snappy: any bytes decompress as the format says | `Snappy.decompress` | the same decoder | 1000 | pass |
| snappy: cramjam reads EthLib's block | `Snappy.compress`, `emitCopies`, `emitLiteral` | cramjam | 1000 | pass |
| snappy: EthLib reads cramjam's block | `Snappy.decompress` | cramjam | 1000 | pass |
| snappy: a block stays within 32 + n + n / 6 | `Snappy.compress` | the bound of `snappy.cc` | 1000 | pass |
| snappy: the masked CRC-32C | `Snappy.maskedCrc` | `crc32c` and `framing_format.txt` §3 | 1000 | pass |
| snappy: a stream decodes as the format says | `Snappy.decodeFrames` | decoder written from `framing_format.txt` | 1000 | pass |
| snappy: a stream decodes as cramjam's | `Snappy.decodeFrames` | cramjam | 1000 | pass |
| snappy: the chunk limit of 65536 bytes | `Snappy.decodeFrames`, `maxChunkLength` | the same decoder | 30 | pass |
| snappy: cramjam reads EthLib's stream | `Snappy.encodeFrames`, `encodeFramesLiteral` | cramjam | 1000 | pass |
| snappy: EthLib reads cramjam's stream | `Snappy.decodeFrames` | cramjam | 1000 | pass |
| varint: the consensus varint decodes | `Encoding.Varint.decode` | reader written from the consensus rules | 1000 | pass |
| varint: the consensus varint encodes | `Encoding.Varint.encode` | the same reader | 1000 | pass |
| varint: the unsigned varint of libp2p | `Encoding.Uvarint.decode` | reader written from the multiformats text | 1000 | pass |
| quic: an integer decodes as aioquic's | `Quic.Varint.decode` | aioquic 1.8.0 | 1000 | pass |
| quic: an integer encodes as aioquic's | `Quic.Varint.encode`, `encodeWith` | aioquic | 1000 | pass |
| quic: a packet number, RFC 9000 A.3 | `Quic.Packet.decodePacketNumber` | the pseudocode of A.3, and aioquic | 1000 | pass |
| quic: Initial secrets and packet keys | `Quic.initialSecrets`, `packetKeys` | aioquic | 300 | pass |
| quic: packet protection is aioquic's | `Quic.Protection.protect`, `unprotect`, `Quic.Packet.encode` | aioquic | 300 | pass |
| enr: a signed record is the reference's | `Enr.makeRecordV4`, `signV4`, `Enr.encode` | EIP-778 with `rlp` and libsecp256k1 | 300 | pass |
| enr: a record with a rule broken | `Enr.decode`, `verifyV4`, `nodeId` | the same | 300 | pass |
| enr: the limit of 300 bytes | `Enr.decode`, `makeRecordV4` | the same | 30 | pass |
| enr: the text form | `Enr.toText`, `fromText` | round trip, and the rules of the EIP | 100 | pass |
| discv4: a packet is the reference's | `Discv4.encode` | `discv4.md` with libsecp256k1 | 300 | pass |
| discv4: a packet with tweaked data | `Discv4.decode` | `discv4.md`, EIP-8, EIP-868 | 300 | pass |
| discv4: a changed signature | `Discv4.decode`, `Rlpx.recoverSigner` | libsecp256k1 | 300 | pass |
| discv5: the logarithmic distance | `Discv5.logDistance` | bit length of the XOR | 1000 | pass |
| discv5: a packet is masked as the specification says | `Discv5.Packet.encode` | `discv5-wire.md`, AES by `cryptography` | 1000 | pass |
| discv5: a packet with header fields that may not fit | `Discv5.Packet.decode` | the same | 1000 | pass |
| discv5: the sizes 63 and 1280 | `Discv5.Packet.decode` | the same | 30 | pass |
| discv5: the handshake packet and its keys | `initiateHandshake`, `sealHandshake`, `openHandshake`, `deriveKeys`, `idSign`, `ecdh` | the same, with HKDF and libsecp256k1 | 200 | pass |
| discv5: a changed ID signature | `Discv5.idVerify` | libsecp256k1 | 200 | pass |
| discv5: a message with one thing changed | `Discv5.Message.decode`, `encode` | `discv5-wire.md` with `rlp` | 1000 | pass |
| rlpx: ECIES | `Rlpx.Ecies.encrypt`, `decrypt` | `rlpx.md` with `cryptography` and libsecp256k1 | 200 | pass |
| rlpx: the reference reads auth | `Rlpx.makeAuth`, `readAuth` | the same | 200 | pass |
| rlpx: the frames of one side | `Rlpx.deriveSecrets`, `writeFrame` | `rlpx.md`, "Framing" and "MAC" | 1000 | pass |
| gossip: a topic string | `Gossip.parseTopic`, `topicString` | a pattern from the networking specification | 1000 | pass |
| gossip: the name of a subnet topic | `Gossip.parseSubnetTopicName`, `subnetTopicName` | a pattern | 1000 | pass |
| gossip: the message ID | `Gossip.messageId` | `hashlib`, with cramjam deciding validity | 1000 | pass |
| gossip: the subnets of a node | `Gossip.computeSubscribedSubnets` | `compute_subscribed_subnets`, transcribed | 1000 | pass |
| gossip: the data of a message within its bounds | `Gossip.decodePayload` | the Snappy decoder and the bound | 1000 | pass |
| reqresp: a payload reads as the consensus layer says | `ReqResp.decodePayload`, `Snappy.readFrames` | reader written from the specification | 1000 | pass |
| reqresp: the reference reads EthLib's payload | `ReqResp.encodePayload`, `encodePayloadLiteral` | the same reader | 1000 | pass |
| forkid: the identifier of a head | `Devp2p.Schedule.forkId` | EIP-2124 and EIP-6122 over `zlib.crc32` | 1000 | pass |
| forkid: mainnet's identifiers | `Devp2p.Schedule.mainnet`, `ChainConfig.mainnet` | the tables of the EIPs | 1000 | pass |
| forkid: the validation of a remote identifier | `Devp2p.Schedule.validate` | the rules of EIP-2124, as geth's filter | 1000 | pass |
| libp2p: a signature is libsecp256k1's | `Libp2p.sign`, `encodeSignature` | coincurve 21.0.0 | 200 | pass |
| libp2p: a changed signature or key | `Libp2p.verify`, `decodeSignature`, `decodePublicKey` | coincurve (strict DER, low s) | 200 | pass |
| libp2p: the peer ID of a key | `Libp2p.peerId`, `decodePeerId` | the bytes of the peer ID specification | 100 | pass |
| noise: the XX handshake is noiseprotocol's | `Noise.writeMessage`, `readMessage`, `transport`, `encryptWithAd` | noiseprotocol 0.3.1 | 200 | pass |
| yamux: two ends of a connection against a model (`StateMachine`) | `Yamux.send`, `receive`, `step`, `Stream.apply` | a model of the connection from the yamux specification | 1000 sequences of up to 80 frames | pass |
| mplex: two ends of a connection against a model (`StateMachine`) | `Mplex.send`, `receive`, `step` | a model from the mplex specification | 1000 sequences of up to 60 frames | pass |
| rlpx: frames of a session, both directions (`StateMachine`) | `Rlpx.writeFrame`, `readFrame`, `Secrets.egress`, `ingress` | what was written is read, a changed frame is refused | 300 sequences of up to 20 frames | pass |
| gossipsub: the router, scripted (`Command`, deterministic) | `receiveRpc`, `join`, `leave`, `publish`, `heartbeat` | a model from gossipsub v1.0 and v1.1 | 1 | pass |
| gossipsub: the router, random commands (`Command`, madhouse) | the same | the same | 1000 sequences of up to 15 commands | pass |
| gossipsub: the router, long sequences (`Command`, madhouse) | the same | the same | 1000 sequences of 30 scripted and up to 120 random commands | pass |
| gossipsub: the router with flood publishing (`Command`, madhouse) | the same, `floodPublish` | the same | 1000 sequences as above | pass |

The discv5 reference reproduces the vectors of `discv5-wire-test-vectors.md` when it starts: the key derivation, the ID signature and the WHOAREYOU packet.
The fork identifier reference reproduces the seventeen mainnet rows of EIP-2124 and EIP-6122 that it holds.
The QUIC reference gives the client Initial secret of RFC 9001 Appendix A.1.

### The two state machine styles

`StateMachine` is used where a specification fixes the transitions: the frames of yamux, of mplex, and of an RLPx session.
A yamux or mplex connection has two ends, and EthLib keeps the table of one end.
So the system under test is two tables, each frame is sent by one and received by the other, and the model is one table of the connection that knows nothing of ends.
After every frame, each end must hold exactly its view of the model: opener, ACK, FIN and RST of each side, and both windows.
A frame that its sender may send must be taken by its receiver, and one that it may not send must be refused, except for the frames that cross a reset, which SOUNDNESS.md documents.

`Command` is used for the gossipsub router, where each event is a type with its own instance: `Tick`, `Subscribe`, `Receive`, `Graft`, `Prune`, `IHave`, `IWant`, `Join`, `Leave`, `Publish`, `Heartbeat`.
The state holds EthLib's `RouterState` and a model beside it: the seen cache with times, the message cache with ages, every backoff, the subscriptions and the fanout.
Each command checks what gossipsub asks of the answer, and then the invariants: no explicit peer in a mesh, no peer in a mesh within its backoff, no peer twice, backoffs equal to the model's, the caches answering as the model, the gossip windows, the fanout.
Where the router may choose, the commands check the bounds and that it could not take more: the mesh after a heartbeat, the outbound quota, the best peer kept, the fanout top-up, the count of gossip targets.
The scores are fixed per peer, so every threshold is crossed: negative, below gossip, below publish, graylisted, and two explicit peers.

## Findings

### 1. A Snappy preamble of six bytes is refused (OPEN)

Definition: `preambleMaxLength` and `readPreambleAux`, `EthLib/Networking/Snappy/Block.lean:53` and `:121`.

Counterexample: the block `80 80 80 80 80 00`.

EthLib: `Snappy.decompress` gives `preambleTooLong`.

Reference: cramjam 2.14.0, which is the Rust `snap` crate, reads it as the empty output.

Source: `format_description.txt` §1 says "The stream starts with the uncompressed length (up to a maximum of 2^32 - 1), stored as a little-endian varint."
It sets no minimal form and no byte count.
EthLib's own docstring says "The format sets no minimality rule. So `80 00` is a valid preamble for the length zero."
By that reading the six-byte form is a valid preamble too, and EthLib refuses it.
The C++ reference (`Varint::Parse32WithLimit`) reads at most five bytes, as EthLib does, so the two implementations of the format disagree with each other.
Go's `snappy.DecodedLen` reads the length with `binary.Uvarint`, as `snap` does; I did not run it.

Consequence: `Gossip.messageId` hashes such data under `MESSAGE_DOMAIN_INVALID_SNAPPY`, and a client on `snap` under `MESSAGE_DOMAIN_VALID_SNAPPY`.
The property `gossip: the message ID of a block with a padded preamble` shows the two IDs: `e903f0fd…` for EthLib and `cea86030…` for the reference.

What would decide it: whether "valid snappy" in the consensus networking specification means the C++ reference or the format text.
If the text, the reader should accept up to ten bytes and then check the range.

Command: `lake exe networking-property 100 2>&1 | grep -A8 'preamble'`.

### 2. A framed stream of no chunks is refused (OPEN)

Definition: `decodeFramesList` and `readFrames`, `EthLib/Networking/Snappy/Frame.lean:191` and `:230`; `ReqResp.decodePayload`, `EthLib/Networking/ReqResp/Encoding.lean:164`.

Counterexample: the empty stream, and the payload `00` (a length of zero with nothing after it).

EthLib: `Snappy.decodeFrames ""` gives `missingStreamIdentifier none`, and `ReqResp.decodePayload 0 100 "00"` gives the same error.

Reference: cramjam frames no data as no bytes, and reads no bytes as no data.

Source: `framing_format.txt` §4.1 says "The stream identifier is always the first element in the stream."
It does not say that a stream has an element.
The consensus specification asks only that the payload hold the declared number of SSZ bytes.
EthLib's `readFrames` documents its choice: "The stream starts with the stream identifier, which the reader reads even when `n` is 0."

Consequence: an encoder that writes the stream identifier with the first data, as `snap` does, sends an empty payload that EthLib refuses.
An empty payload is the SSZ of an empty list, such as a request for zero roots.

What would decide it: what the clients send for an empty payload; I did not capture one.

Command: `lake exe networking-property 100 2>&1 | grep -A8 'no chunks\|no stream'`.

### Documented choices that differ from implementations I know

These are not findings of a property; the router commands check EthLib's documented reading.
Both are stated in the module docstring of `Gossip/Router.lean`.

- "A GRAFT declined under the outbound quota gets no answer."
  Gossipsub v1.1 says the router "only accepts the new peer in the mesh if it is an outbound connection" and names no answer.
  go-libp2p-pubsub answers with a PRUNE; without one the peer keeps this node in its mesh.
- "A message goes to every peer in the mesh, the peer that sent it included, as v1.0 says."
  v1.0 says "it will forward the message to every peer in its local gossipsub topic mesh", and earlier, of flooding, that a router "never forwards a message back to the source".

### Harness mistakes, one line each

- cramjam refuses a literal whose length takes one to four bytes when fewer than four bytes follow its tag (`01 f0 00 00`); the C++ reference and the format accept it, so the cramjam property leaves such blocks out.
- The smallest discv5 packet is a WHOAREYOU packet, not a message packet; the size property built the wrong one.
- The heartbeat may add `D_out` outbound peers after it fills a mesh to `D`; the command first asked for exactly `D`.
- A yamux or mplex frame that crosses a reset is taken and dropped by the end that reset, as SOUNDNESS.md says; the machines first called that a disagreement.
- Installing `eth-enr` downgraded `rlp`, `eth-keys`, `eth-utils`, `eth-typing`, `cytoolz` and `pycryptodome` in the shared `.venv`; I removed it at once and restored the listed versions (`typing_extensions` went from 4.15.0 to 4.16.0).

## Not covered

- `Quic/Frame.lean` and the decoder of `Quic/Packet.lean`: only `Packet.encode` runs, inside the protection property; aioquic's `pull_quic_header` and frame readers are the reference to use next.
- `Quic/Tls/*` and `Libp2p/Tls.lean` (about 2,000 lines): no property; they need a TLS 1.3 reference driven message by message.
- `Quic.Protection.retryTag` and the reserved-bit and length checks of `unprotect` beyond one changed byte.
- `Gossip/Rpc.lean` and `Encoding/Protobuf.lean`: no property; the `protobuf` package with the pubsub schema is the reference to use.
- `Enr/Consensus.lean` (`eth2`, `attnets`, `syncnets`, `cgc`, `nfd`) and `Enr/Eth.lean`.
- `Devp2p/P2p.lean` and `Devp2p/Session.lean`: Hello, Disconnect, capability offsets and the session phases; a `StateMachine` fits the session.
- `Libp2p/Multistream.lean` and `Upgrade.lean`; the byte codecs `Yamux.encode`/`decode` and `Mplex.encode`/`decode` (the machines use frames, not bytes).
- `Noise/Identity.lean` (the libp2p payload and its authentication) and `Noise.frame`/`unframe`; a handshake with a changed message.
- `Rlpx.makeAck`, `readAck`, `respond`, `finish`: only `auth`, ECIES, the secrets and the frames are compared.
- `Discv5.makeWhoareyou`, `readWhoareyou`, `sealMessage`, `openMessage`, and `Discv4.recordSignedBy`.
- Snappy copies with an offset above 65535 that are valid: they need more than 64 KiB of output, and the generator stays small.
- The gossip subnets with the real `compute_shuffled_index`: the property passes a rotation as the shuffle to both sides.
- The router with scores that change over time, peers that disconnect, and IDONTWANT.

## Notes on lean-hedgehog

What worked well.

- A generator of structured, almost valid inputs is short to write with `Gen.frequency`, `Gen.zip` and `Gen.element`, and the shrunk counterexamples were minimal on the first try: `01 f0 00 00` for the cramjam literal quirk, the empty element list for the six-byte preamble, two frames for the yamux reset, three for mplex.
- `Gen.subsequence` gave sorted, unique ENR keys with no filter.
- `propertyM` with `forAll` first and the effect after it made the oracle process easy to use, and shrinking re-ran the oracle without trouble.
- `StateMachine` with a transition generator that reads the model state reached deep states: window limits, reuse of IDs, both ends opening the same mplex ID.
- The `Command` journal ("executed …") made the one router failure readable at a glance.

What was awkward or missing.

- `Command.build` gets the context only, not the state, so a command cannot be generated for the state it will meet; I used a small fixed universe of peers, topics and IDs so that random commands collide.
- `scenario .madhouse` draws 1 to 15 commands and takes no range; for long sequences I called `executeCommands` from my own `propertyM`, which also lets a scripted prefix (`Command.fixed`) come before the random part.
- `scenario` starts from `default` only; a start state that depends on a parameter (flood publishing) again needed `executeCommands`.
- `StateMachine.applySut` and `invariants` see the model state after the transition, not before; a check of "was this frame allowed" had to be derived from the system's own answer.
- A `StateMachine … Id` gives a `Property Id`, and `checkGroup` takes one monad; I found no lift from `Property Id` to `Property IO`, so pure machines are declared in `IO`.
- `tripping` needs `BEq` and `Repr` of the decoder's result, and `Except ε α` has no `BEq` in core, so `tripping x encode decode` does not elaborate for a decoder into `Except`; I mapped it to `Option`.
- `forAll` needs `Repr`, and `ByteArray` and functions have none; a `Repr ByteArray` instance in the library, in hexadecimal, would save every driver from writing one.
- A report shows `forAll` values in the order drawn but not their names; with eight draws the reader counts positions.
- A property in a findings group fails by design, and `checkGroup` has no way to say "expected to fail", so the driver ignores the group's result.
- There is no label or coverage count (Haskell's `classify`, `cover`), so I could not see from a passing run how many generated blocks were valid; I trusted the weights.

Bugs in the library: none met.
