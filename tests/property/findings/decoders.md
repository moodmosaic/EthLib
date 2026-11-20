# Decoders: findings of the property tests

The driver is `Property/Decoders.lean`, with its modules under `Property/Decoders/`.
The references are `oracle/decoders.py` and the `oracle/decoders_*.py` it loads.
Their packages are in `oracle/requirements-decoders.txt`; no package was added to the environment.

```bash
cd tests/property
lake build decoders-property
lake exe decoders-property 1000
HEDGEHOG_ONLY="quic:" lake exe decoders-property 5000
```

The scope is the "Not covered" list of `findings/networking.md`: the decoders and codecs that the first round left.
No property found a place where EthLib computes something other than its cited source.
So a bug that remains is not in what these properties reach, or it is in a part listed under "Not covered".
Every refusal and every accepted input is compared with a reference, and the shares of each kind are in the table.

The last run was at 1,000 cases: 79 properties passed, 59,213 cases in all, in about 100 seconds.
The default run of 100 cases passed eight times in a row after the minimums of `cover` were set.
The findings group of this driver is empty.

## What was tested

Cases are those of `lake exe decoders-property 1000`.
"Three-way" means that the bytes are built field by field with the text a reader must give, and that EthLib, the reference and that text agree.

### Protobuf and the gossipsub RPC

| Property | EthLib definitions | Parameters varied | Reference | Cases | Label shares | Result |
| --- | --- | --- | --- | --- | --- | --- |
| protobuf: the records of a message | `Protobuf.records`, `readRecord`, `readKey`, `readVarint`, `readLen`, `readFixed`, `skipGroup` | wire types 0 to 7, field numbers 0 to `2^66` with the edges of each key length, varints padded to 10 and 11 bytes and past 64 bits, groups nested to depth 2 with a wrong or missing end, lengths past the input, one byte changed | a reader written from the encoding guide; the unknown fields that `protobuf` 7.36.2 (upb) keeps of the same bytes | 1000 | valid as generated 36%, changed and still accepted 49%, refused 16%; group 25%, nested group 7%, each refusal rule 0.5% to 3% | pass |
| protobuf: the references read what the writer writes | `Protobuf.serialize`, `encodeRecord`, `encodeKey`, `encodeValue`, `records` | every value kind, field numbers to `2^29 - 1` | the same two | 1000 | a group 28%, a key of five bytes 15% | pass |
| rpc: an RPC decodes as the schema says | `Gossip.decodeRpc`, `decodeSubOpts`, `decodeMessage`, `decodeControl`, `decodeIHave`, `decodeIWant`, `decodeGraft`, `decodePrune`, `decodePeerInfo`, `decodeIDontWant`, `decodeControlExtensions`, `decodePartial`, `Control.merge` | every message of the schema; fields missing, twice, out of order, unknown (the experimental 6492434 and 6492435 too), of another wire type, forbidden, not UTF-8; flags above 1; one byte changed | a model of the libp2p schema with EthLib's documented choices; `protobuf` with the schema built from descriptors at run time, where no documented choice applies | 1000 | valid 36%, changed and accepted 34%, refused 30%, compared with the package 88% | pass |
| rpc: the rules that EthLib documents | the same | the signed fields 1, 3, 5, 6 at wire types 0, 1, 2, 3, 5 and at three positions; a missing topic; two topics; a bad string in each string field, last or earlier; extensions twice in one control field and in two; partial twice; nine named fields with another wire type | the same model | 1000 | signed 13%, not UTF-8 36%, extensions twice 12%, partial twice 5%, control twice 10%, no topic 6%, another wire type 6% | pass |
| rpc: the package reads and writes EthLib's bytes | `Rpc.encode` and every `encode` under it, `decodeRpc` | every part of an RPC, topics of one to four bytes a character | `protobuf`: it parses to the same RPC and serializes to the same bytes; EthLib reads its bytes back | 1000 | extensions 73%, partial 92%, prune with peers 20%, no control field 25% | pass |
| rpc: the flags of a subscription | `SubOpts.asksPartial`, `sendsPartial` | all eight flag triples | the partial messages text | 1000 | | pass |
| rpc: the extensions message in the first RPC alone | `checkExtensionsOrder` | streams of 0 to 5 RPCs | gossipsub v1.3: "MUST be included in the first message", "MUST NOT be sent more than once" | 1000 | first alone 17%, none 33%, a later one 51% | pass |

### QUIC

| Property | EthLib definitions | Parameters varied | Reference | Cases | Label shares | Result |
| --- | --- | --- | --- | --- | --- | --- |
| quic: a frame of each type, RFC 9000 section 19 | `Frame.decode`, `decodeBody`, `ack`, `ranges`, `validate`, `Frame.Valid`, `ackRangesValid`, `Frame.allowed`, `Frame.encode`, `encodeBodyList`, `Frame.type` | all 31 type bytes in the four packets; every integer at its shortest and at longer forms; ACK ranges that end exactly at zero and one below; offsets that end exactly at `2^62 - 1` and one past; stream counts `2^60` and `2^60 + 1`; connection IDs of 0, 1, 20, 21 to 255 bytes; Retire Prior To equal to and one above the sequence; an empty token; a type in a longer form; unknown types to `2^62 - 1`; lengths past the payload; one byte changed; bytes after the frame | three-way: a reader written from section 19 over aioquic 1.8.0 (`Buffer`, `pull_ack_frame` for the ranges), and Table 3 for the packets | 1000 | each of 22 frame names 2.5% to 9%; valid 31%, mutated and accepted 4%, refused for its encoding 40%, refused for its packet 25%; each of 11 broken rules 1.6% to 4.6% | pass |
| quic: a payload of frames read back one at a time (`StateMachine`) | `Frame.decode` at each position of a payload | sequences of up to 60 writes, reads and changed bytes, in each packet type; a STREAM frame without a length takes the rest | the model of what was written, with the reader position; after a changed byte, the reader of the oracle | 1000 sequences | read of a frame 63%, at the end 59%, after a changed byte 43%, of a refused frame 16%, of a frame without a length 7% | pass |
| quic: a header of each form, RFC 9000 section 17 | `Packet.decode`, `decodeList`, `connectionId`, `lengthAndNumber`, `versions`, `Packet.encode` | Initial, 0-RTT, Handshake, 1-RTT, Retry, Version Negotiation; connection IDs of 0 to 20 bytes, to 255 in Version Negotiation; the four packet number widths; a Length from the width to `2^62 - 1`; the unused bits; fixed bit 0; each reserved bit; version 2 and others; a Retry with no token; versions cut short; one byte changed | three-way: a reader written from section 17, and aioquic's `pull_quic_header` on the fields it reads | 1000 | each form 10% to 15%; valid 50%, mutated and accepted 8%, refused 42%; each of 7 broken rules 3% to 7% | pass |
| quic: the writer of headers and its bounds | `Packet.encode`, `Header.Valid` | each form with a connection ID, a number, a Length or a token outside its bound | the bounds of section 17; the reader of the oracle reads what is written | 1000 | within bounds 54%, breaks a bound 46% | pass |
| quic: coalesced packets read back one at a time (`StateMachine`) | `Packet.decode`, the Length of a long header | datagrams of up to 30 packets, long headers with payloads to 1200 bytes, a short header last, connection IDs of 0, 4, 8, 20 bytes | the model of what was written; aioquic's walk of the same datagram finds each packet at the same place | 1000 sequences | read of each form 30% to 38%, at the end 75% | pass |
| quic: an integer at each of its four widths | `Varint.encodeWith`, `encode`, `decode`, `minWidth`, `capacity` | width 0 to 3, values to the capacity of the width, inputs cut at every length | aioquic `pull_uint_var`, `encode_uint_var` | 1000 | each width 25%, the largest value of its width 16%, a longer form 22% | pass |
| quic: the Retry packet and its tag | `Protection.retryTag`, `Packet.encode` of a Retry | original connection IDs of 0 to 30 bytes, tokens of 1 to 40 bytes, the unused bits | aioquic `encode_quic_retry`, which gives the vector of RFC 9001 A.4 at start | 300 | more than 20 bytes (refused) 15%, no bytes 16%, 20 bytes 13% | pass |
| quic: a sealed packet and the bits of its header | `Protection.unprotect`, `protect`, `checkReservedBits`, `checkHeader`, `checkSuite` | each protected type, both suites, numbers to `2^62 - 1`, an expected number up to 100 behind; a reserved bit set, a Length one short or long, fixed bit 0, ChaCha20 on an Initial, a byte changed | aioquic seals any header; RFC 9000 sections 17.2 and 17.3.1 say what a receiver does; aioquic opens the valid ones | 1000 | valid 43%, reserved bit 20%, changed byte 15%, fixed bit 7%, Length 11%, Initial under ChaCha20 3% | pass |
| quic: the width of a packet number | `Packet.packetNumberWidth`, `decodePacketNumber` | numbers to `2^62`, gaps to the acknowledged number at each power of 256 and one off | section 17.1: the least width that holds more than twice the gap; Appendix A.3 reads the number back | 1000 | no acknowledgement 27%, not earlier (refused) 15%, more than four bytes (refused) 14%; widths 1 to 4: 47%, 13%, 6%, 5% | pass |

### TLS 1.3 as QUIC carries it

| Property | EthLib definitions | Parameters varied | Reference | Cases | Label shares | Result |
| --- | --- | --- | --- | --- | --- | --- |
| tls: a handshake message of each type, RFC 8446 section 4 | `Tls.decode`, `readBody`, `readFrame`, `readExtensions`, `readCertificateEntry`, `Tls.encode`, `encodeBody` | the seven messages; hash lengths 0, 20, 32, 48, 64; session IDs of 0 to 32 and 33 bytes; each fixed field with another value; each vector below its least length; an extension type twice; a byte after the last field; a field past its message; unknown handshake types; one byte changed | three-way: a reader written from the presentation language of RFC 8446; the encoding is canonical, so EthLib must write back the same bytes | 1000 | each message 9% to 11%; valid 50%, mutated and accepted 6%, refused 37%, envelope not complete 7%; 13 broken rules 0.6% to 5% | pass |
| tls: the payload of an extension in each form | `decodePayload`, `readPayload`, `encodePayload` | the nine forms; lists at their least and largest lengths (127 versions); 30 payloads that break a bound; another extension type; one byte changed | three-way, the same kind of reader | 1000 | each form 9% to 14%; valid 47%, mutated and accepted 8%, refused 45% | pass |
| tls: the key schedule, RFC 8446 section 7.1 | `Tls.keySchedule`, `handshakeSecret`, `masterSecret`, `deriveSecret`, `finished`, `certificateVerifyInput` | shared secrets of 0 to 80 bytes, transcripts of 0 to 200 bytes, both roles | HMAC of the standard library and `HKDFExpand` of `cryptography`; the handshake secret of RFC 8448 section 3 at start | 300 | a shared secret of another length than 32: 25% | pass |
| tls: the transcript hash and its retry | `Tls.transcript`, `Transcript.append`, `messageHash`, `singleClientHello`, `retryRandom` | eleven orders of ClientHello, ServerHello, HelloRetryRequest, EncryptedExtensions, and random ones | section 4.4.1, with the retry random computed as SHA-256 of "HelloRetryRequest" | 1000 | with a retry 22%, a retry out of place 36% | pass |
| tls: key shares and shared secrets of both groups | `Crypto.keyShare`, `sharedSecret`, `readScalar`, `readP256Share` | X25519 and P-256; scalars 0 and `2^256 - 1`; the seven points of small order of RFC 7748; shares of 0 to 70 bytes, off the curve | `cryptography` (OpenSSL) | 200 | X25519 48%, P-256 52%, a shared secret 55%, a share refused 36%, a scalar refused 10% | pass |
| tls: the CertificateVerify signature | `Crypto.signCertificateVerify`, `verifyCertificateVerify`, `publicKeyMatches` | content of 0 to 120 bytes, four schemes | `cryptography` verifies EthLib's signature; EthLib verifies `cryptography`'s, and not over other content | 50 | | pass |
| tls: EthLib dials aioquic | `Handshake.clientStart`, `clientStep` and all below; `validateConfig`; `Libp2p.Tls.authenticatePeer` | both suites and both groups in each order, shares of all, one or no group; the listener's suites and groups; a wrong expected peer ID | aioquic's `tls.Context` as listener, with a libp2p certificate; its four traffic secrets, its state, the certificate it saw | 60 | completes 27%, no suite in common 37%, no share for the listener 25%, wrong peer ID 12% | pass |
| tls: EthLib listens to aioquic | `Handshake.serverStart`, `serverStep`, `serverFlight` and all below | the same, the dialer being aioquic | aioquic's `tls.Context` as dialer, the same four secrets | 60 | completes 45%, no suite in common 37%, no group in common 18% | pass |
| tls: EthLib dials EthLib, with and without a retry | both, with `clientRetry`, `checkSecondHello`, `retryGroup` | the same setups on both ends | the shared secret from the two private keys by `cryptography`; the traffic secrets and both Finished values from the messages by the reference of the key schedule | 60 | completes 80%, with a HelloRetryRequest 27%, no group in common 13%, no suite 7% | pass |
| tls: the messages that may carry an extension | `Handshake.allowedExtension` | types 0 to 60 and any, in all seven messages each | the table of RFC 8446 section 4.2, and RFC 9001 section 8.2 for type 57 | 1000 | a listed type 32%, an unlisted one 68% | pass |
| tls: a handshake as commands, with changed bytes (`Command`, madhouse) | both ends, `checkLevel`, `readMessage` | sequences of up to 80 commands: deliver, change a byte on the way, offer at another level, offer again, settle | no end completes after a changed byte; RFC 9001 section 4.1.3 for the levels; both ends hold the same secrets at the end | 300 sequences | a byte changed 37%, refused after it 33%, accepted after it 7%, higher level 27%, lower level 10%, offered again 30%, both ends completed 16% | pass |

### Snappy

| Property | EthLib definitions | Parameters varied | Reference | Cases | Label shares | Result |
| --- | --- | --- | --- | --- | --- | --- |
| snappy: copies from more than 65535 bytes back | `Snappy.decompress`, `decompressElements`, `copyBytes` | a first literal of 65535 to 70000 bytes; then up to four elements: four-byte offsets of 65536, 65537, the output length, one less, any; four-byte offsets of 65535 or less; two-byte and one-byte offsets; an offset one past the output, `2^32 - 1`, zero; a declared length one off | a reader written from `format_description.txt`, and cramjam 2.14.0 | 200 | valid 51%, refused 49%, a valid copy from more than 65535 back 37% | pass |
| snappy: the compressor at the end of a two-byte offset | `Snappy.compress`, `emitCopies`, `copyElement` | a run of 4 to 300 bytes repeated 65533 to 65538, 70000 and 131072 bytes back, behind zeros or noise | both readers give the data back; EthLib reads its own block | 100 | within a two-byte offset 41%, past it 59%, a filler of zeros 75% | pass |

With a filler of zeros the table entry of the run survives, and the compressor copies the run at 65535 bytes and writes a literal at 65536: the block is 3142 and 3205 bytes for a run of 64.

### libp2p

| Property | EthLib definitions | Parameters varied | Reference | Cases | Label shares | Result |
| --- | --- | --- | --- | --- | --- | --- |
| libp2p-tls: a time is read as the calendar gives it | `Libp2p.Tls.readTime`, `decimal`, `leapYear`, `monthDays` | tag (UTCTime, GeneralizedTime, the other form's tag, three other tags), year 1 to 9999 with 35 edge years, the 1950 pivot, the end of February in 20 chosen years, month ends, each field one past its range, ten broken texts | Python `datetime` under RFC 5280 section 4.1.2.5 | 4000 | read 66%, refused 34%; UTCTime 1950-1999 read 14%, 2000-2049 read 14%; GeneralizedTime before 1950 read 17%, from 2050 read 15%; before 1970 33%; 29 February of a leap year read 5%, of another year refused 3%; last day of a month read 14%; a day past the month's end refused 11%; century year read 9% | pass |
| libp2p-tls: a certificate is read and authenticated as the texts say | `readCertificate`, `readAlgorithm`, `readValidity`, `readName`, `readExtension`, `readTail`, `readP256`, `verifyP256`, `readSignedKey`, `signedKey`, `authenticateHost`, `authenticateCertificate`, `authenticate`, `authenticatePeer`, `Libp2p.peerId` | certificate key (P-256, secp256k1, P-384, Ed25519), signature algorithm, signature (good, high s, flipped, padded), version (absent, 0 to 3), serial, names, both time forms, inverted validity, compressed SPKI, unique IDs, extensions (14 sound lists, 15 broken), host key (secp256k1, P-256, Ed25519, RSA, P-384), 13 host variants; receiver: host algorithms, certificate algorithms, `rejectUniqueIds`, clock (between, each end, one second outside each end, 0, `2^40`), chain of 0, 1 or 2, expected peer | a strict reader of RFC 5280 section 4.1 and the libp2p TLS text in the oracle, with `cryptography` 50.0.2 for every signature and key, cross-checked against `cryptography`'s own parser | 1000 | authenticated 19%, read and refused 52%, not read 29%; authenticated at the first second 5%, at the last 3%; refused one second before 2.5%, after 2.8%; first failing rule: validity 10%, algorithm 12%, selfSignature 6%, chain 5%, uniqueId 4.5%, hostSignature 4%, missingExtension 4%, peerId 3%, publicKey 3%, criticalExtension 2% | pass |
| libp2p-tls: a certificate with one byte changed | the same, on bytes changed after signing | flip of any byte with 9 masks, drop, insert, cut, append | the same reader on the changed bytes | 1000 | untouched 16%, changed and still read 41%, changed and not read 43%, changed and authenticated 0% | pass |
| libp2p-tls: a P-256 signature verifies as OpenSSL says | `Tls.verifyP256`, `readP256`, `Libp2p.decodeScalars` | key, message, `n - s`, eight DER changes, other message, other key | OpenSSL through `cryptography`, with strict DER | 1000 | verifies 65%, does not 35%, the high-s twin verifies 19% | pass |
| peerid: the DER of a signature is the reference's | `Libp2p.encodeSignature`, `derInteger`, `decodeScalars` | r and s at every byte length from 1 to 32, zero, the top-bit edges | `cryptography` `encode_dss_signature` | 1000 | r takes 33 bytes 26%, r under 32 bytes 59%, a scalar is zero 4.5% | pass |
| peerid: a changed DER signature is read as the reference reads it | `Libp2p.decodeScalars` | flip, padded r, padded s, append, cut, long-form length, negative | `cryptography` `decode_dss_signature` plus re-encoding and the range | 1000 | valid 27%, mutated and still accepted 25%, refused 47% | pass |
| yamux: a stream of frames is read back, one frame at a time (`StateMachine`) | `Yamux.decode`, `Yamux.encode`, `Kind.ofUInt8?`, `Kind.toUInt8` | version 0 to 255, type 0 to 255, flags over all 16 bits, stream ID and length over 32 bits, data of 0 to 40 bytes, a data length past or short of the data, one byte of the next frame changed | an encoder written in Lean from "Framing" writes the stream; a reader written in Python from the same text reads every position | 1000 sequences of up to 60 | data valid 42%, window update 46%, ping 47%, go away 46%; unknown type refused 23%, another version refused 25%; data mutated and still accepted 9%, refused 5% | pass |
| mplex: a stream of frames is read back, one frame at a time (`StateMachine`) | `Mplex.decode`, `Mplex.encode`, `Flag.ofNat?`, `Flag.toNat`, `Flag.ends`, `Uvarint.decode` | flag 0 to 7, stream ID to `2^60 - 1` and past it, data of 0 to 40 bytes, data on a close or reset, declared lengths `2^20`, `2^20 + 1`, `2^32`, `2^63 - 1`, `2^63`, padded varints, one byte changed | the same arrangement, from "Message format" | 1000 sequences of up to 60 | new stream 30%, message 43%, close 38%, reset 38%; flag 7 refused 18%, padded varint 38%, stream ID past the bound 18%, data on a close or reset 19% | pass |
| mplex: a frame of 1 MiB is read, and one byte more is refused | `Mplex.decode`, `maxData` | sizes `2^20 - 1`, `2^20`, `2^20 + 1`, flag 0 to 2, data present or missing | the Python reader, and the bound | 10 | data there 50%, missing 50% | pass |
| yamux: the numbers and names of the texts, and those of mplex and multistream | the constants of `Yamux`, `Mplex`, `Multistream` | none | literals written from the texts | 1 | | pass |
| multistream: a stream of messages is read back, one at a time (`StateMachine`) | `Multistream.decode`, `Multistream.encode`, `Uvarint.decode` | 9 names with `na`, `ls` and the empty message, any bytes, lengths 126 to 128 and 16382 to 16384, length 0, length short or long, last byte not a newline, padded varint, one byte changed | the same arrangement, from "Protocol" | 1000 sequences of up to 60 | message valid 70%, long message 21%, padded varint refused 24%, length of zero refused 24%, no newline refused 23% | pass |
| multistream: a negotiation, its messages read in any order (`Command`, madhouse) | `Multistream.Dialer.start`, `Listener.start`, `dial`, `listen`, `negotiate` | proposals and supported lists of 0 to 4 names from 6; commands `ListenerReads`, `DialerReads`, `Drain`, `Settled` over two wires of bytes | a model of both peers written from "Protocol" | 1000 sequences of up to 60 | settled 64%: agreed on the first proposal 19%, after `na` 10%, nothing in common 26%, no proposal 10% | pass |
| multistream: a negotiation with stray messages (`Command`, madhouse) | the same, with `Stray` | the same, plus a stray message to either peer at any time | the same model, following the module's documented reading where the text is silent | 1000 sequences of up to 60 | settled after a stray 41%; dialer stopped 9%, dialer aborted 8%, listener aborted 3%, both agreed after a stray 9% | pass |
| multistream: the outcome is the first proposal that the listener supports | `Multistream.negotiate`, `run`, `respond`, `supports` | two lists of 0 to 5 and 0 to 4 names | `List.find?` | 1000 | in common 51%, nothing in common 36%, no proposal 14% | pass |
| upgrade: Noise, then yamux when both support it | `Upgrade.upgrade`, `TcpProfile.muxers`, `securityProposals`, `noiseId` | both profiles, all four combinations | the rule of the consensus networking specification | 100 | both yamux 23%, one 48%, neither 29% | pass |

### devp2p, RLPx, discovery, ENR entries, Noise

| Property | EthLib definitions | Parameters varied | Reference | Cases | Label shares | Result |
| --- | --- | --- | --- | --- | --- | --- |
| devp2p: the reference reads EthLib's message | `Devp2p.encodeMessage`, `decodeMessage`, `Message.toItem` | message kind, every reason, p2p version, capabilities, port, Snappy on and off | reader written from `rlpx.md` with `rlp`, Snappy reader from `format_description.txt` | 1000 | hello 45%, disconnect 33%, ping or pong 22%, compressed 26% | pass |
| devp2p: the Hello of EIP-8 with additional elements | `decodeMessage`, `Codec Hello` | the one vector of EIP-8 | the same reader, and the literal fields | 1 | | pass |
| devp2p: frame data reads as rlpx.md says | `decodeMessage`, `splitFrame`, `messageData`, `Message.ofItem` | odd field, element more or less, other ID, trailing bytes, other compression, one byte changed | the same reader | 1000 | valid 28%, mutated and accepted 15%, refused 57% | pass |
| devp2p: the reasons of Disconnect | `DisconnectReason.ofNat?`, `toNat` | every number 0 to 17, up to 300, and large ones | the table of `rlpx.md`, transcribed | 1000 | in the table 55%, outside 45% | pass |
| devp2p: shared capabilities and their message IDs | `sharedCapabilities`, `messageOffsets`, `negotiate`, `route` | both lists, names by prefix and case, versions, the length of each capability (0 included), the ID | "Message ID-based Multiplexing", in Python | 1000 | none shared 27%, one 19%, two or more 54%, two versions of a name 15%, ID in a block 24% | pass |
| devp2p: Snappy from version 5 of both peers | `snappyEnabled` | both versions, 0 to `2^64` | EIP-706 as arithmetic | 1000 | both 27%, one older 49%, both older 24% | pass |
| devp2p: a message that declares more than 16 MiB | `messageData`, `MAX_MESSAGE_SIZE` | declared length `2^24 - 5` to `2^24 + 5`, up to `2^35` | the same reader | 1000 | above 36%, at most 64%, exactly `2^24` 6% | pass |
| devp2p: 16 MiB of data pass, and one byte more does not | `Session.receive` | `2^24 - 1`, `2^24`, `2^24 + 1` bytes, plain and in a cramjam block | the bound of "Message Encoding" | 1 (six combinations) | | pass |
| devp2p: a session against its model (`Command`, madhouse) | `receive`, `Phase.opened`, `negotiate`, `route` | our Hello (version 3 to 255, capabilities), lengths, 12 command slots, 1 to 40 frames | per-frame reader from `rlpx.md` in Python, phase model in Lean | 1000 sequences | Hello opens 66%, Disconnect closes 23%, Ping 28%, capability message 31%, compressed read 26%, refused before Hello 76%, after Disconnect 20%, while active 54% | pass |
| rlpx: the reference reads and writes EthLib's ack | `Rlpx.makeAck`, `readAck`, `sealPacket` | all keys, nonce, ECIES `r` and `iv`, padding 0 to 200 | ECIES and ack from `rlpx.md`, libsecp256k1, `cryptography` | 300 | no padding 24% | pass |
| rlpx: an ack with one thing changed | `readAck`, `openPacket`, `Codec AckMessage` | odd field, version other than 4, more or fewer fields, size one off, one byte changed | the same | 1000 | valid 25%, mutated and accepted 17%, refused 57% | pass |
| rlpx: the ack of before EIP-8 is refused, as documented | `readAck` | keys, nonce | the 210-byte form built by the reference | 50 | | pass |
| rlpx: an auth with one thing changed | `readAuth`, `recoverSigner`, `makeAuth` | 23 named changes (version forms, recovery id, high s, flipped signature, key off curve, sizes), one byte changed | the same, recovery by libsecp256k1 | 1000 | valid 21%, mutated and accepted 24%, refused 55%, accepted with another ephemeral key 9% | pass |
| rlpx: both sides derive the secrets of rlpx.md | `respond`, `finish`, `deriveSecrets`, `Secrets.egress`, `ingress` | both sides' keys, nonces, paddings | derivation from the private keys, with what the packets must hold | 300 | no padding in auth 28%, in ack 27% | pass |
| rlpx: a packet with a changed byte is refused | `respond`, `finish` | which packet, the change | the same readers | 300 | auth 51%, ack 49% | pass |
| rlpx: the size limit of a packet | `sealPacket`, `makeAck`, `readAck` | sizes 65534, 65535, 65536 | the 16-bit size | 20 | largest 35%, one more 35% | pass |
| discv5: WHOAREYOU is the packet of the specification | `Discv5.makeWhoareyou`, `readWhoareyou` | destination, IV, nonce, ID nonce, `enr-seq` | packet codec from `discv5-wire.md`; reproduces the vectors | 1000 | `enr-seq` 0 29% | pass |
| discv5: a packet read as a challenge | `readWhoareyou` | flag 0 to 255, authdata size, message present, one byte changed | the same | 1000 | valid 31%, mutated and accepted 4%, refused 65%, valid packet of another flag 15% | pass |
| discv5: a message packet is the specification's | `sealMessage`, `openMessage` | key, IDs, IV, nonce, plaintext 0 to 80 and 1190 to 1196 bytes | the same, AES-GCM by `cryptography` | 1000 | would pass 1280 bytes 11%, 1270 or more 16%, empty 12% | pass |
| discv5: a packet opened as a message | `openMessage` | the key held (right, another, none), reader ID, flag, one byte changed | the same | 1000 | valid 42%, refused 58%, mutated and accepted 0% | pass |
| discv5: node B accepts a handshake | `acceptHandshake`, `initiateHandshake`, `deriveKeys` | ephemeral key form (compressed, uncompressed, off curve, other prefix, cut, none), signer, flipped signature | step 4 of `discv5-theory.md`, HKDF of `cryptography`; reproduces the read key of the vectors | 300 | valid 36%, mutated and accepted 7%, refused 57% | pass |
| discv4: the record of an ENRResponse is the sender's | `Discv4.recordSignedBy` | signer and sender, scheme, flipped, high s, short signature, changed seq, no key, size around 300 | EIP-778 reader with `rlp` and libsecp256k1 | 300 | valid 39%, mutated and accepted 7%, refused 54%, valid but over 300 bytes 13% | pass |
| enr: the consensus entries at every fork and length | `Enr.readEntries`, `readSsz`, `readCgc`, `readAt`, `readRequiredAt` | every fork from phase0 on, `count` 1 to 24, 57 to 72, 128, 255 to 257, 1000, each of five entries valid, absent or malformed | `p2p-interface.md` of phase0, altair, fulu; remerkleable beside a reader from the SSZ rules | 1000 | valid 57%, mutated and accepted 6%, refused 37%, before Altair 16%, Altair to before Fulu 43%, from Fulu 42%, bitfield of another length than 64 read 37% | pass |
| enr: the consensus keys of a fork | `keysAt`, `ConsensusKey.since` | all 29 forks | the same texts | 1000 | before the beacon chain 34%, from Fulu 26% | pass |
| enr: the eth entry reads as eth.md says | `readEthEntry`, `readEth` | more outer or inner elements, hash size, non-canonical or large `forkNext`, entry absent | `enr-entries/eth.md` with `rlp` | 1000 | valid 40%, mutated and accepted 17%, refused 43% | pass |
| enr: the eth entry is written as eth.md says | `ethEntry` | hash, next | `rlp` | 1000 | no next fork 24% | pass |
| noise: the payload is the protobuf package's | `Noise.makePayload`, `encodePayload`, `signedStatic` | identity key, static key, extensions | `protobuf` 7.36.2 with the schema of the Noise specification built at run time; libsecp256k1 | 300 | with extensions 58%, without 42% | pass |
| noise: a payload in every form of the encoding | `decodePayload` | seven forms (order, a field twice, extensions in parts, unknown fields, other wire type, group) | the same package | 1000 | plain 13%, extensions in parts 34%, twice 13%, wire type 16%, group 14% | pass |
| noise: a payload with a changed byte | `decodePayload` | form, one byte changed | the package with extensions as bytes, and a walker from the encoding guide | 1000 | mutated and accepted 33%, refused 67%, refused by the wire rules only 0.1% | pass |
| noise: field number 0 in a group is refused, as documented | `decodePayload`, `Protobuf.records` | key, signature, extensions | the package reads it; the walker refuses | 100 | | pass |
| noise: a payload authenticates as the specification says | `authenticatePayload`, `Remote.publicKey` | other static key, other signer, flipped signature, Ed25519 key, key off curve, no key, no signature, long key; four forms | libsecp256k1 over the prefix and the static key | 300 | valid 43%, refused 57% | pass |
| noise: noiseprotocol reads a libp2p handshake | `initializeLibp2p`, `writeLibp2p`, `readLibp2p`, `complete` | all six keys, extensions of both sides | noiseprotocol 0.3.1 reads EthLib's three messages; `cryptography` derives the X25519 keys | 100 | responder sends extensions 57%, initiator 64% | pass |
| noise: no extensions in the first message | `writeLibp2p`, `readLibp2p` | extensions, a key in the payload | the rule of the Noise specification | 100 | with 52%, without 48% | pass |
| noise: a message behind its length | `Noise.frame`, `unframe` | sizes 0 to 300, 65535, 65536, 65537 | two big-endian bytes | 1000 | too long 11%, empty 11% | pass |
| noise: bytes read as one frame | `Noise.unframe` | declared length one off and 256 off, input cut to 0 to 3 bytes | the same | 1000 | valid 67%, refused 33% | pass |

## Findings

None.

## Documented differences

These are choices that EthLib's docstrings state.
The properties check that each holds, and none is a finding.

From the `protobuf` package (upb), in `Encoding/Protobuf.lean` and `Gossip/Rpc.lean`:

- A named field with another wire type is rejected; `protobuf` keeps it as an unknown field.
- A singular message field (`extensions`, `partial`) keeps its last occurrence whole; `protobuf` merges the occurrences, so `1a 04 32 02 50 01 1a 02 32 00` gives `partialMessages` false in EthLib and true in `protobuf`.
- The fields `from`, `seqno`, `signature`, `key` of a message are rejected at any wire type; `protobuf` reads them.
- A string that is not UTF-8 is rejected; `protobuf` (proto2) keeps its bytes.
- A varint of a value of `2^64` or more, or of eleven bytes, is rejected; `protobuf` drops the bits past the 64th and reads some eleven-byte forms.
- A key or a length padded past five bytes is accepted, as the encoding guide asks no shortest form; `protobuf` refuses it.
- `protobuf` keeps `00 00` as field number 0 of a message that has no fields; EthLib refuses field number 0 everywhere, as the proto2 guide says.
- A message without a topic is rejected; `protobuf` parses it and reports it as not initialized.

From RFC 9000, in `Quic/Frame.lean` and `Quic/Packet.lean`:

- A frame type in a longer form is `frameEncoding`; section 12.4 lets a receiver treat it as PROTOCOL_VIOLATION.
- A frame that breaks both its form and its packet type is reported for its form.
- The Length of a long header is not compared with the bytes that follow; the module leaves that to the caller, and aioquic checks it in its reader.
- A Retry with a token of no bytes is refused when read (section 17.2.5.2 asks a client to discard it); aioquic's header reader takes it.
- Version 2 is refused; aioquic reads it.
- A Version Negotiation packet may hold connection IDs of 255 bytes (section 17.2.1); aioquic bounds them at 20.

From the libp2p and X.509 texts, in `Libp2p/`:

- A value in a name, or an algorithm parameter, of a tag outside the subset of `Der.validate` is refused; `cryptography` reads such names.
- A validity whose end is before its start is refused at reading; `cryptography` reads it.
- A compressed P-256 point is refused, in the certificate key and in a P-256 host key.
- A host key must be the deterministic protobuf, and Ed25519, RSA and other ECDSA host keys are refused.
- Every critical extension other than the libp2p one is refused, a critical KeyUsage included, so `Handshake.checkSigningUsage` never sees a critical one.
- Only ecdsa-with-SHA256 without parameters under a P-256 key is a certificate signature.
- mplex: the reader enforces the sender's rules (1 MiB, no data on a close or reset).
- multistream: `ls` is an ordinary proposal; a wrong first message aborts; an answer that is neither echo nor `na` stops the dialer.
- `cryptography` 50.0.2 reads extensions and unique IDs in a version 1 certificate, an empty `Extensions`, two differing algorithm identifiers, and unused bits in a BIT STRING; EthLib follows RFC 5280 and refuses them.
- `cryptography` reads no version 2 certificate; EthLib does.

From the devp2p, discovery and Noise texts:

- A key with field number 0 inside a group is refused (`3b 00 01 3c`); the `protobuf` package reads it there, and refuses the same key at the top level of a message.
- The ack of before EIP-8 (210 bytes, no size) is refused; `Rlpx/Handshake.lean` says so.
- A Disconnect before the Hello is read uncompressed; `Devp2p/Session.lean` says so.
- `cgc` and `nfd` are required from Fulu on, so a record without them is refused; the fulu text says that the sender MUST add them.
- Noise skips a known field with another wire type, as protobuf does, where `Gossip/Rpc.lean` refuses it.
- With no clause in the specification and no property of their own: a Ping or Pong with a list that is not empty is refused, a Disconnect as a bare byte is refused, bytes after `msg-data` are refused, a recovery id of 2 or 3 in `auth` is refused, a high `s` is accepted in `auth` and in a record.

QUIC transport parameters (RFC 9000 section 18) have no codec in EthLib: `Quic/Tls/Extensions.lean` keeps them opaque, as its docstring says.
So the bounds of each parameter could not be tested; the handshake carries the bytes unchanged, which the aioquic properties check.

## Whether a pass means something

Each reference was given a fault, in a copy of `oracle/`, and the driver was run against it at 1,000 cases.
Every fault was found.

| Fault planted in the reference | Property that failed | After |
| --- | --- | --- |
| NEW_TOKEN allowed in 0-RTT | quic: a frame of each type | 6 tests |
| a stream count of `2^60` refused | quic: a frame of each type | 1 test |
| Retire Prior To equal to the sequence refused | quic: a frame of each type | 14 tests |
| one reserved bit of a short header ignored | quic: a header of each form | 44 tests |
| a session ID of 33 bytes accepted | tls: a handshake message of each type | 721 tests; the generator now draws 33 bytes more often |
| `signature_algorithms` of no entry accepted | tls: the payload of an extension | 8 tests |
| cookie not allowed in HelloRetryRequest | tls: the messages that may carry an extension | 753 tests; a case now asks about all seven messages |
| the label `s hs traffic` misspelt | tls: the key schedule; tls: EthLib dials EthLib | 1 test each |
| field number `2^29` accepted | protobuf: the records of a message | 440 tests; the generator now draws `2^29` more often |
| `key` (6) not forbidden | rpc: the rules that EthLib documents | 91 tests; the general RPC property did not find it in 1,000 |
| a copy from exactly the output length refused | snappy: copies from more than 65535 bytes back | 4 tests |
| 2100 taken as a leap year | libp2p-tls: a time; a certificate | 1 test; 10 tests |

In the devp2p family the reference was changed in 31 places (table entries, bounds, fork gates, the order of nonces, prefixes).
28 changes were found; the other 3 are equivalent, because another check refuses the same inputs.

## Harness mistakes, one line each

- The oracle padded a buffer by the Length of a header, which may be `2^62 - 1`: the Python process took 58 GB for two minutes before it was killed; the oracle now has a 4 GB address limit and pads only short lengths.
- A STREAM frame without a length takes the frames after it as data, so an offset at `2^62 - 1` makes the next byte an error; the model of the payload first expected the frame.
- The generator of unknown frame types shrank to type 0, which is PADDING.
- upb refuses a key or a length of more than five bytes, and reads `00 00` as field 0 of an empty message; both were first taken for disagreements with EthLib.
- A group that the input ends in is refused as `truncated` or as a short varint by its depth, as the docstring of `ProtobufError` says; the property first asked for one of them.
- aioquic takes a short header with the other key phase for a key update and fails to open it; the reference now sets its key phase from the packet.
- `HEDGEHOG_ONLY=tls` also selects `libp2p-tls`; the property names of this layer now end their family with a colon.
- A minimum of `cover` near the observed share failed on some seeds, and a share of 3% is absent from one run of a hundred cases in twenty; such minimums are now asked of runs of 1,000 only.
- `load_der_public_key` raises `UnsupportedAlgorithm`, not `ValueError`, for an unknown key OID; the oracle crashed on a flipped byte.
- The first RFC 5280 reader of the oracle did not validate algorithm parameters, and EthLib does.
- A scratch file in the shared scratchpad was overwritten by another agent.

- The first generator of capability lists shared nothing in 70% of cases; both lists now hold a common part.
- The self-check of `decoders_devp2p.py` ran before the functions it calls were defined, so the oracle of every agent failed to start for about a minute.
- A failing case with a random plaintext of 1.2 KB shrank for over 12 minutes; the long plaintext now repeats one byte.
- An ENR label counted `cgc` as required before Fulu instead of from it.

## Not covered

- QUIC transport parameters: EthLib has no codec for them.
- QUIC version 2, stateless resets, key updates and the limits of RFC 9001 section 6.6: EthLib has none of them.
- TLS: `receiveTicket` (NewSessionTicket after completion), the PSK offer checks (`checkPskOffer`, `pskIdentities`), a cookie in a HelloRetryRequest (`retryCookie`; EthLib's own listener sends none), `checkSigningUsage`, the branch `rejectLegacySessionId := false`, an empty client Certificate (`certificateRequired`).
- TLS: the retry path has no second implementation, since aioquic has no HelloRetryRequest; it is checked by EthLib against EthLib, with the secrets and the Finished values derived apart from the messages.
- TLS: the alert numbers of `Handshake.Error.code` were compared with RFC 8446 section 6 by reading only.
- The handshake against aioquic runs 60 cases a direction, since each case makes two certificates.
- Protobuf: packed repeated fields, which the schema has none of; groups deeper than three; RPCs of more than a few hundred bytes.
- Snappy: outputs above 70,000 bytes, and the framed format with such blocks.
- The fields of an error (the counts of `truncated`, the OID of `duplicateExtension`) are compared in few places; mostly the constructor or only the refusal is.
- Version 2 certificates have no second reference: `cryptography` cannot read them, so the RFC reader of the oracle judges them alone.
- RSA certificate keys, names with nested constructed values, high tag numbers and indefinite lengths except through byte flips.
- yamux data over 40 bytes; mplex data other than 0 to 40 bytes and around 1 MiB.
- Text forms of peer IDs, multiaddrs, and Ed25519 or RSA peer IDs: EthLib has none.
- The multistream model follows the module's reading where the text is silent, so it cannot fault those choices.

- A discv5 session as commands (message, challenge, handshake, both directions); each step is compared alone.
- `Discv5.sealHandshake` and `openHandshake` with a changed record or authdata, beyond the earlier round.
- `Noise.encodePayload` at its limit of 65535 bytes, and `writeLibp2p`, `readLibp2p` out of order or with a changed message.
- `Enr.readEntries` at forks before phase0 and with `count` 0; no text defines them.
- The `auth` and `ack` vectors of EIP-8; only its Hello vector is used.
- Devp2p sending: there is no send-side session in EthLib.
- A changed byte under an AEAD tag is never accepted, so that class is empty by nature (discv5 message, RLPx packet, Noise authentication).

## Notes on lean-hedgehog 0.3.0

What helped.

- `applySut sut before after t` is what a stream reader needs: `before` says where the read starts and which frame it must meet, and `after.unread` says what must be left; the QUIC payload and datagram machines use both.
- The context first in `check`, `apply` and `build`: the oracle sits in the context of the TLS handshake scenario, and a command holds only its own data (`Spoil` an index and a mask).
- `classify`, `label` and `cover` in `TestT`, after the oracle answered: a case is counted by what the reference saw in it (`classifySeen` splits a word of the answer), not by what the generator meant, and a generator that seldom reached a rule showed at once.
  The first RPC generator broke several rules per case, so 19% of all cases died on an eleven-byte varint before any other rule was read; the shares showed it, and one rule per case fixed it.
- `cover` found real holes: the STREAM frame without a length was at 0.5%, and both ends of a handshake completed in 3% of the command sequences, before the generators were changed.
- `scenarioFrom` with a generated start state, a range and a setup: the setups of both ends are generated, and the setup makes the certificates through the oracle and sends the first ClientHello.
- `checkGroup` with `Selection.fromEnv` and `mustFail`: with three agents on one driver, `HEDGEHOG_ONLY` was the only way to run one's own part; a findings group of no property prints nothing and is true, so the driver needs no special case.
- `===` on `Except`: `got === .error .reservedBits` reads as the rule it states.
- Shrinking: the model mistake of the greedy STREAM frame shrank to `[WRITE(STREAM 0c00ffffffffffffffff), WRITE(PADDING 00), READ]`, the upb quirk to `0000`, the key phase to the header `44 00`, a certificate to all-zero keys and default fields.

What was awkward.

- A minimum of `cover` depends on the run length, and the default run of a driver is 100 cases: a kind at 3% is absent from one run in twenty, and 22 frame types each at 3% fail most short runs.
  This layer has `coverLong long minimum name b`, which is `classify` under 1,000 cases; a `cover` that knows the number of tests, or a minimum that is waived below a count of tests, would do it in the library.
- `cover` takes a whole percentage, so a kind that is rightly rare cannot be required below 1%.
- A `cover` in a helper that several properties share counts in each of them; a flag had to be passed through.
- The report lists `cover`, `classify` and `label` lines in the order of first appearance, which changes from run to run; a fixed order would make two runs comparable.
- A `label` with a varying text floods the report.
- The state of `scenarioFrom` is one type for what is generated and for what the setup adds, so every field that the setup fills is an `Option` (`client`, `clientState`), and each command unpacks it; a setup from a generated value to the state, `α → TestT m σ`, would remove them.
- A scenario's command list has no weights; `List.replicate 14 (Command.gen Deliver (σ := Session))` stands for one, and it needs the state named.
- `forAll` lines carry no name; a property with five draws is read by counting lines.
- `HEDGEHOG_ONLY` matches parts of names, so `tls` selects `libp2p-tls` too, and a name that holds a comma cannot be selected whole.
- `ensure !x "message"` parses as `!(x "message")`; a line in USAGE would save the next reader.

- `next` is pure, so it cannot know what the oracle will answer; the devp2p session assumes that a Hello is valid, which is enough to generate the commands after it.
  A line in USAGE that `next` may be an approximation would help.
- There is no way to delay a command but a counter in the state and `check`.
- With an expensive test and a large byte array, shrinking ran for over 12 minutes with no line of progress.
- Every structure that holds a `ByteArray` or a function needs a `Repr` written by hand for `forAll`.

`buildIn` and `next` are used in the devp2p session: a Hello shares a part of our capabilities, and a capability message aims at the blocks of IDs.
Not used: `HEDGEHOG_RECHECK`, `Property.lift` (the tree has `Support.pureIO`).

Bugs in the library: none met.

## A failure of the harness, found by the coordinator

A full run at 1,000 cases failed once in the scenario of a handshake with changed bytes, shrunk to two `SPOIL(74, 2)` in a row.
Two changes of one byte with one mask restore the byte, so the handshake completed, as it should, and the model still held the message for changed.
`Spoil` now runs once in a sequence.
The case was replayed from its report line with `HEDGEHOG_RECHECK` before the change, where it failed, and after it, where it passes.
