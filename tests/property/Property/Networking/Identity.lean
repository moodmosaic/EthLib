import Hedgehog
import Support
import Property.Networking.Common
import EthLib.Networking.Libp2p.PeerId
import EthLib.Networking.Noise

/-!
# libp2p identities and the Noise XX handshake

Signatures against libsecp256k1 (strict DER, low `s`).

Also a whole handshake against the `noiseprotocol` package.
-/

open Hedgehog Support EthLib EthLib.Networking NetworkingProperty
open EthLib.Cryptography.Secp256k1 (Fn)

namespace NetworkingProperty.Identity

/-- A signature is libsecp256k1's: SHA-256, RFC 6979, low `s`, DER. -/
def sign (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAll genSecret
  let message ← forAllWith hex (genBytes (.linear 0 60))
  pure do
    answer ((Libp2p.sign (Fin.ofNat _ sk) message).mapError fun _ => ()) ===
      (← oracle.ask ["libp2p_sign", secretHex sk, hex message])

/-- A way to change a DER signature. -/
inductive Change where
  | none
  | flip (i : Nat)
  /-- Replace `s` by `n - s`, in correct DER. -/
  | highS
  /-- Pad `r` with a zero byte that DER forbids. -/
  | padR
  | append
  | cut
  /-- Change the length byte of the sequence. -/
  | length
  /-- Zero for `s`. -/
  | zeroS
  deriving Repr

/-- A changed signature verifies exactly when libsecp256k1 takes it. -/
def verify (oracle : Oracle) : Property IO := propertyM do
  let sk ← forAll genSecret
  let message ← forAllWith hex (genBytes (.linear 0 40))
  let change ← forAll (Gen.frequency [(3, pure Change.none),
    (3, Change.flip <$> Gen.nat (.linear 0 80)),
    (1, pure .highS), (1, pure .padR), (1, pure .append), (1, pure .cut), (1, pure .length),
    (1, pure .zeroS)])
  let badKey ← forAll (Gen.frequency [(8, pure none), (1, some <$> Gen.nat (.constant 0 36))])
  pure do
    let .ok sig := Libp2p.sign (Fin.ofNat _ sk) message | failWith "sign"
    let .ok (r, s) := Libp2p.decodeSignature sig | failWith "EthLib refuses its own signature"
    let sig : ByteArray := match change with
      | .none => sig
      | .flip i => sig.set! (i % sig.size) (sig[i % sig.size]! ^^^ 0x01)
      | .highS => Libp2p.encodeSignature r (Fn.modulus - s)
      | .padR =>
        let body := [0x02, UInt8.ofNat ((Libp2p.derInteger r).length - 1)] ++ [0] ++
          (Libp2p.derInteger r).drop 2 ++ Libp2p.derInteger s
        ⟨([0x30, UInt8.ofNat body.length] ++ body).toArray⟩
      | .append => sig.push 0
      | .cut => sig.extract 0 (sig.size - 1)
      | .length => sig.set! 1 (sig[1]! + 1)
      | .zeroS => Libp2p.encodeSignature r 0
    let .ok key := Libp2p.publicKey (Fin.ofNat _ sk) | failWith "publicKey"
    let key := match badKey with
      | some i => key.set! i (key[i]! ^^^ 0x04)
      | none => key
    annotate s!"key {hex key} signature {hex sig}"
    (if Libp2p.verify key message sig then "1" else "0") ===
      (← oracle.ask ["libp2p_verify", hex key, hex message, hex sig])

/-- A peer ID is the identity multihash of the key protobuf, and reads back to the key. -/
def peerId : Property IO := pureIO do
  let sk ← forAll genSecret
  let point := publicOf sk
  let id := Libp2p.peerId point
  hex id === "0025" ++ "08021221" ++ hex point.encodeCompressed
  ensure ((Libp2p.decodePeerId id).toOption == some point) "the peer ID does not read back"
  let i ← forAll (Gen.nat (.constant 0 5))
  ensure (Libp2p.decodePeerId (id.set! i (id[i]! ^^^ 1))).toOption.isNone "a changed header reads"

/-- A whole XX handshake, and the first transport message of each side, are noiseprotocol's. -/
def noise (oracle : Oracle) : Property IO := propertyM do
  let keys ← forAllWith (fun ks => " ".intercalate (ks.map hexv))
    (Gen.list (.singleton 4) (genVector 32))
  let prologue ← forAllWith hex (genBytes (.linear 0 8))
  let payloads ← forAll (Gen.list (.singleton 4) (genBytes (.linear 0 40)))
  pure do
    let [si, ei, sr, er] := keys | failWith "keys"
    let [p1, p2, p3, text] := payloads | failWith "payloads"
    let want ← oracle.ask (["noise_xx"] ++ keys.map hexv ++ [hex prologue] ++ payloads.map hex)
    let run : Except Noise.NoiseError (List ByteArray) := do
      let a := Noise.initializeHandshake true si ei prologue
      let b := Noise.initializeHandshake false sr er prologue
      let (a, m1) ← Noise.writeMessage a p1
      let (b, _) ← Noise.readMessage b m1
      let (b, m2) ← Noise.writeMessage b p2
      let (a, _) ← Noise.readMessage a m2
      let (a, m3) ← Noise.writeMessage a p3
      let (b, got3) ← Noise.readMessage b m3
      let (sendA, _) ← Noise.transport a
      let (sendB, _) ← Noise.transport b
      let (_, first) ← Noise.encryptWithAd sendA .empty text
      let (_, back) ← Noise.encryptWithAd sendB .empty text
      if got3 != p3 then throw .identity
      pure [m1, m2, m3, first, back]
    match run with
    | .ok out => " ".intercalate (out.map hex) === want
    | .error _ => failWith s!"EthLib's handshake fails; the reference gives {want}"

/-- The properties of this module that hold. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  let slow := min cases 200
  [("libp2p: a signature is libsecp256k1's", (sign oracle).withTests slow),
   ("libp2p: a changed signature or key", (verify oracle).withTests slow),
   ("libp2p: the peer ID of a key", peerId.withTests (min cases 100)),
   ("noise: the XX handshake is noiseprotocol's", (noise oracle).withTests slow)]

end NetworkingProperty.Identity
