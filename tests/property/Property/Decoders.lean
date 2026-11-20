import Hedgehog
import Support
import Property.Decoders.Devp2p
import Property.Decoders.Libp2p
import Property.Decoders.Protobuf
import Property.Decoders.Quic
import Property.Decoders.Snappy
import Property.Decoders.Tls

/-!
# The decoders and codecs of the networking layer, on generated inputs

    lake exe decoders-property            # 100 cases of each
    lake exe decoders-property 1000
    HEDGEHOG_ONLY=quic lake exe decoders-property 1000

Each module under `Property/Decoders/` gives the properties of one family of codecs.

The answers come from `oracle/decoders.py`: the `protobuf` package, aioquic, `cryptography`.

Where no package reads a format, the reference is a reader written from the text of the format.
-/

open Hedgehog Support

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "decoders"
  let selection ← Selection.fromEnv
  let ok ← checkGroup "decoders" (DecodersProperty.Protobuf.passing oracle cases ++
    DecodersProperty.Quic.passing oracle cases ++
    DecodersProperty.Tls.passing oracle cases ++
    DecodersProperty.Libp2p.passing oracle cases ++
    DecodersProperty.Devp2p.passing oracle cases ++
    DecodersProperty.Snappy.passing oracle cases) selection
  -- Each property of this group states what EthLib does not do, and must fail.
  let found ← checkGroup "decoders: findings" (DecodersProperty.Protobuf.findings oracle cases ++
    DecodersProperty.Quic.findings oracle cases ++
    DecodersProperty.Tls.findings oracle cases ++
    DecodersProperty.Libp2p.findings oracle cases ++
    DecodersProperty.Devp2p.findings oracle cases ++
    DecodersProperty.Snappy.findings oracle cases) selection (mustFail := true)
  pure (if ok && found then 0 else 1)
