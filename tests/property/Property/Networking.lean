import Hedgehog
import Support
import Property.Networking.Codecs
import Property.Networking.Gossip
import Property.Networking.Identity
import Property.Networking.Records
import Property.Networking.Router
import Property.Networking.Snappy
import Property.Networking.Streams
import Property.Networking.Wire

/-!
# The networking layer, on generated inputs

    lake exe networking-property            # 100 cases of each
    lake exe networking-property 2000

Each module under `Property/Networking/` gives the properties of one part of the layer.

The answers come from three places:

- `oracle/networking.py`.
- Models written from the sources.
- State machines.
-/

open Hedgehog Support

def main (args : List String) : IO UInt32 := do
  let cases := casesOf args
  let oracle ← Oracle.start "networking"
  let selection ← Selection.fromEnv
  let ok ← checkGroup "networking" (NetworkingProperty.Snappy.passing oracle cases ++
    NetworkingProperty.Codecs.passing oracle cases ++
    NetworkingProperty.Records.passing oracle cases ++
    NetworkingProperty.Wire.passing oracle cases ++
    NetworkingProperty.Gossip.passing oracle cases ++
    NetworkingProperty.Identity.passing oracle cases ++
    NetworkingProperty.Streams.passing cases ++
    NetworkingProperty.Router.passing cases) selection
  -- Each property of this group disagrees with a reference, and must fail.
  --
  -- Its report is the evidence.
  let findings ← checkGroup "networking: findings"
    (NetworkingProperty.Snappy.findings oracle cases ++ NetworkingProperty.Gossip.findings oracle)
    selection (mustFail := true)
  pure (if ok && findings then 0 else 1)
