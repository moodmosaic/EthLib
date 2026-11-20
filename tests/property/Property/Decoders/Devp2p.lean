import Hedgehog
import Support
import Property.Decoders.Common
import Property.Decoders.Devp2p.Discv
import Property.Decoders.Devp2p.Enr
import Property.Decoders.Devp2p.Noise
import Property.Decoders.Devp2p.P2p
import Property.Decoders.Devp2p.Rlpx

/-!
# Decoders: devp2p, RLPx, discv5, discv4, the entries of a node record, and Noise

Each module under `Property/Decoders/Devp2p/` gives the properties of one protocol.

The references are in `oracle/decoders_devp2p.py`.
-/

open Hedgehog Support EthLib

namespace DecodersProperty.Devp2p

open DecodersProperty

/-- The properties that must pass. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  P2p.passing oracle cases ++ Rlpx.passing oracle cases ++ Discv.passing oracle cases ++
    Enr.passing oracle cases ++ NoiseId.passing oracle cases

/-- The properties that fail by design: each is a finding. -/
def findings (_oracle : Oracle) (_cases : Nat) : List (String × Property IO) := []

end DecodersProperty.Devp2p
