import Hedgehog
import Support
import Property.Decoders.Common
import Property.Decoders.Libp2p.Certificate
import Property.Decoders.Libp2p.Frames
import Property.Decoders.Libp2p.Negotiation
import Property.Decoders.Libp2p.Signature

/-!
# Decoders: libp2p

The certificate of libp2p TLS, multistream-select, and the byte codecs of yamux and mplex.

Each module under `Property/Decoders/Libp2p/` gives the properties of one of them.
-/

open Hedgehog Support EthLib

namespace DecodersProperty.Libp2p

open DecodersProperty

/-- The properties that must pass. -/
def passing (oracle : Oracle) (cases : Nat) : List (String × Property IO) :=
  Certificate.passing oracle cases ++ Signature.passing oracle cases ++
    Frames.passing oracle cases ++ Negotiation.passing cases

/-- The properties that fail by design: each is a finding. -/
def findings (_oracle : Oracle) (_cases : Nat) : List (String × Property IO) := []

end DecodersProperty.Libp2p
