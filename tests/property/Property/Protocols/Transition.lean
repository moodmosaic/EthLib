import Property.Protocols.Calls

/-!
# The state transition at every preset

Each call of `Calls.lean` is a property: EthLib and consensus-specs agree on it.

The case draws the preset, the configuration and the fork.

A property labels each case by what EthLib made of it, and by the kind of its preset.

So a report says how many cases changed the state, and at which presets.
-/

open Hedgehog Support EthLib EthLib.Base EthLib.Consensus

namespace ProtocolsProperty

/-- The calls of a list, by name, at a world. -/
abbrev Calls := (world : World) → SignatureChecks → List (Call world.preset)

/-- The names of the calls of a list. -/
def Calls.names (calls : Calls) : List String :=
  (calls (World.ofKeys "minimal" "-") standIn).map (·.name)

/-- The kind of a preset: its name when it is written out, else that it was drawn. -/
def World.kind (world : World) : String :=
  if world.presetKey = "minimal" then "minimal"
  else if world.presetKey = "mainnet" then "mainnet"
  else if world.presetKey = shortMainnet then "mainnet, short vectors"
  else if world.presetKey = oddTime then "odd times"
  else if world.presetKey = oddRewards then "odd rewards"
  else if world.presetKey = oddBalances then "odd balances"
  else if world.presetKey = oddLimits then "odd limits"
  else if world.presetKey = tiny then "tiny"
  else "drawn"

/-- A call agrees with consensus-specs at the worlds given.

`signatures` is `standin` or `real`, and `checks` the checks of EthLib that go with it.

`genWords` describes the states from the shape of the world. -/
def callProperty (oracle : Oracle) (worlds : Gen World) (signatures : String)
    (checks : SignatureChecks) (calls : Calls) (index : Nat)
    (genWords : Shape → Gen (List String)) (between : Bool := false) : Property IO := propertyM do
  let world ← forAllWith World.show worlds
  match (calls world checks)[index]? with
  | none => pure (failWith "the list has no such call")
  | some call =>
    let forks := if between then betweenOf call.forks else call.forks
    let (forkName, fork) ← forAllWith (fun (name, fork) => s!"{name} as {fork.name}")
      (Gen.element (if forks.isEmpty then call.forks else forks))
    let words ← forAllWith " ".intercalate
      ((fun state arguments => state ++ ["|"] ++ arguments) <$> genWords world.shape <*>
        call.arguments)
    pure do
      compare oracle forkName world fork signatures call.name words (call.run fork)
      label s!"preset: {world.kind}"

/-- The properties of a list of calls, each under its name and a suffix. -/
def callProperties (oracle : Oracle) (cases : Nat) (worlds : Gen World) (signatures : String)
    (checks : SignatureChecks) (calls : Calls) (genWords : Shape → Gen (List String))
    (suffix : String := "") (between : Bool := false) : List (String × Property IO) :=
  calls.names.zipIdx.map fun (name, index) =>
    (name ++ suffix,
      (callProperty oracle worlds signatures checks calls index genWords between).withTests
        cases)

end ProtocolsProperty
