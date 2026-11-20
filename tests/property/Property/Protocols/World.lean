import Property.Protocols.Names

/-!
# The preset and the configuration of a test case

The earlier drivers ran the state transition at the minimal preset only.

Mainnet and minimal agree on many values, so a definition that reads the wrong one passes at both.

`MAX_EFFECTIVE_BALANCE` and `MIN_ACTIVATION_BALANCE` are 32 ETH in both, for one.

So a case here draws its preset: minimal, mainnet, or one whose values differ from both.

The oracle builds consensus-specs with the same values, see `oracle/protocols_spec.py`.

A configuration is drawn for each case, since the oracle sets it without building anything.
-/

open Hedgehog Support EthLib EthLib.Consensus

namespace ProtocolsProperty

/-- The preset and the configuration of a case, with the words that name them to the oracle. -/
structure World where
  /-- The preset as the oracle takes it: `minimal` or `mainnet`, then `;NAME=value` for each. -/
  presetKey : String
  /-- The configuration as the oracle takes it: `-`, or `NAME=value;...`. -/
  configKey : String
  /-- The preset. -/
  preset : Preset
  /-- The configuration. -/
  config : Config

/-- The pairs of a key: `NAME=value` separated by `;`. -/
def pairsOf (key : String) : List (String × Nat) :=
  (key.splitOn ";").filterMap fun word =>
    match word.splitOn "=" with
    | [name, value] => value.toNat?.map (name, ·)
    | _ => none

/-- The world of two keys. -/
def World.ofKeys (presetKey configKey : String) : World :=
  let mainnet := presetKey.startsWith "mainnet"
  let preset := (pairsOf presetKey).foldl (fun p (name, value) => setPreset p name value)
    (if mainnet then Preset.mainnet else Preset.minimal)
  let config := (pairsOf configKey).foldl (fun c (name, value) => setConfig c name value)
    (if mainnet then Config.mainnet else Config.minimal)
  ⟨presetKey, configKey, preset, config⟩

/-- The two keys as one text, for a report. -/
def World.show (world : World) : String := s!"{world.presetKey} {world.configKey}"

/-- A key from pairs. -/
def keyOf (base : String) (pairs : List (String × Nat)) : String :=
  ";".intercalate (base :: pairs.map fun (name, value) => s!"{name}={value}")

/-- Mainnet with short vectors of roots, mixes and slashings.

The whole mainnet state is three megabytes, which is slow to send for every case.

Every value that is no length of a vector is that of mainnet. -/
def shortMainnet : String :=
  keyOf "mainnet" [("SLOTS_PER_HISTORICAL_ROOT", 256), ("EPOCHS_PER_HISTORICAL_VECTOR", 128),
    ("EPOCHS_PER_SLASHINGS_VECTOR", 64)]

/-- Values that are odd, not powers of two, and differ wherever two presets agree. -/
def oddTime : String :=
  keyOf "minimal" [("SLOTS_PER_EPOCH", 6), ("SLOTS_PER_HISTORICAL_ROOT", 48),
    ("SHUFFLE_ROUND_COUNT", 1), ("TARGET_COMMITTEE_SIZE", 3), ("MAX_COMMITTEES_PER_SLOT", 5),
    ("SYNC_COMMITTEE_SIZE", 12), ("EPOCHS_PER_SYNC_COMMITTEE_PERIOD", 3),
    ("MIN_SEED_LOOKAHEAD", 2), ("MAX_SEED_LOOKAHEAD", 3), ("EPOCHS_PER_ETH1_VOTING_PERIOD", 3),
    ("EPOCHS_PER_HISTORICAL_VECTOR", 24), ("EPOCHS_PER_SLASHINGS_VECTOR", 10),
    ("MIN_EPOCHS_TO_INACTIVITY_PENALTY", 2), ("PTC_SIZE", 6),
    ("INCLUSION_LIST_COMMITTEE_SIZE", 5), ("MIN_ATTESTATION_INCLUSION_DELAY", 2)]

/-- Every quotient and multiplier of rewards and penalties a different prime.

A definition that reads the value of another fork, or another quotient, then differs. -/
def oddRewards : String :=
  keyOf "minimal" [("HYSTERESIS_QUOTIENT", 5), ("HYSTERESIS_DOWNWARD_MULTIPLIER", 2),
    ("HYSTERESIS_UPWARD_MULTIPLIER", 7), ("BASE_REWARD_FACTOR", 53),
    ("WHISTLEBLOWER_REWARD_QUOTIENT", 101), ("PROPOSER_REWARD_QUOTIENT", 5),
    ("INACTIVITY_PENALTY_QUOTIENT", 1000003), ("MIN_SLASHING_PENALTY_QUOTIENT", 7),
    ("PROPORTIONAL_SLASHING_MULTIPLIER", 5), ("INACTIVITY_PENALTY_QUOTIENT_ALTAIR", 2000003),
    ("MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR", 11), ("PROPORTIONAL_SLASHING_MULTIPLIER_ALTAIR", 6),
    ("INACTIVITY_PENALTY_QUOTIENT_BELLATRIX", 3000017),
    ("MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX", 13),
    ("PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX", 4),
    ("MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA", 17), ("WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA", 19)]

/-- The balances that mainnet and minimal set equal, each its own value. -/
def oddBalances : String :=
  keyOf "minimal" [("MIN_DEPOSIT_AMOUNT", 3000000000), ("MAX_EFFECTIVE_BALANCE", 30000000000),
    ("EFFECTIVE_BALANCE_INCREMENT", 2000000000), ("MIN_ACTIVATION_BALANCE", 34000000000),
    ("MAX_EFFECTIVE_BALANCE_ELECTRA", 100000000000)]

/-- Every limit of a list or of a sweep small and odd, so that a case reaches it. -/
def oddLimits : String :=
  keyOf "minimal" [("MAX_VALIDATORS_PER_COMMITTEE", 130), ("VALIDATOR_REGISTRY_LIMIT", 1000),
    ("HISTORICAL_ROOTS_LIMIT", 1000), ("MAX_PROPOSER_SLASHINGS", 3),
    ("MAX_ATTESTER_SLASHINGS", 3), ("MAX_ATTESTATIONS", 5), ("MAX_DEPOSITS", 3),
    ("MAX_VOLUNTARY_EXITS", 5), ("MAX_BLS_TO_EXECUTION_CHANGES", 3),
    ("MAX_WITHDRAWALS_PER_PAYLOAD", 3), ("MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP", 5),
    ("PENDING_DEPOSITS_LIMIT", 1000), ("PENDING_PARTIAL_WITHDRAWALS_LIMIT", 10),
    ("PENDING_CONSOLIDATIONS_LIMIT", 6), ("MAX_ATTESTER_SLASHINGS_ELECTRA", 2),
    ("MAX_ATTESTATIONS_ELECTRA", 3), ("MAX_DEPOSIT_REQUESTS_PER_PAYLOAD", 5),
    ("MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD", 3), ("MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD", 3),
    ("MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP", 3), ("MAX_PENDING_DEPOSITS_PER_EPOCH", 3),
    ("MAX_PAYLOAD_ATTESTATIONS", 2), ("MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD", 3),
    ("MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD", 3), ("MAX_BUILDERS_PER_WITHDRAWALS_SWEEP", 3)]

/-- The shortest epoch and the smallest committees, with the shuffle of mainnet. -/
def tiny : String :=
  keyOf "minimal" [("SLOTS_PER_EPOCH", 2), ("SLOTS_PER_HISTORICAL_ROOT", 16),
    ("SHUFFLE_ROUND_COUNT", 90), ("TARGET_COMMITTEE_SIZE", 1), ("MAX_COMMITTEES_PER_SLOT", 64),
    ("SYNC_COMMITTEE_SIZE", 4), ("EPOCHS_PER_SYNC_COMMITTEE_PERIOD", 1), ("PTC_SIZE", 2),
    ("EPOCHS_PER_ETH1_VOTING_PERIOD", 1), ("EPOCHS_PER_HISTORICAL_VECTOR", 8),
    ("EPOCHS_PER_SLASHINGS_VECTOR", 4), ("MAX_SEED_LOOKAHEAD", 1),
    ("MIN_EPOCHS_TO_INACTIVITY_PENALTY", 1), ("INCLUSION_LIST_COMMITTEE_SIZE", 1)]

/-- The presets that are written out. -/
def namedPresets : List String :=
  ["minimal", shortMainnet, oddTime, oddRewards, oddBalances, oddLimits, tiny]

/-- A preset with values drawn within what the specification assumes of them.

The roots of an epoch divide those of the state, and the sync committee has four subnets.

The mixes outlast the lookahead.

The oracle builds consensus-specs for each such preset, which takes about a second.

`variants` bounds how many a run meets. -/
def genDrawnPreset (variants : Nat) : Gen String := do
  -- One number fixes the whole preset, so that a run meets a bounded set of them.
  let seed ← Gen.nat (.constant 0 (variants - 1))
  let pick (salt : Nat) (choices : List Nat) : Nat :=
    choices.getD ((seed * 2654435761 + salt * 40503) / 7 % choices.length) 0
  let slots := pick 1 [2, 3, 4, 5, 8, 12, 16, 32]
  let lookahead := pick 2 [1, 1, 2, 3]
  pure (keyOf (if seed % 2 = 0 then "minimal" else shortMainnet) [
    ("SLOTS_PER_EPOCH", slots),
    ("SLOTS_PER_HISTORICAL_ROOT", slots * pick 3 [4, 5, 8, 16]),
    ("SHUFFLE_ROUND_COUNT", pick 4 [0, 1, 2, 9, 10, 11, 89, 90, 91, 200, 255]),
    ("TARGET_COMMITTEE_SIZE", pick 5 [1, 2, 3, 4, 7, 128]),
    ("MAX_COMMITTEES_PER_SLOT", pick 6 [1, 2, 3, 4, 7, 64]),
    ("SYNC_COMMITTEE_SIZE", 4 * pick 7 [1, 2, 3, 5, 8, 16]),
    ("EPOCHS_PER_SYNC_COMMITTEE_PERIOD", pick 8 [1, 2, 3, 5, 8, 256]),
    ("MIN_SEED_LOOKAHEAD", lookahead),
    ("MAX_SEED_LOOKAHEAD", lookahead + pick 9 [0, 1, 3, 4]),
    ("EPOCHS_PER_ETH1_VOTING_PERIOD", pick 10 [1, 2, 3, 4, 64]),
    ("EPOCHS_PER_HISTORICAL_VECTOR", pick 11 [16, 21, 64, 100]),
    ("EPOCHS_PER_SLASHINGS_VECTOR", pick 12 [2, 5, 8, 64]),
    ("MIN_EPOCHS_TO_INACTIVITY_PENALTY", pick 13 [1, 2, 4, 7]),
    ("MIN_ATTESTATION_INCLUSION_DELAY", pick 14 [1, 1, 2, 3]),
    ("PTC_SIZE", pick 15 [1, 2, 3, 5, 16, 512]),
    ("INCLUSION_LIST_COMMITTEE_SIZE", pick 16 [1, 2, 3, 16]),
    ("HYSTERESIS_QUOTIENT", pick 17 [1, 2, 4, 5, 10]),
    ("HYSTERESIS_DOWNWARD_MULTIPLIER", pick 18 [0, 1, 2, 3]),
    ("HYSTERESIS_UPWARD_MULTIPLIER", pick 19 [1, 4, 5, 6, 9]),
    ("BASE_REWARD_FACTOR", pick 20 [1, 32, 64, 65, 1000]),
    ("WHISTLEBLOWER_REWARD_QUOTIENT", pick 21 [1, 2, 512, 4096]),
    ("PROPOSER_REWARD_QUOTIENT", pick 22 [1, 2, 8, 9]),
    ("MAX_WITHDRAWALS_PER_PAYLOAD", pick 23 [2, 3, 4, 5, 16]),
    ("MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP", pick 24 [1, 2, 7, 16, 16384]),
    ("MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP", pick 25 [1, 2, 3, 8]),
    ("MAX_PENDING_DEPOSITS_PER_EPOCH", pick 26 [1, 2, 5, 16]),
    ("MAX_BUILDERS_PER_WITHDRAWALS_SWEEP", pick 27 [1, 2, 3, 16]),
    ("MIN_ACTIVATION_BALANCE", 1000000000 * pick 28 [32, 32, 31, 33, 16]),
    ("MAX_EFFECTIVE_BALANCE", 1000000000 * pick 29 [32, 32, 31, 33, 40]),
    ("MAX_EFFECTIVE_BALANCE_ELECTRA", 1000000000 * pick 30 [2048, 64, 100, 2047]),
    ("PROPORTIONAL_SLASHING_MULTIPLIER", pick 31 [1, 2, 3, 5]),
    ("PROPORTIONAL_SLASHING_MULTIPLIER_ALTAIR", pick 32 [1, 2, 3, 5]),
    ("PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX", pick 33 [1, 2, 3, 5]),
    ("MIN_SLASHING_PENALTY_QUOTIENT", pick 34 [1, 32, 64, 128]),
    ("MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR", pick 35 [1, 32, 64, 128]),
    ("MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX", pick 36 [1, 32, 64, 128]),
    ("MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA", pick 37 [1, 32, 4096, 128]),
    ("WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA", pick 38 [1, 2, 512, 4096])])

/-- A preset: mostly one that is written out, sometimes a drawn one. -/
def genPresetKey (variants : Nat := 24) : Gen String :=
  Gen.frequency [(5, Gen.element namedPresets), (1, genDrawnPreset variants)]

/-- A value of a configuration, as `NAME=value`. -/
def genConfigPair (name : String) (gen : Gen Nat) : Gen String :=
  (fun value => s!"{name}={value}") <$> gen

/-- An amount of Gwei of a churn limit. -/
def genChurnGwei : Gen Nat :=
  Gen.frequency [(3, (· * 1000000000) <$> Gen.nat (.linear 1 300)),
    (1, Gen.nat (.linear 1 (300 * 1000000000)))]

/-- The values of a configuration that the state transition reads, each with a generator. -/
def configValues : List (Gen String) := [
  genConfigPair "MIN_VALIDATOR_WITHDRAWABILITY_DELAY" (Gen.nat (.linear 0 300)),
  genConfigPair "SHARD_COMMITTEE_PERIOD" (Gen.nat (.linear 0 300)),
  genConfigPair "EJECTION_BALANCE" ((· * 1000000000) <$> Gen.nat (.linear 0 40)),
  genConfigPair "MIN_PER_EPOCH_CHURN_LIMIT" (Gen.nat (.linear 1 9)),
  genConfigPair "CHURN_LIMIT_QUOTIENT" (Gen.element [1, 2, 3, 5, 8, 32, 65536]),
  genConfigPair "MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT" (Gen.nat (.linear 1 16)),
  genConfigPair "MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA" genChurnGwei,
  genConfigPair "MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT" genChurnGwei,
  genConfigPair "CHURN_LIMIT_QUOTIENT_GLOAS" (Gen.element [1, 2, 3, 5, 8, 16, 32768]),
  genConfigPair "CONSOLIDATION_CHURN_LIMIT_QUOTIENT" (Gen.element [1, 2, 3, 5, 8, 32, 65536]),
  genConfigPair "MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS" genChurnGwei,
  genConfigPair "INACTIVITY_SCORE_BIAS" (Gen.nat (.linear 1 9)),
  genConfigPair "INACTIVITY_SCORE_RECOVERY_RATE" (Gen.nat (.linear 0 33)),
  genConfigPair "MIN_BUILDER_WITHDRAWABILITY_DELAY" (Gen.nat (.linear 0 300)),
  genConfigPair "SLOT_DURATION_MS" (Gen.element [1000, 2000, 6000, 12000, 12500]),
  genConfigPair "MAX_BLOBS_PER_BLOCK" (Gen.nat (.linear 0 12)),
  genConfigPair "MAX_BLOBS_PER_BLOCK_ELECTRA" (Gen.nat (.linear 0 12)),
  genConfigPair "GENESIS_FORK_VERSION" (Gen.nat (.linear 0 0xFFFFFFFF)),
  genConfigPair "CAPELLA_FORK_VERSION" (Gen.nat (.linear 0 0xFFFFFFFF)),
  genConfigPair "DENEB_FORK_VERSION" (Gen.nat (.linear 0 0xFFFFFFFF))]

/-- The first epoch of each fork: the genesis mostly, sometimes later or never.

Both named configurations leave the forks from Gloas in the far future.

The committees of Gloas are refused before the epoch of the fork, so a case needs it reached. -/
def forkEpochs : List (Gen String) :=
  ["ALTAIR", "BELLATRIX", "CAPELLA", "DENEB", "ELECTRA", "FULU", "GLOAS", "HEZE"].map fun name =>
    genConfigPair s!"{name}_FORK_EPOCH" (Gen.frequency [(6, pure 0), (1, Gen.nat (.linear 0 40)),
      (1, pure (2 ^ 64 - 1))])

/-- A configuration: that of the preset, or with a few values of its own.

Three of four have the epochs of the forks set. -/
def genConfigKey : Gen String := do
  let values ← Gen.frequency [
    (2, pure []),
    (3, do Gen.sequence (← Gen.subsequence configValues))]
  let epochs ← Gen.frequency [(1, pure []), (3, Gen.sequence forkEpochs forkEpochs.length)]
  let pairs := values ++ epochs
  pure (if pairs.isEmpty then "-" else ";".intercalate pairs)

/-- A world: a preset and a configuration. -/
def genWorld (variants : Nat := 24) : Gen World :=
  World.ofKeys <$> genPresetKey variants <*> genConfigKey

end ProtocolsProperty
