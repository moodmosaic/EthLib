"""Pure helpers of the pyspec: one command, one answer."""

# lc_better <fork> <new hex> <old hex>   is_better_update of two LightClientUpdates.
# custody <node id> <count>              get_custody_groups, or error.
# columns <group>                        compute_columns_for_custody_group, or error.
# att_subnet <per slot> <slot> <index>   compute_subnet_for_attestation.
# col_subnet <column>                    compute_subnet_for_data_column_sidecar.
# subscribed <node id> <epoch>           compute_subscribed_subnets.

import importlib

SPECS = {}


def spec_of(fork):
    if fork not in SPECS:
        SPECS[fork] = importlib.import_module(f"eth_consensus_specs.{fork}.minimal")
    return SPECS[fork]


def numbers(values):
    return ",".join(str(int(v)) for v in values) or "-"


def answer(words):
    try:
        match words:
            case ["lc_better", fork, new, old]:
                spec = spec_of(fork)
                decode = spec.LightClientUpdate.decode_bytes
                better = spec.is_better_update(
                    decode(bytes.fromhex(new)), decode(bytes.fromhex(old))
                )
                return "true" if better else "false"
            case ["custody", node_id, count]:
                spec = spec_of("fulu")
                return numbers(spec.get_custody_groups(int(node_id), int(count)))
            case ["columns", group]:
                spec = spec_of("fulu")
                assert int(group) < spec.config.NUMBER_OF_CUSTODY_GROUPS
                return numbers(spec.compute_columns_for_custody_group(int(group)))
            case ["att_subnet", per_slot, slot, index]:
                spec = spec_of("fulu")
                subnet = spec.compute_subnet_for_attestation(
                    spec.Uint64(int(per_slot)),
                    spec.Slot(int(slot)),
                    spec.CommitteeIndex(int(index)),
                )
                return str(int(subnet))
            case ["col_subnet", column]:
                spec = spec_of("fulu")
                return str(int(spec.compute_subnet_for_data_column_sidecar(int(column))))
            case ["subscribed", node_id, epoch]:
                spec = spec_of("fulu")
                return numbers(spec.compute_subscribed_subnets(int(node_id), int(epoch)))
    except Exception as error:
        return f"error {type(error).__name__}"
    return "error unknown command"
