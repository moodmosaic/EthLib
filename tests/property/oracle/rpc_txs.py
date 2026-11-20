"""Signed transactions for the RPC oracle, built with the classes of EELS and coincurve."""

# A transaction is sixteen fields joined with `,`:
#     type,key,chain,nonce,gas price,priority fee,max fee,gas,to,value,data,
#     access list,max blob fee,blob hashes,authorizations,signature
# The key is the index of a sender.  A legacy transaction with chain 0 signs no chain.
# An access list is `address:key.key` entries joined with `/`.
# An authorization is `chain:address:nonce:key:fault`, and they are joined with `/`.
# The signature is 0, or 1 for the high `s` with the parity turned, or 2 for an `r` of 0.

import importlib

import coincurve
from ethereum.crypto.hash import keccak256
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes0, Bytes20, Bytes32
from ethereum_types.numeric import U8, U64, U256, Uint

# The latest fork has every type of transaction, and the bytes of a type are those of any fork.
LATEST = "osaka"
TX = importlib.import_module("ethereum.forks." + LATEST + ".transactions")
TYPES = importlib.import_module("ethereum.forks." + LATEST + ".fork_types")

ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

# The secret keys of the senders and of the authorities.
KEYS = [keccak256(b"transition sender %d" % i) for i in range(8)]


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def address_of(index):
    """The address of a key."""
    public = coincurve.PrivateKey(KEYS[index]).public_key.format(compressed=False)
    return keccak256(public[1:])[12:]


def sign(index, digest, fault=0):
    """The parity, `r` and `s` of a signature, with a fault if one is asked."""
    signature = coincurve.PrivateKey(KEYS[index]).sign_recoverable(digest, hasher=None)
    r = int.from_bytes(signature[:32], "big")
    s = int.from_bytes(signature[32:64], "big")
    parity = signature[64]
    if fault == 1:
        return 1 - parity, r, ORDER - s
    if fault == 2:
        return parity, 0, s
    return parity, r, s


def access_list(word):
    if word == "-":
        return ()
    entries = []
    for entry in word.split("/"):
        address, keys = entry.split(":")
        slots = tuple(Bytes32(bytes.fromhex(k)) for k in keys.split(".") if k)
        entries.append(TX.Access(account=Bytes20(bytes.fromhex(address)), slots=slots))
    return tuple(entries)


def authorizations(word):
    if word == "-":
        return ()
    made = []
    for entry in word.split("/"):
        chain, address, nonce, key, fault = entry.split(":")
        address = Bytes20(bytes.fromhex(address))
        message = rlp.encode((U256(int(chain)), address, U64(int(nonce))))
        parity, r, s = sign(int(key), keccak256(b"\x05" + message), int(fault))
        made.append(
            TYPES.Authorization(
                chain_id=U256(int(chain)),
                address=address,
                nonce=U64(int(nonce)),
                y_parity=U8(parity),
                r=U256(r),
                s=U256(s),
            )
        )
    return tuple(made)


def make(spec):
    """The bytes of the signed transaction of a specification, as a block holds a typed one."""
    (
        kind,
        key,
        chain,
        nonce,
        gas_price,
        priority,
        max_fee,
        gas,
        to,
        value,
        data,
        accesses,
        blob_fee,
        blobs,
        auths,
        fault,
    ) = spec.split(",")
    key, chain, fault = int(key), int(chain), int(fault)
    common = {
        "nonce": U256(int(nonce)),
        "gas": Uint(int(gas)),
        "to": Bytes0(b"") if to == "-" else Bytes20(bytes.fromhex(to)),
        "value": U256(int(value)),
        "data": unhex(data),
    }
    blank = {"r": U256(0), "s": U256(0)}
    if kind == "0":
        tx = TX.LegacyTransaction(gas_price=Uint(int(gas_price)), v=U256(0), **common, **blank)
        if chain == 0:
            parity, r, s = sign(key, TX.signing_hash_pre155(tx), fault)
            v = 27 + parity
        else:
            parity, r, s = sign(key, TX.signing_hash_155(tx, U64(chain)), fault)
            v = 35 + 2 * chain + parity
        signed = TX.LegacyTransaction(
            gas_price=tx.gas_price, v=U256(v), r=U256(r), s=U256(s), **common
        )
        return rlp.encode(signed)
    typed = {"chain_id": U64(chain), "access_list": access_list(accesses), **common}
    fees = {
        "max_priority_fee_per_gas": Uint(int(priority)),
        "max_fee_per_gas": Uint(int(max_fee)),
    }
    if kind == "1":
        cls, hasher = TX.AccessListTransaction, TX.signing_hash_2930
        fields = {"gas_price": Uint(int(gas_price)), **typed}
    elif kind == "2":
        cls, hasher = TX.FeeMarketTransaction, TX.signing_hash_1559
        fields = {**fees, **typed}
    elif kind == "3":
        cls, hasher = TX.BlobTransaction, TX.signing_hash_4844
        hashes = tuple(Bytes32(bytes.fromhex(h)) for h in blobs.split(".")) if blobs != "-" else ()
        fields = {
            "max_fee_per_blob_gas": U256(int(blob_fee)),
            "blob_versioned_hashes": hashes,
            **fees,
            **typed,
        }
    else:
        cls, hasher = TX.SetCodeTransaction, TX.signing_hash_7702
        fields = {"authorizations": authorizations(auths), **fees, **typed}
        fields["nonce"] = U64(int(nonce))
    parity, r, s = sign(key, hasher(cls(y_parity=U256(0), **fields, **blank)), fault)
    signed = cls(y_parity=U256(parity), r=U256(r), s=U256(s), **fields)
    return bytes([int(kind)]) + rlp.encode(signed)
