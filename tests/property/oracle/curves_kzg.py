"""KZG references: c-kzg-4844, on the trusted setup that EthLib embeds."""

# A blob, a cell, a commitment and a proof are hexadecimal bytes.
# A list is its items joined by `;`, or `[]`.
# Long answers are their SHA-256.

import hashlib
import os
import re
import tempfile

import ckzg

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "../../../EthLib/Cryptography/Kzg/TrustedSetupData.lean")

_setup = None


def setup():
    """The setup of `TrustedSetupData.lean`, in the file format of c-kzg-4844."""
    global _setup
    if _setup is None:
        with open(DATA) as source:
            points = re.findall(r'"([0-9a-f]+)"', source.read())
        g1 = [point for point in points if len(point) == 96]
        g2 = [point for point in points if len(point) == 192]
        assert len(g1) == 8192 and len(g2) == 65, "unexpected setup data"
        lines = ["4096", "65", *g1[:4096], *g2, *g1[4096:]]
        with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as out:
            out.write("\n".join(lines) + "\n")
        _setup = ckzg.load_trusted_setup(out.name, 0)
        os.unlink(out.name)
    return _setup


def unhex(word):
    return b"" if word == "-" else bytes.fromhex(word)


def items(word):
    return [] if word == "[]" else [unhex(item) for item in word.split(";")]


def digest(parts):
    return hashlib.sha256(b"".join(parts)).hexdigest()


def guarded(run):
    try:
        return run()
    except Exception:
        return "error"


def answer(words):
    ts = setup
    match words:
        case ["kzgcommit", blob]:
            return guarded(lambda: ckzg.blob_to_kzg_commitment(unhex(blob), ts()).hex())
        case ["versionedhash", commitment]:
            # EIP-4844, Helpers: `VERSIONED_HASH_VERSION_KZG + sha256(commitment)[1:]`.
            return (b"\x01" + hashlib.sha256(unhex(commitment)).digest()[1:]).hex()
        case ["kzgproof", blob, z]:
            return guarded(
                lambda: " ".join(
                    part.hex() for part in ckzg.compute_kzg_proof(unhex(blob), unhex(z), ts())
                )
            )
        case ["kzgblobproof", blob, commitment]:
            return guarded(
                lambda: ckzg.compute_blob_kzg_proof(unhex(blob), unhex(commitment), ts()).hex()
            )
        case ["kzgverify", commitment, z, y, proof]:
            return guarded(
                lambda: str(
                    int(
                        ckzg.verify_kzg_proof(
                            unhex(commitment), unhex(z), unhex(y), unhex(proof), ts()
                        )
                    )
                )
            )
        case ["kzgverifyblob", blob, commitment, proof]:
            return guarded(
                lambda: str(
                    int(
                        ckzg.verify_blob_kzg_proof(
                            unhex(blob), unhex(commitment), unhex(proof), ts()
                        )
                    )
                )
            )
        case ["kzgverifybatch", blobs, commitments, proofs]:
            return guarded(
                lambda: str(
                    int(
                        ckzg.verify_blob_kzg_proof_batch(
                            b"".join(items(blobs)),
                            b"".join(items(commitments)),
                            b"".join(items(proofs)),
                            ts(),
                        )
                    )
                )
            )
        case ["kzgcells", blob]:

            def run():
                cells, proofs = ckzg.compute_cells_and_kzg_proofs(unhex(blob), ts())
                assert cells == ckzg.compute_cells(unhex(blob), ts())
                return digest(cells) + " " + digest(proofs)

            return guarded(run)
        case ["kzgrecover", indices, cells]:

            def run():
                wanted = [] if indices == "[]" else [int(i) for i in indices.split(";")]
                cells_out, proofs = ckzg.recover_cells_and_kzg_proofs(wanted, items(cells), ts())
                return digest(cells_out) + " " + digest(proofs)

            return guarded(run)
        case ["kzgverifycells", commitments, indices, cells, proofs]:

            def run():
                wanted = [] if indices == "[]" else [int(i) for i in indices.split(";")]
                return str(
                    int(
                        ckzg.verify_cell_kzg_proof_batch(
                            items(commitments), wanted, items(cells), items(proofs), ts()
                        )
                    )
                )

            return guarded(run)
    return None
