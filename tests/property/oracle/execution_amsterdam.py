"""References for the forks that no release of EELS has: BPO3 to BPO5 and Amsterdam."""

# No release has these forks.
# So the branch `forks/amsterdam` of EELS is installed apart from the released package.
# It is installed at the revision that `requirements-evm.txt` names.
# `ETHLIB_AMSTERDAM_SPECS` names another directory.
#
# The commands are those of `execution.py`, which finds the branch first on the path:
#
#     tx <fork> <chain> <bytes>     A transaction as bytes.
#     txbody <fork> <bytes>         A transaction as an item of a block body.
#     header <fork> <bytes>         A header as bytes.
#     receipt <fork> <bytes>        A receipt as bytes.

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SPECS = os.environ.get("ETHLIB_AMSTERDAM_SPECS", os.path.join(HERE, "..", ".venv", "evm-amsterdam"))
sys.path.insert(0, SPECS)
# The interpreter runs isolated, so the directory of this file is not on the path.
sys.path.insert(0, HERE)

import execution  # noqa: E402

execution.FORKS += ["bpo3", "bpo4", "bpo5", "amsterdam"]

execution.main()
