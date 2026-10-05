# BITOXIN reproducibility supplement

This directory accompanies the preprint's controlled observability experiments.
The production core is the measured implementation. The paper distinguishes
measured observation behavior from proposed system campaigns.

## Run

From this directory, with Python 3 and a C11 compiler:

```sh
python3 experiments/run_observability.py
python3 experiments/run_observability.py --portable
python3 experiments/run_observability.py --sanitize
```

The first command writes native data; the subsequent configurations must match
its raw CSV SHA-256. On a non-ARM64 host, native defaults to portable C and must
not be reported as a native ARM64 replication. Sanitizers depend on compiler
support. No network, root privilege, physical power operation or kernel module
is needed. Each run executes 61,440 fault injections and 120 clean controls.

`experiments/PROTOCOL.md` specifies boundaries, policies and expected counts.
`paper/data/trials.csv.gz` contains the original 61,560 result rows plus a header;
`paper/data/*-summary.json` records compiler provenance and outcome hashes.
`evidence/` contains earlier host/Linux/virtual-kernel logs, not newly rerun
hardware experiments. Those additional wrapper tests need the complete BITOXIN
repository and are not reproduced by the three commands above.

The protocol has one persistent buffer-bit flip between operations. It does not
simulate arbitrary hardware faults or establish natural-defect discovery rates.
`following_detected` in walk-boundary rows repeats `current_detected`; in
scan-boundary rows it is cumulative detection by the following pass. `attempts`
counts post-injection calls, including a failure, and excludes prefix setup.

`SHA256SUMS` identifies the supplied files before rerunning scripts. The C sources
are GPL-2.0-or-later, as their SPDX notices state; GPL version 2 is in `COPYING`.
The source notices and license are preserved. This license notice does not choose
an arXiv distribution license for the article on the author's behalf.
