# English manuscript and reproducibility package

## Manuscript scope

`manuscript.tex` is a complete English methods/tool preprint for arXiv in a standard
10-point, two-column format. It treats BITOXIN as a stateful-testing design concept and the
kernel/user probe as its reference implementation. The scope is BITOXIN's method,
observation behavior, execution interfaces and validation evidence.

The historical motivation couples background scenarios that may activate latent
defects with an interruptible dependent computation that exposes resulting
corruption. The current injection campaign evaluates only the observation side.
The proposed comparative study separates dependency retention and background
scenarios as two experimental factors; no activation benefit is claimed as measured.

Publication author details are awaiting user confirmation. The current anonymous
block is temporary and must be replaced before upload. No author identities,
affiliations, funding, conflicts or historical data are inferred. See
[arXiv preparation](ARXIV.md) for the upload package and form metadata.

The new evidence consists of 61,440 single-bit-injection cases and 120 clean
controls, each run in native ARM64, portable-C and native ASan/UBSan configurations.
The outcomes are identical across builds. Exact enumeration is reported without
statistical confidence intervals or claims about field defect probabilities.
Previous host/Linux/QEMU verification is identified separately from the new
experiment. The production probe was unchanged from commit
`bde601c` while these experiments were performed.

## Reproduce the new evidence

From the repository root, with a C11 compiler and Python 3:

```sh
python3 experiments/run_observability.py
python3 experiments/run_observability.py --portable
python3 experiments/run_observability.py --sanitize
python3 tools/prepare_paper.py
make test
```

On a non-ARM64 machine the native build uses portable C; it must not be reported
as a native ARM64 replication. The first run writes the reference raw data. The
following variants must match its SHA-256 byte for byte. The declared protocol is
`experiments/PROTOCOL.md`; no target board, production service, or PM operation is
used. Output files are deliberately deterministic apart from compiler provenance.

- `data/trials.csv.gz`: one row per trial/control, 61,560 rows plus a header.
- `data/summary.csv`: groups pooled over three seeds and two directions.
- `data/*-summary.json`: build provenance, outcome checks and raw-data hash.
- `data/walk-rows.tex`, `data/scan-rows.tex`, `figures/detection.tex`: generated
  directly from summary data; these are not manually entered measurements.

In `walk_boundary` rows, `following_detected` repeats the current result; no
following-pass observation is performed there. In `scan_boundary` rows it means
cumulative detection by the following pass. `attempts` counts post-injection calls,
including a failing call, and excludes clean-prefix preparation/reconstruction.
A non-detected row has phase `none`; its reported-bit field is not an error address.

## Build and edit

Use Tectonic (tested with 0.16.9):

```sh
tools/build_paper.sh
# If the required TeX resources are already cached:
tools/build_paper.sh --only-cached
```

The script produces `output/pdf/bitoxin-paper-en.pdf` and a standalone LaTeX source
ZIP under `output/paper/`. The ZIP also builds with a conventional LaTeX/BibTeX
workflow using the supplied `.tex` and `.bib` files and TikZ/PGFPlots packages.
Tectonic may download TeX dependencies on an initial build. No network access is
required by the experiments.

## arXiv preparation

The target is an arXiv preprint. Keep the current compact scholarly format; no
conference template or anonymous review mode is needed. The paper preserves its
controlled-experiment scope and distinguishes proposed system campaigns from results.
After confirming publication author details, run:

```sh
tools/build_paper.sh
python3 tools/package_arxiv.py
```

The package contains the article inputs, generated bibliography and a self-contained
`anc/` reproducibility supplement. See [ARXIV.md](ARXIV.md). The final arXiv-rendered
PDF must be checked at upload; the local build is not an arXiv processing result.
No submission or distribution-license selection is performed by these commands.

The article, experiment scripts and editorial work were prepared with AI assistance.
The human author reviews and takes responsibility for the publication. Existing
source notices are preserved. The full repository and local logs need not be
uploaded: the dedicated package contains only the intended source/data subset and
sanitized evidence records.

`output/paper/artifact-manifest.sha256` identifies repository sources, evidence and
article outputs. The arXiv supplement has its own `anc/SHA256SUMS` for the packaged
experiment files.

## Reference verification

Bibliographic metadata and cited claims were checked against primary sources on
2026-10-05: the textbook authors/publisher, author manuscripts, conference publisher,
NIST, official project documentation, GCC, Linux and AMD/Xilinx. See
`reference-audit.md` for source links and claim boundaries. The literature discussion
is targeted positioning, not a systematic literature review.
