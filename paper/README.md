# English manuscript and reproducibility package

## Manuscript scope

`manuscript.tex` is a complete English methods/tool manuscript in a neutral
10-point, two-column format. It treats BITOXIN as a QA design concept and the
kernel/user probe as one reference implementation. Product adoption does not
require a Linux module. The protected-value and transaction-service examples
are proposed adaptations, not evaluated case studies.

The author block and PDF metadata are anonymous. This is not a claim that the
project name or the entire repository is unidentifiable under every venue's
anonymity rules. No author names, affiliations, funding, conflicts, public archive
URL, or historical experimental data have been invented.

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

## Submission preparation

A venue has not been selected. The current evidence is best framed as a bounded
method/tool contribution with controlled observability experiments. The paper
explicitly avoids claiming a new foundational testing theory or demonstrated
improvement in real product defect discovery. A full empirical effectiveness claim
would require a product-level comparative study and meaningful external baselines.

Before an actual submission, select the venue and article category, use its exact
template/page limit, and supply author/affiliation and required declarations.
Check that venue's anonymity and AI-assistance disclosure rules. This manuscript,
experiment harness and editorial work were prepared with AI assistance; the human
authors must review and take responsibility for the work and use the venue's
required disclosure wording. No disclosure policy has been assumed or fabricated.

For artifact review, create a suitable archive and persistent identifier if the
venue requests one. The manuscript currently says only that a local artifact
accompanies it. Existing source attribution and licenses must be retained; the
repository and its old logs contain identities and local paths, so do not upload
it as an anonymous artifact without a separate, policy-appropriate preparation.
The manuscript source ZIP contains only the article's editable inputs.
`output/paper/artifact-manifest.sha256` binds the source, data, earlier verification
logs and final article outputs; `output/pdf/source-manifest.sha256` is refreshed
for the current repository sources as part of the paper build.

## Reference verification

Bibliographic metadata and cited claims were checked against primary sources on
2026-10-05: the textbook authors/publisher, author manuscripts, conference publisher,
NIST, official project documentation, GCC, Linux and AMD/Xilinx. See
`reference-audit.md` for source links and claim boundaries. The literature discussion
is targeted positioning, not a systematic literature review.
