# arXiv submission package

Target: an arXiv preprint, not an anonymous conference submission.

## Files

- `output/paper/bitoxin-arxiv-draft.zip`: optional draft package for review and local verification.
- `output/paper/bitoxin-arxiv-upload.zip`: article source, bibliography and
  ancillary reproducibility files. The manuscript specifies Sunchul Jung as the author.
- `output/pdf/bitoxin-paper-en.pdf`: locally checked reading copy. The PDF built
  by arXiv must also be inspected during submission.
- `output/paper/arxiv-metadata.json`: title, plain-text abstract and suggested
  category for the submission form. It does not select a distribution license
  or assert a journal reference, DOI, or existing arXiv identifier.

The source uses the standard `article` class and single spacing. No conference
format or special arXiv template is required by this package. `manuscript.tex`
is the top-level file. `manuscript.bbl` is supplied alongside `references.bib`.
The source uses standard TeX packages and no shell-escape or system font paths.
The local build uses Tectonic; arXiv's server-side rendering is a separate check.

Suggested primary category: **cs.SE (Software Engineering)**, based on the
paper's focus on testing and QA design. No cross-list category is preselected.
The category is a recommendation, not a moderation outcome.

## Reproducibility attachment

The `anc/` directory contains the reference core, controlled-injection harness,
protocol, compressed trial data and summaries, reproduction instructions and
hashes. Its paths are self-contained. No proprietary product source, account
information, local absolute paths or unrelated workspace files are included.
The C sources retain their GPL-2.0-or-later notices; GPL version 2 is included.

The new observability experiment can be rerun from that directory with Python 3
and a C11 compiler. Existing host/Linux/QEMU evidence is included as sanitized
text records, distinguished from the directly reproducible injection campaign.
Sanitizing replaces the original machine's workspace prefix with `<workspace>`
and removes terminal display escape sequences; it does not alter test counts
or outcomes. The full repository is not needed to
reproduce the new campaign, and no Linux module is loaded by that campaign.

## Metadata still supplied by the author

The publication author is Sunchul Jung. Affiliation and email have not been
specified; email is optional. The upload builder rejects anonymous/empty authors by
default; its `--draft` switch is only for local package verification and writes
an explicitly named draft ZIP. No draft package should be uploaded as a finished
submission. A distribution license is chosen by the submitting author in arXiv;
this preparation does not make that choice or submit the paper.

The text and experiment scripts were prepared with AI assistance. Quantitative
claims were checked against executed experiments and recorded data. The author
should review the complete preprint and take responsibility for its contents.

## Official references checked on 2026-10-05

- [TeX submission and bibliography files](https://info.arxiv.org/help/submit_tex.html)
- [Ancillary data and code](https://info.arxiv.org/help/ancillary_files.html)
- [Supported TeX processors](https://info.arxiv.org/help/faq/texlive.html)
- [Category definitions](https://arxiv.org/category_taxonomy)
- [Submission overview](https://info.arxiv.org/help/submit/index.html)

The official system currently accepts `.bib` or a matching pre-generated `.bbl`;
this package supplies both. At upload, use a supported LaTeX processor such as
XeLaTeX (closest to the local Tectonic build) and verify the generated preview.
No acceptance, endorsement status or server-side compilation result is claimed.
