# Reference audit (2026-10-05)

This local editorial record is not part of the anonymous manuscript source ZIP.
No references are inferred from titles alone; summaries are limited to the
accessible primary-source descriptions/materials. Some direct PDF retrievals
failed; their successfully retrieved author/publisher records were used instead.

| BibTeX key | Primary source checked | Supported use |
|---|---|---|
| ammann2017 | https://www.albany.edu/faculty/offutt/softwaretest/ and https://assets.cambridge.org/97811071/72012/frontmatter/9781107172012_frontmatter.pdf (indexed publisher content), textbook slides indexed at https://www.cs.cornell.edu/courses/cs5154/2021sp/resources/TestingConcepts-1.pdf | Edition 2, copyright 2017, DOI; RIPR terms and separation of fault activation from observation. Direct PDF opens timed out. |
| chen2018 | https://nottingham-repository.worktribe.com/output/925152/metamorphic-testing-a-review-of-challenges-and-opportunities (indexed author repository record) | Authors, ACM CSUR 51(1), article 4, 2018, DOI; relations among inputs and outputs. The article pagination 4:1-4:27 is also in the indexed author manuscript metadata. |
| wei2011 | https://arxiv.org/abs/1108.1068 | Author manuscript, inferred-contract testing; ASE 2011 journal reference 440-443 and related DOI. No borrowed effectiveness figure is used. |
| hypothesis | https://hypothesis.readthedocs.io/en/latest/stateful.html | Action sequences, bundles, models and invariants; documentation, not a peer-reviewed result. |
| chess2008 | https://www.usenix.org/conference/osdi-08/finding-and-reproducing-heisenbugs-concurrent-programs and https://www.microsoft.com/en-us/research/?p=156206 | Author list and OSDI 2008 venue; systematic schedule exploration and reproduction. |
| kuhn2012 | https://www.nist.gov/publications/combinatorial-methods-event-sequence-testing | Author list, ICST 2012 and DOI; t-way event orders. |
| stressapptest | https://github.com/stressapptest/stressapptest | Project's memory/I/O traffic and integrity-checking design; no comparative measurement is claimed. |
| dixit2022 | https://arxiv.org/abs/2203.08989 | Author preprint, silent corruption, in/out-of-production detection strategies. It is explicitly cited as arXiv, not assigned an unverified venue. |
| gcc | https://gcc.gnu.org/onlinedocs/gcc/Extended-Asm.html | Compiler input/output/clobber contract. |
| linuxfreezer | https://docs.kernel.org/power/freezing-of-tasks.html | Freezable tasks and retained execution; no hardware sleep assertion from notifications. |
| alfke1996 | https://docs.amd.com/v/u/en-US/xapp052 | XAPP052 title/date and LFSR background. The engine's masks are independently tested rather than attributed to that note's convention. |

Compuon and HESM are deliberately presented as general application designs in the
paper, not as public empirical datasets or citeable validation results. Their
local-code motivation remains documented in `docs/qa-applications.md`.
