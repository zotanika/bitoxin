# BITOXIN QA Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans; maintain this checklist.

**Goal:** Rewrite the preemptible QA probe and deliver its evidence-based white paper.
**Architecture:** Shared resumable probe engine, Linux kthread wrapper and portable
pthread runner. The document describes the implemented contracts and test evidence.
**Tech Stack:** C11, Linux Kbuild, ARM64 inline asm, Python/ReportLab.
**Spec:** ../specs/2026-10-05-bitoxin-qa.md

## Global Constraints
Preserve preemption and state across interruption; no PM manipulation. Keep
documentation focused on BITOXIN. No claim of unrun board validation. Use Korean
white paper.

## Review Focus
Zero-index omission; corruption after a bit's visit; partial pass at suspend/stop;
worker startup failure/unload and debugfs lifetime; register constraints and
32-bit arithmetic/invalid sizes. Tests and review must cover these deliberately.

### Task 1: Shared probe and behavioral tests
- [x] Write tests and watch new behavior fail against a skeletal implementation.
- [x] Implement bitoxin_core.h/.c and bitoxin_lane.h with bounded resumable walks.
- [x] Verify native, forced portable, optimized and sanitizer builds.

### Task 2: Linux module and usable host runner
- [x] Test runner argument errors, bounded passes, signal stop and JSON output.
- [x] Replace bitoxin.c; add Kbuild/Makefile and tools/bitoxin-run.c.
- [x] Run ARM64 Linux tests; compile real module headers; record runtime limits.

### Task 3: QA documentation and Korean white paper
- [x] Write README, probe usage guidance, verification evidence and references.
- [x] Create editable white paper source and reproducible PDF renderer.
- [x] Render every page, visually inspect and fix layout; open final PDF.

### Task 4: Review
- [x] Review algorithm, lifecycle, asm, test adequacy and document claims.
- [x] Resolve material issues with regressions and rerun affected/full checks.
- [x] Deliver code and PDF with explicit remaining board-validation boundary.

## Execution record

Native and Linux ARM64 full suites and ASan/UBSan passed. Linux 6.1.0-53
module build with W=1 and ARM64 QEMU guest lifecycle/freezer tests passed.
Independent review found the degree-14 mask problem (also caught locally); it
was fixed and all 22 orders verified. The optional cursor-consistency finding
was fixed with a failing-then-passing regression. No remaining review blockers.

Ruling: preserve existing checkout on a new codex branch; no other repo was
modified. The explicit implementation request authorizes continuous work.
Ruling: generic Linux build plus QEMU freezer tests are delivered; physical PM,
BSP qualification, injected startup failures and panic path remain unrun.
The original white paper was rendered and visually inspected; current page counts
and content follow the maintained source and generated PDF.
