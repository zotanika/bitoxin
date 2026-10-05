# Verification record - BITOXIN 2

Date: 2026-10-05. Baseline: `53203f75ab0362924f21299af56ceacc0d1d86b1`.
The rewrite is on `codex/bitoxin-qa-rewrite`. See the source manifest beside the
white paper for the exact delivered inputs; a baseline hash does not identify
uncommitted rewritten bytes.

Preserved evidence: `output/verification/native.log`, `sanitizers.log`,
`linux-arm64.log`, `guest-arm64.log`, `linux-versions.txt` and `host-versions.txt`.
The separate `output/pdf/source-manifest.sha256` identifies source/document inputs.

## Observed during development

1. The first core test failed against the skeletal engine before implementation.
2. The runner tests failed against its skeletal implementation (bounded completion,
   arguments and signal behavior), then passed after implementation.
3. A full-order LFSR test exposed legacy degree-14 `0x201d` as non-maximal.
   An independent reviewer reproduced a 2 KiB false failure after 126 operations.
   It was replaced with `0x3802`; all 22 orders (degrees 9..30) now pass.
4. Native ARM64 macOS optimized C/asm tests and forced portable-C tests passed.
5. Native ASan/UBSan tests passed; this does not instrument instructions inside asm.
6. Linux ARM64 GCC expanded tests, sanitizers and Linux 6.1.0-53-arm64 module build
   with W=1 passed.
7. QEMU ARM64, two Cortex-A53 vCPUs and a Linux 6.1.0-53 guest: invalid-size
   rejection, two workers completing two 2-KiB passes, freezer participation of
   completed and active workers, retained active cursors, PM notifications, active
   unload and five repeated non-freezable four-worker load/unload cycles passed.
   The PM test used pm_test=freezer: **no physical sleep was exercised**.
   Guest result: BITOXIN_GUEST_ALL_PASS. Startup allocation/thread-creation failure
   injection and the actual panic path remain unexecuted.

## Behavioral checks

- LFSR full cycle/closure, explicit bit zero, uniform end states and inverse pass.
- Chunked continuation vs uninterrupted passes without buffer reinitialization.
- Unexpected bit before visit, corruption after visit found by whole-buffer scan.
- Opposite-polarity corruption; first failure stays latched without further writes.
- Corrupted zero LFSR/cursor/non-closing state and invalid size/seed inputs.
- Linear-map exponentiation and factor tests establish maximum order for all masks.
- 10,128 lane input patterns (single bits, complements and varied full-width words).
- Simulated register output corruption is detected before a buffer write.
- Runner validates arguments/allocation cap, exact pass counts, independent workers,
  and distinguishes signal interruption from completed passes; 2 KiB seed wrap
  and corrupted verifier cursor also have regressions.

The register fault test substitutes only the lane in a test translation unit; it
is an oracle test, not a physical fault-injection result. No production corruption
injection switch is present.

## What is not established

No Compuon test suite or HESM board scenario has been run in this task. No real
suspend/resume, runtime PM, clock gating, DDR retention, hardware bit flip,
vendor BSP reproduction or security certification is established. Compilation
against generic Linux headers is not target-BSP qualification. A test failure
can originate in the probe, kernel, hardware or environment; attribution needs
reproduction and independent evidence.

## Reproduction

`make test`, `make sanitize`, and the Docker commands in README reproduce the
available software checks. `tools/Dockerfile.verify` uses Debian package versions
available at build time; preserve image IDs/package versions for exact repeats.
`tools/Dockerfile.guest` and `tools/verify-guest.sh` reproduce the disposable
virtual-kernel lifecycle/freezer checks. Neither command loads a module into the
host kernel or runs a PM operation on the physical machine.

## English manuscript observability campaign (2026-10-05)

The production engine remains unchanged. `experiments/PROTOCOL.md` specifies the
new fault model, boundaries, controls and analytical expectations. The executable
harness enumerated 61,440 injected trials and 120 clean controls per configuration.
Native ARM64, forced portable C and native ASan/UBSan produced byte-identical raw
CSV data (SHA-256 `de12c6ba7a3981253e949af7bc1d451e10f2afbbe26787ca3a075af8ecd35fc0`).
The existing `make test` suite also passed after adding the experiment tools.

Retained walk plus scan detected all 15,360 assigned walk-boundary faults; walk-only
detected 7,680/15,360; reinitialization/replay detected 0/15,360. The additional
15,360 scan-boundary faults include errors behind the verification cursor that
miss the current pass but are detected by the following retained pass. All 120
clean controls completed without a mismatch. These are enumerated software cases,
not estimates of physical fault coverage or independent statistical samples.
Data, build provenance, generated tables and paper reproduction instructions are
in `paper/`. No new product or hardware campaign was performed.
