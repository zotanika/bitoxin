# Compuon / HESM QA application notes

2026-10-05. These are proposed campaigns, not product validation results.
No referenced project, target board, service, PM setting or production key was
modified or exercised by this rewrite.

## Evidence used

- Requested `../compuon-dev` was not present. The provisional local reference is
  `../compuon/core`, HEAD `517f1a1b1206212bb15355e0731bf2d9fb81de17`.
  Its README describes C++17 static-library backends, `compuon_tests` and
  `compuon_sync_tests`; verify the actual branch before applying these recipes.
- `../../cryptolab/b2c/hesm`, HEAD `d0671cc637d57673516b8141bf7eb82340565073`,
  **dirty working tree** at inspection. README and verification/build notes were
  read from that working tree, not asserted to match the HEAD commit. A35 Linux,
  M33, TF-M, OP-TEE, RPMsg and shared DDR are the relevant boundaries.
- The HESM README explicitly lists USB reset/suspend/hot-unplug and bus-powered
  operation as unvalidated boundaries. A proposed experiment is not evidence that
  any of these features is already supported.

## Campaign design common to both

Run the same product scenario with A: no BITOXIN, B: conventional load at comparable
resource pressure, C: BITOXIN. Hold builds, board revision, PM settings, workload
inputs, temperature/voltage envelope, memory budget and observation duration fixed
where practical. Record differences that cannot be matched. Randomize run order
and repeat on more than one unit when feasible. Small cached and larger working
sets, different pauses and freezer settings are separate experiments, not one score.

Capture unique confirmed defects and first valid failure latency. Preserve no-failure
runs as right-censored observations; do not average only the failing runs. Report
reproduction denominator, completed PM transitions independently measured, overhead,
false reports caused by the test, lost-log/hang counts and root-cause turnaround.
The same seed reproduces a visit order, not thread scheduling or physical timing.

A minimal run record contains:

- product/test build identifiers and dirty state; BSP/kernel config, module hash;
- board ID/revision, CPU/firmware/OP-TEE/TF-M versions where relevant;
- backend, buffer sizes, threads, seeds, chunk, pause, freezer/panic settings;
- monotonic/boottime stamps, boot ID and externally correlated PM/workload events;
- before/after BITOXIN JSON, serial/pstore/kernel logs, product result and expected value;
- result category: complete / interrupted / detected corruption / product failure /
  setup failure / unexplained reset or hang / not run.

`pm_prepare`/`pm_post` are not successful-suspend counters. Require independent PM
traces or target counters. Runtime PM and CPU idle are not covered by those counters.

## Compuon

### Start with a host-side control

Build Compuon in a separate build directory using its documented CMake options;
code generation and fixture configuration must match that checkout. Run its tests
first without BITOXIN. Then run the exact same built test binaries concurrently
with the portable runner on **the same machine**. For example, after successful build:

```sh
# Terminal 1; intentionally runs until signalled.
./build/bitoxin-run --kib 1024 --threads 1 --passes 0 --seed 1 > compuon-probe.json
# Terminal 2; replace with the verified Compuon build directory.
ctest --test-dir /path/to/compuon-build -C Release --output-on-failure
# Stop terminal 1 with Ctrl-C; its expected exit is 130, not a completed-pass result.
```

Both `compuon_tests` and `compuon_sync_tests` should be present in the referenced
checkout. `No tests found` is not success. Preserve product logs separately from
probe status. The runner verifies its own buffer, not Compuon's protected objects.

### Useful extension scenarios

Repeat valid init/use/rotate/shutdown and protocol freshness/rejection checks under
scheduling pressure. Combine validated test vectors and expected rejection outcomes
with pause/resume at supported product boundaries. Keep legitimate integrity
rejection distinct from an environmental bit error, transport failure or race.
Where code generation is seeded, preserve both generator seed and resulting binary.

The Linux module is an additional option for Linux QA hosts. It is not a Windows
or game-runtime integration. The portable backend is not a kernel context-switch
probe. Neither mode establishes anti-cheat strength, secrecy or cryptographic soundness.

## HESM

### A35 Linux is the initial attachment point

Build the module against the exact board BSP, load it on the A35 Linux side, and
run the existing host -> USB CDC-NCM -> gateway -> RPMsg/shared DDR -> M33/TF-M
known-answer transaction scenario. If testing the current kms-tee branch, separately
label the local REE -> OP-TEE TA -> M33 key-custody path; it is not the same route.

Use existing public fixtures/test keys and the repository's provisioning rules.
Do not create a test that bypasses secure-memory boundaries or treats BITOXIN
buffer success as evidence about TF-M secure RAM.

Recommended initial matrix:

| Lane | Scenario | Required independent observation |
|---|---|---|
| Host control | Existing native/sanitizer/portability gates | Existing gate status and hashes |
| Board baseline | Repeated documented fixture transactions | Plaintext/KAT comparison and timeout/recovery |
| Board + probe | Same scenario with one small A35 worker | Probe JSON, product result, CPU/memory overhead |
| PM exploration | Board-supported suspend/resume with retained probe | Actual PM state/counters plus pre/post results |
| Transport exploration | Supported USB reconnect/reset and RPMsg recovery | Link/service recovery and transaction identity |
| Custody branch | Supported key lifecycle with public test keys | Existing custody assertions; branch-specific evidence |

Start with 64 KiB or 1 MiB and one worker; tune using actual free RAM, latency and
PM residency rather than assuming the largest allocation is best. A 1 ms pause
per 4096 operations is a separate duty-cycle lane. Full system suspend support
must be established on that BSP before interpreting failures as new defects.

The module's vmalloc allocation is private kernel memory and is not user swap
traffic. It does not traverse the HESM shared window or secure memory automatically.
If faults are suspected at those boundaries, retain product transaction-level
oracles and instrument those owners; do not have BITOXIN overwrite their buffers.

## Evaluation boundary

Host/QEMU tests prove selected software behavior and ISA execution. Only actual
board runs can evaluate power sequencing, cache coherency across this SoC, DDR
retention, clock gating and firmware interactions. Record these as NOT_RUN until
measured. Fix a discovered product bug and repeat the same campaign to show the
failure disappeared; use more than crash counts to attribute causality.
