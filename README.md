# BITOXIN 2

A preemptible state-integrity probe to run **alongside** QA workloads and
sleep/wakeup scenarios. It keeps a known computation and its memory alive across
interruptions, then reports observed corruption. It does not manipulate power
sequencing, prove hardware health, or locate the original cause by itself.

The author's 2018 use involved independent Linux kernel threads, including a
reported near-100% reproduction of a vendor BSP paging/PM issue. That is a
historical recollection, not a measured result of this rewrite.

## Reusing the concept

For Compuon and HESM, the intended application is to carry **product state** through
linked operations and lifecycle boundaries, with an independent expected result
and checkpoints that expose corruption. It does not require deploying this Linux
module or running this probe beside the product. The implementations below are
reference examples for system-state integrity; see [product QA design](docs/qa-applications.md)
for concrete adaptations. Those product integrations have not been implemented.

## What changed

- Persistent per-worker buffers; LFSR bit traversal includes bit zero explicitly.
- Both 1 -> 0 and 0 -> 1 passes, followed by whole-buffer verification.
- ARM64 GPR dependency chain with complete compiler constraints; no IRQ or
  preemption disabling around the probe, no deliberate invalid-pointer store.
- First probe failure is latched; workers stop and report details. Kernel panic
  is an explicit, off-by-default option.
- Load-time configuration, bounded memory, cooperative freezer support,
  debugfs snapshots and clean thread shutdown.
- A shared C engine with native/sanitizer tests and a portable pthread runner.
- Corrected the legacy degree-14 LFSR mask (0x201d had period 126 in this
  convention). All 22 supported masks have independently checked maximal order.

This replaces the old `mode=burst/hook/mixed` control and hook exports. The new
module is **bitoxin_qa.ko**. The old source remains in Git history.

## Host build and test

```sh
make
make test
make sanitize
./build/bitoxin-run --kib 1024 --threads 2 --passes 2 --seed 1
```

Options: `--kib` per worker (power of two, 1..131072), `--threads` (1..32),
`--passes` (0 = until signal, default 2), `--seed` (nonzero, below buffer bit
count), `--chunk` (1..65536, default 4096), `--pause-ms` (0..1000, default 0).
Total buffer allocation is limited to 256 MiB. Adjacent workers receive adjacent
nonzero seeds; these are phases of one LFSR cycle, not independent random streams.

One directional pass includes a bit walk **and** the final byte verification.
Two passes restore all bytes to 0xff. Each pass costs 9 x buffer_bytes probe
operations, excluding initialization/control work. A chunk is an operation budget,
not an atomic section or a scheduler guarantee.

The runner prints one final JSON record. Exit codes: 0 completed requested passes,
1 probe failure, 2 invalid arguments, 3 setup failure, 130 interrupted. An interrupted
run can have useful observations but is not a completed pass. `--passes 0` is
intended for parallel QA campaigns; stop with SIGINT/SIGTERM and preserve its JSON.
A process-level checker on another machine does not check the target's memory.

On ARM64 the backend is `aarch64-gpr`. Elsewhere it is `portable-c`, which checks
algorithm semantics and memory data, without claiming equivalent GPR coverage.
The user runner does not lock or pin memory; unlike vmalloc-backed kernel memory,
its pages can participate in ordinary user-space paging when the OS allows it.

## Linux kernel module

Build **against the target BSP's configured kernel build tree** and its matching
toolchain. The implemented APIs are verified against Linux 6.1 ARM64 headers;
that does not promise compatibility with every vendor kernel or old 2018 BSP.
`CONFIG_MODULES` and `CONFIG_DEBUG_FS` are required. Kernel preemption settings
and the surrounding context determine where involuntary preemption can happen.

```sh
make module KDIR=/path/to/target/kernel/build
# Cross-build example: make module KDIR=... ARCH=arm64 CROSS_COMPILE=aarch64-linux-gnu-
sudo insmod bitoxin_qa.ko mem_kib=1024 threads=2 seed=1 passes=0
sudo cat /sys/kernel/debug/bitoxin/status
# Run the approved QA workload / sleep-wakeup campaign in parallel.
sudo cat /sys/kernel/debug/bitoxin/status > bitoxin-final.json
sudo rmmod bitoxin_qa
```

Mount debugfs if it is not already mounted; the module creates `bitoxin/status`
there but does not mount it. No runtime-writable module controls are exposed;
unload/reload to change configuration. Capture status **before** unloading.

| Module parameter | Default | Meaning |
|---|---:|---|
| `threads` | 1 | 1..32 independent buffer owners |
| `mem_kib` | 1024 | Power-of-two KiB per worker, max 128 MiB each / 256 MiB total |
| `seed` | 1 | First worker's LFSR seed; reproducible traversal, not scheduling |
| `passes` | 0 | Verified directional passes; 0 continues until error/unload |
| `chunk` | 4096 | Operations between status/stop/freezer checks, max 65536 |
| `pause_ms` | 0 | Optional pause after each chunk, max 1000 ms |
| `freezable` | 1 | Cooperate with system suspend; retain buffer and cursor |
| `panic_on_error` | 0 | If 1, log first failure then panic for external QA detection |

The default freezer participation is deliberate: system suspend can freeze the
worker before device suspend and thaw it after resume. This preserves data across
the transition but does **not** execute the GPR chain while a CPU is powered off.
`freezable=0` permits a separate non-freezable-thread experiment; it changes PM
interaction and can change reproducibility. Keep this setting in evidence and
compare it explicitly with the old workload rather than assuming equivalence.

`pm_prepare` / `pm_post` count system suspend/hibernation notifications. A prepare
can be aborted; a matched pair does not prove a hardware sleep state was reached.
They do not count runtime PM or CPU-idle transitions. Pair status snapshots with
board PM traces/counters and workload outcomes. Snapshots are per-worker coherent,
not a simultaneous global snapshot.

Errors identify worker, seed, completed passes, walk/verify phase, buffer bit
index (byte start during verification), expected and observed values. A panic can
still lose logs without serial/pstore/watchdog capture. Crashes of the checker,
unexpected reboots and hangs also require an external observer.

## Validation and application

- [Verification record](docs/verification.md): actual checks and remaining limits.
- [QA applications](docs/qa-applications.md): Compuon and HESM campaign design.
- [White paper source](docs/whitepaper.ko.md) and [PDF](output/pdf/bitoxin-whitepaper-ko.pdf).

Reproduce Linux compile/tests using `tools/Dockerfile.verify` and
`tools/verify-linux.sh`. These use a disposable build tree and read-only source:

```sh
docker build --platform linux/arm64 -t bitoxin-verify:local -f tools/Dockerfile.verify .
docker run --rm --platform linux/arm64 --network none -v "$PWD:/src:ro" \
  bitoxin-verify:local /src/tools/verify-linux.sh
```

Package versions are recorded in the verification evidence; the Dockerfile is a
convenient environment recipe, not an immutable dependency lock.

The optional virtual-kernel runtime check uses a disposable ARM64 QEMU guest:

```sh
docker build --platform linux/arm64 -t bitoxin-guest:local -f tools/Dockerfile.guest .
docker run --rm --platform linux/arm64 --network none -v "$PWD:/src:ro" \
  bitoxin-guest:local /src/tools/verify-guest.sh
```

This checks module lifecycle and `pm_test=freezer`, not actual hardware sleep.
Rebuild the PDF with `python3 tools/build_whitepaper.py` in a Python environment
with ReportLab installed. On macOS it embeds the existing AppleGothic TrueType
font; elsewhere set `BITOXIN_KOREAN_FONT` to a Korean-capable TrueType font.

## Limits

LFSR coverage is coverage of **test-buffer bit indices**, not SoC state space,
all instruction n-grams, DRAM cells, page-table states or execution schedules.
Cache hits may never reach DRAM. The verifier can itself be corrupted; errors may
be masked, occur after verification, or affect untested state. No failure observed
is not a reliability certificate. This is not a cryptographic RNG, security proof,
Rowhammer tool, fault-location system, or a replacement for product-specific tests.

License: GPL-2.0-or-later, preserving the original project's license.
