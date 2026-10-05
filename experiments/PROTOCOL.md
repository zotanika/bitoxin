# Controlled observability experiment protocol

Defined on 2026-10-05 before executing the new experiment. The production probe
is unchanged. This is an enumerated software fault model, not a hardware campaign
or a comparison against other test tools.

## Fixed design

Use the shared C engine with a 64-byte buffer (512 bits), seeds 1, 17 and 255,
and both pass directions. These seeds are phases of the same LFSR cycle, not
independent random samples. Execute with a budget of one probe operation per call.
Inject exactly one persistent XOR bit flip at a call boundary. The harness and
control state are trusted. No additional faults occur during a trial.

Experiment 1 enumerates all 512 target bits after k = 0, 128, 256, 384, 512
completed bit visits. Apply three observation policies to separate fresh trials:
(a) retain and complete walk plus scan; (b) retain but stop before the scan;
(c) discard the corrupted state, reconstruct the clean prefix, then complete
walk plus scan. Policy (c) models reinitialization/replay, not a competing tool.
The third policy's reconstruction overhead is not counted as detection latency.
Each policy has 15,360 injections; also run one no-fault control per combination
of policy, seed, direction and boundary (90 controls).

Experiment 2 enumerates all target bits after q = 0, 16, 32, 48, 63 bytes of the
verification scan. Retain state and record detection by the current pass boundary
and, if not detected, by the following pass boundary. This is 15,360 injections
and 30 no-fault controls. It tests the finite observation horizon explicitly.

## Outcomes and validation

Raw rows record experiment, policy, seed, direction, boundary, injected bit
(-1 for a clean control), detection by the current horizon, detection by the next
horizon, phase, reported bit and number of post-injection run calls attempted.
A failing run call counts as one attempted operation; counts are not elapsed time.
Unexpected non-data failures or a bounded loop overrun fail the experiment.

Analytical expectations, specified before running: for each 512-bit group,
retained walk+scan detects 512 faults; walk-only detects 512-k; reconstruction
detects none. During the scan, the current horizon detects 512-8q faults and the
next horizon detects all 512. Clean controls detect none. These expectations are
conditional on the stated model and can be disproved by executing the real engine.

Report exact enumeration counts, not inferential p-values or confidence intervals.
These are correlated finite cases, not random samples of field defects. They do
not measure real scheduling, PM, hardware failure rate or time-to-bug improvement.
Native ARM64, portable C and sanitizer runs must yield identical outcome rows.
