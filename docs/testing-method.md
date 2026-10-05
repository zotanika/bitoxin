# BITOXIN testing method

BITOXIN retains known state across dependent computation and permitted execution
interruptions. Its reference probe reads and checks buffer bits, carries the
actual loaded data through a register transformation, writes the inverted bit,
and verifies the whole buffer before continuing with the opposite polarity.
The same buffer survives between chunks and passes.

## Activation and observation

Background workloads and sleep/wakeup scenarios may bring a system into conditions
that activate a latent defect. BITOXIN checks whether resulting corruption reaches
an observation. More activity is not automatically better: it may prevent entry
into the low-power state of interest. Record reached conditions separately from
requested transitions. A PM notification pair does not prove physical sleep.

Preemption remains permitted. A chunk limits work between control checks; it does
not make the computation atomic or reproduce a particular execution schedule.
A traversal seed reproduces buffer order, not event timing.

## Preserve evidence in the probe

- Retain the buffer and cursors across interruptions; do not repair them from
  expected values before checking them.
- Carry actual loaded data into the register check and subsequent write.
- Check visited bits and the final buffer. A fault behind the advancing verifier
  can escape the current pass, so the observation horizon must be explicit.
- Latch the first mismatch and preserve worker identity, seed, phase, progress,
  expected value and observed value.
- Use an external supervisor for hangs, resets and lost logs. Preserve run and
  boot identifiers where possible; an unexpected restart alone does not identify
  corruption as its cause.

## Measured observation experiment

The campaign in `experiments/PROTOCOL.md` enumerates 61,440 single-bit injections
and 120 clean controls per build configuration. It compares retained state plus
a final scan, retained state without the scan, and clean-state reconstruction.
It also injects faults behind an advancing scan and observes the following pass.
These finite cases establish specified observation behavior, not physical fault
activation rates or a speedup in discovering natural defects.

See [verification evidence](verification.md) and the
[English manuscript](../paper/README.md) for results and reproduction instructions.

## Proposed system campaign

Cross two factors: retaining probe state across a selected event boundary versus
reinitializing it, and baseline conditions versus a defined background or
transition scenario. This separates state retention from background activity and
allows their interaction to be examined. The reinitializing variant is an
experimental comparator; it is not a runtime option in the shipped probe.

Match operation count and mix, resource budget, and observation duration where
possible. Record initialization costs separately. Preserve build identifiers,
configuration, traversal seeds, event traces, status snapshots and transition
measurements. Record valid detection latency, confirmed root causes, false
reports, overhead and reproduction denominators, including runs without failures.
Retain the state-establishing prefix when minimizing a failing scenario and
confirm attribution by rerunning after the responsible defect is fixed.

This comparative system campaign has not been performed. Existing freezer tests
and software injections do not establish hardware power-sequence coverage.
