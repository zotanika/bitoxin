# Applying the BITOXIN concept to product QA

2026-10-05. These are design proposals, not implemented integrations or measured
product results. The intended reuse is the **test design concept**: carry real
product state through dependent operations and permitted interruptions, then make
incorrect state observable against an independent expectation. Linux modules,
LFSRs, register assembly and a separate stress process are not prerequisites.
The code in this repository is a reference realization for system-state probing.

## A reusable test structure

1. Start with a known product state and a separately computed reference state.
2. Generate a sequence of operations allowed by the product contract. The actual
   product output/state feeds the next product operation; the reference model
   independently applies the same intended operation. Never repair actual state
   from the reference or update the reference from an unchecked actual result.
3. Keep state alive across selected scheduling, ownership, session or transport
   boundaries. PM is one possible boundary, not the definition of this method.
4. Compare intermediate checkpoints and the final state. Check identity, lifetime
   and expected rejection outcomes as well as numeric values. Latch the first
   mismatch with the seed, operation index, inputs and transition trace.
5. Use controlled test faults to establish which errors reach those checks.
   A passing fault-free sequence alone does not demonstrate detection ability.

A small harness needs an operation generator, a product adapter, an independent
reference model, a boundary/event controller and a failure trace. A seeded generator
helps reproduce the operation sequence; scheduling needs its own event record.
An LFSR could order inputs but does not establish operation-sequence coverage.

Do not reset the object after every step or serialize the whole scenario behind
one test lock. Equally, do not interpret unsupported concurrent mutation as a
product defect: perturb execution only within the synchronization contract, and
model intentionally invalid operations as explicit expected rejections.

Identity/round-trip relations are useful checks, but are not a complete oracle.
Multiplication by zero can erase an earlier error; inverse operations can cancel
correlated faults. Use varied, nondegenerate operands and intermediate checks.
An ordinary assertion or typed error is sufficient: crash is not required.

## Compuon: carry the protected value and its lifecycle

The requested `../compuon-dev` is absent. The provisional reference is
`../compuon/core`, HEAD `517f1a1b1206212bb15355e0731bf2d9fb81de17`.
Inspect the intended checkout before implementation. Relevant existing tests are:

- `tests/test_compuon_deferred.cpp`: arithmetic, copy/move and independent copies;
  deferred reads verify through the session key rather than a plaintext cache.
- `tests/test_identity_arithmetic.cpp`: zero identities and identity folds.
- `tests/test_api_lifecycle.cpp`: init/rekey/shutdown, backend cleanup and preserving
  the gated operand profile across rekey.
- `tests/test_sync_protocol.cpp`: protocol freshness/session behavior.

Build a longer sequence from these operations, retaining actual protected objects:

```text
protected x = 37; independent reference r = 37
x += 11; r += 11
copy x to y; independently copy r to s
[permitted scheduling boundary]
y *= 3; s *= 3
x -= 5; r -= 5
verify protected x == 43, protected y == 144, and copy independence
continue from these objects; do not reconstruct them from expected values
```

Use bounded integer operands and an independently implemented reference to avoid
undefined overflow or mirroring the product's bug. For a backend with a plaintext
cache, checking only that cache does not exercise protected-state verification;
select the backend's actual verification interface. Record protection-disabled
builds separately from protected builds.

Add lifecycle operations according to the documented contract. Do not assume old
handles remain usable after rekey/shutdown. Where they are invalidated, check that
rejection and create the next generation explicitly; where preservation is promised,
continue checking the retained state. Keep positive controls that would fail if all
operations were disabled. Existing zero-identity tests remain useful for their
specific purpose, but a zero-only stress chain can mask state errors.

First implementation target: extend the existing test harness with a seeded,
bounded operation sequence and an independent value/lifetime model. No kernel
module or product runtime hook is implied by this proposal.

## HESM: preserve request, buffer and result correspondence

Reference: `../../cryptolab/b2c/hesm`, HEAD
`d0671cc637d57673516b8141bf7eb82340565073`, with a **dirty working tree** at
inspection. Read files describe more than that commit alone can reproduce.
Relevant evidence is in `tests/session_test.c`, `tests/shared_window_test.c`,
`tests/ckks_v2l1w_service_test.c`, `tests/ckks_v2l1w_kernel_test.c`,
`tests/ckks_v2l1w_tools_test.py` and `include/hesm/tfm_ops.h`.

The existing session fixture already connects BEGIN, WRITE_REF/WRITE, EXECUTE
and READ. For example, its known `abcdef` input returns `fedcba`; another test
mixes WRITE_REF and WRITE under one input tag. Extend this connected path:

```text
known request/input + independent expected result
  -> BEGIN -> WRITE_REF / WRITE -> EXECUTE -> READ
  -> check request identity, status, output length and expected bytes
  -> next request with distinct data, retaining service and buffer history
```

Vary legal fragmentation, descriptor offsets, buffer reuse and ownership handoffs.
Preserve the service/session state between transactions so stale output or stale
lengths can be detected. Distinct adjacent inputs help expose accidental reuse.
Use an explicit state-machine model for negative sequences: a refused operation
must have the specified status and specified effect on the live request. Delays,
retries, aborts and reconnects need contract-specific expectations, not an assumption
that every interruption must succeed transparently. USB suspend/reset/hot-unplug
listed as unvalidated in project docs remain exploratory cases.

Use the existing public fixtures and test-key/provisioning rules for the crypto
path. Compare deterministic coefficient/byte fixtures exactly; compare approximate
CKKS decoded values with the profile's defined tolerance and scale. A self-consistent
round trip alone can miss two implementations sharing the same error, so retain
known-answer fixtures or an independent reference. A key lifecycle test should
model the active key generation and the documented LOAD/REVOKE outcomes; this
proposal does not establish persistence or revocation behavior across power loss.

Shared-window fault injection belongs in a test-owned buffer or explicit test
interface, at defined ownership points. The useful dependency is from actual input
and session metadata through execution to the matching response. It does not require
arbitrary access to secure RAM, nor a separate private-memory probe on A35.

First implementation target: extend the host session fixture into multiple linked
transactions with a state-machine oracle, then apply the same contract checks to
the real transport and crypto profiles. Simulator evidence does not establish board
cache coherency, power sequencing or DDR retention.

## Measure the concept's contribution

Compare A: independent short cases, B: linked stateful cases, C: linked cases with
permitted event perturbations and checkpoints. Match operation counts, operation
mix, resource budget and observation time where practical; report unmatched costs.
Do not count a longer test's additional operations as evidence for dependency alone.
Known injected faults measure detectability under that model, not field bug frequency.

Preserve product/build identifiers and dirty state, generator and fixture seeds,
operation/event traces, configuration, expected/actual results and the first failing
step. Minimize a failing sequence while retaining the state history needed for
reproduction. Count unique confirmed defects, false reports, first valid failure
latency, overhead and reproduction denominators. Keep no-failure runs in the data.
Fix a confirmed defect and rerun the sequence to validate the attribution.

No Compuon/HESM files, services, boards or keys were changed or exercised here.
These application designs are separate from the reference probe's validation log.
