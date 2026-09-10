# Peterson's algorithm in Lean

This repository is a source-guided study of the mutual-exclusion algorithms in
Gary L. Peterson's 1981 paper,
[“Myths about the mutual exclusion problem”](https://doi.org/10.1016/0020-0190%2881%2990106-X).
It contains Lean
models and proofs for the paper's two-process algorithm, both for one passage
and for repeated requests, and for the paper's finite n-process construction.

Mutual exclusion means that distinct processes never occupy their critical
sections together. The proofs make every shared read and write a separate
atomic step under sequential consistency, so they account for interleavings
between the two reads in the two-process waiting test. They cover both fixed
read orders used uniformly by the processes.

## Checked results

The public claim contract names six result families:

- [`Peterson.peterson_mutual_exclusion`](Peterson/Safety.lean): one-passage
  safety for two processes, with either initial `turn` value.
- [`Peterson.peterson_global_progress`](Peterson/Progress.lean): a pending
  one-passage request leads to some new entry under explicit protocol fairness
  and critical-work completion premises.
- [`Peterson.Repeated.repeated_mutual_exclusion`](Peterson/Repeated/Safety.lean):
  safety across arbitrarily many requests and private restarts.
- [`Peterson.Repeated.repeated_request_entry`](Peterson/Repeated/Progress.lean):
  every repeated request reaches its own entry under the same two kinds of
  liveness premise.
- [`Peterson.NProcess.arbitrary_mutual_exclusion`](Peterson/NProcessCapacity.lean),
  supported by [`level_capacity`](Peterson/NProcessCapacity.lean): one-passage
  safety for every finite process count at least two, using individually atomic
  ascending peer scans.
- [`Peterson.Repeated.repeated_overtaking_bound`](Peterson/Repeated/Overtaking.lean),
  its zero-before-`turn`, after-`turn`, and bounded-service refinements, and the
  universal sharpness witness
  [`repeated_overtaking_sharp`](Peterson/Repeated/OvertakingExamples.lean): a
  repeated request can be overtaken by at most one peer entry; zero occur before
  its `turn` write, and one is attainable for every reviewed parameter choice.

Safety claims require no fairness. Progress and bounded service require weak
fairness for continuously enabled protocol work plus eventual completion by a
critical-section occupant. The overtaking count is an entry count, not a time,
step, or read bound. The n-process result makes no progress or repeated-use
claim. None of the results establishes weak-memory correctness or refinement
to compiled code.

## Reading path

[The algorithm and models](docs/algorithm.md) relates the program counters and
events to the source algorithms. [The proof guide](docs/proofs.md) explains the
six results and why their assumptions differ. [Verification](docs/verification.md)
gives build and theorem-inspection commands. [Related work](docs/related-work.md)
records the narrow library and comparison work.

The reconstruction used an author-marked electronic restoration of the paper;
identity with the publisher's version has not been established. The paper,
images, and transcriptions are not redistributed here.

## Building

With `elan` installed, run from the repository root:

```sh
lake build Peterson.Verification Peterson.NProcessVerification
```

The project pins Lean `v4.34.0-rc2`, CSLib, Mathlib, and the full transitive
dependency graph. [STATUS.md](STATUS.md) distinguishes prior development checks
from qualification of a particular exported tree.

## AI assistance

Erik Peterson initiated and directed this project. The research, prose,
tooling, and Lean proofs are model-generated. Lean checked the proofs, and
separate AI agents reviewed each model and theorem boundary against the source.
Those reviews are fallible and can share errors. Lean's acceptance establishes
the encoded propositions, not historical source faithfulness. There has been
no independent human mathematical review.

Licensed under [MIT](LICENSE).
