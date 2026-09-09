# Peterson's algorithm in Lean

This is a study and Lean proofs of Gary L. Peterson's 1981 paper,
[“Myths about the mutual exclusion problem”](https://doi.org/10.1016/0020-0190%2881%2990106-X).
The repository contains a formal model of its two-process algorithm and proofs
in Lean, a system for checking mathematical arguments. The accompanying notes
explain how the algorithm works and why the proofs hold.

Peterson's algorithm solves the mutual-exclusion problem: coordinating access
to a shared resource so that two processes cannot use it at the same time.
Each process records its intent in a shared flag; a third variable resolves
contention when both want access. The processes run independently, and either
can pause between operations. Establishing correctness means accounting for
all the ways those operations can interleave.

The notes and proofs follow the two-process algorithm closely, including
separate reads of the two parts of its waiting condition. They also make
explicit the assumptions needed to turn the paper's description into a
mathematical model.

## Results and scope

The formalization proves two results:

- **Mutual exclusion:** the processes cannot both be in their critical
  sections, the portions of their programs that use the shared resource.
- **Conditional progress:** once a request is pending, some process
  eventually makes a new entry, assuming enabled protocol steps are not
  neglected forever and critical-section work eventually finishes. This
  includes allowing a process to clear its flag on exit.

Both proofs concern a single passage through the algorithm: each process may
make at most one attempt. The memory model is sequential consistency, with
each shared read or write treated as an atomic operation. Both initial values
of the tie-break variable are covered, as are both short-circuit orders for
reading the wait condition; the processes use the same fixed order.

Safety does not require fairness. Progress does, and it gives no bound on
waiting time. The formalization does not cover repeated requests, weak-memory
execution, a compiled implementation, or the paper's n-process construction.
The [proof notes](docs/proofs.md) explain the progress assumptions in detail.

## Reading the proof

[The algorithm and model](docs/algorithm.md) introduces the state and operations
and follows an execution in which both processes request access.
[The proof notes](docs/proofs.md) develop the safety invariant and the argument
for eventual progress.

The two theorems are
[`peterson_mutual_exclusion`](Peterson/Safety.lean) and
[`peterson_global_progress`](Peterson/Progress.lean). Their definitions are in
[Specification.lean](Peterson/Specification.lean) and
[ProgressSpecification.lean](Peterson/ProgressSpecification.lean).
[Related work](docs/related-work.md) describes the other formalizations consulted
and the use of CSLib.

The reconstruction used an author-marked electronic restoration of the paper;
its identity with the publisher's version has not been established. The
[model notes](docs/algorithm.md) distinguish the source description from the
choices made in this formalization.

## Building

With `elan` installed, run from the repository root:

```sh
lake build Peterson.Safety Peterson.Progress
```

The project pins Lean `v4.34.0-rc2` and its dependencies. The
[verification guide](docs/verification.md) gives the commands for inspecting
the theorem statements and their logical assumptions, along with the limits
of those checks. [STATUS.md](STATUS.md) records the version and verification
history.

## AI assistance

Erik Peterson initiated and directed this project. The research, prose,
tooling, and Lean proofs are model-generated. Lean checked the proofs;
separate AI agents reviewed the model against the source and examined the
explanations. Those reviews are fallible and can share errors. In particular,
Lean's acceptance of a proof does not establish that its model faithfully
represents the paper. There has been no independent human mathematical review.

Licensed under [MIT](LICENSE).
