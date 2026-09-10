# Reproduction and verification limits

## Pinned environment and complete build

The exported root pins Lean `v4.34.0-rc2`, CSLib revision
`33e7370a94646c19176dc847f7514559bc5e06fb`, Mathlib revision
`950d27063f377d5ccd80d3eeedcebe319d3eb821`, and the complete dependency lock.
Dependency sources are fetched under their own licenses and are not copied into
this repository.

With `elan` installed, run at the repository root:

```sh
lake build Peterson.Verification Peterson.NProcessVerification
```

`Peterson.Verification` imports the one-passage, repeated, overtaking, and
checked-example graph. `Peterson.NProcessVerification` imports the n-process
model, history, scan, capacity proof, and examples. Together they compile every
Lean path listed in [publication-checks.toml](../publication-checks.toml) and
print the axioms of the checked declarations.

The public claim contract is exact: `build_modules` names these two verification
roots, `source_paths` enumerates every exported Lean source file, and each claim
record maps to its declaration and defining module. A successful build checks
the saved proof terms; it does not by itself run the lab's source scanner or
establish that prose and source interpretation are accurate.

## Inspect the six claim families

Save this as `ClaimProbe.lean` at the root:

```lean
import Peterson.Verification
import Peterson.NProcessVerification

#print axioms Peterson.peterson_mutual_exclusion
#print axioms Peterson.peterson_global_progress
#print axioms Peterson.Repeated.repeated_mutual_exclusion
#print axioms Peterson.Repeated.repeated_request_entry
#print axioms Peterson.NProcess.level_capacity
#print axioms Peterson.NProcess.arbitrary_mutual_exclusion
#print axioms Peterson.Repeated.repeated_overtaking_bound
#print axioms Peterson.Repeated.repeated_pre_turn_zero
#print axioms Peterson.Repeated.repeated_after_turn_bound
#print axioms Peterson.Repeated.repeated_bounded_service
#print axioms Peterson.Repeated.repeated_overtaking_sharp
```

Run `lake env lean ClaimProbe.lean`. The authoritative clean checks reported
only `propext`, `Classical.choice`, and `Quot.sound` on the principal paths.
These are standard Lean logical assumptions concerning proposition equality,
classical choice, and quotient equality. Project-local `sorry`, `admit`, custom
axioms, and unsafe proof escapes were rejected by the separate source/trust
check. The public qualification tool repeats source coverage, build, theorem
kind, and exact axiom classification against the exported bytes.

## Inspect the CSLib semantics

The models use CSLib's `LTS.Tr`, finite `MTr` traces and `CanReach`; temporal
models additionally use `OmegaExecution`. The exact upstream sources are:

- [LTS.Basic at the pinned revision](https://github.com/leanprover/cslib/blob/33e7370a94646c19176dc847f7514559bc5e06fb/Cslib/Foundations/Semantics/LTS/Basic.lean)
- [LTS.OmegaExecution at the pinned revision](https://github.com/leanprover/cslib/blob/33e7370a94646c19176dc847f7514559bc5e06fb/Cslib/Foundations/Semantics/LTS/OmegaExecution.lean)
- [OmegaSequence.Defs at the pinned revision](https://github.com/leanprover/cslib/blob/33e7370a94646c19176dc847f7514559bc5e06fb/Cslib/Foundations/Data/OmegaSequence/Defs.lean)

After the first dependency fetch, confirm that the local checkout matches the
lock without running `lake update`:

```sh
set -eu
lake env lean --version
cslib_dir=.lake/packages/cslib
cslib_rev=33e7370a94646c19176dc847f7514559bc5e06fb
test "$(git -C "$cslib_dir" rev-parse HEAD)" = "$cslib_rev"
test -z "$(git -C "$cslib_dir" status --porcelain --untracked-files=all)"
git -C "$cslib_dir" diff --exit-code "$cslib_rev" --
```

`petersonLTS` and the n-process `lts` store the project step relations directly.
`CanReach` adds no fairness. The observation adapters make absent events copy
the entire state, while present events must be actual adjacent protocol or
restart steps. Fairness and critical completion remain explicit predicates.

## What the checks establish

Kernel checking establishes that each declaration proves its encoded
proposition under its reported axioms. Finite examples exercise concrete paths
but do not prove the unbounded results. Independent semantic reviews compared
each protected model and theorem boundary with the retained source evidence;
those AI reviews can share mistakes and are not human mathematical review.

None of these checks establishes publisher-facsimile identity for the inspected
restoration, paper redistribution rights, weak-memory or compiler correctness,
or performance on a real scheduler. Fresh four-domain packet review and a
source-revision-bound exported-root qualification are required before release.

See [status](../STATUS.md), [proof ideas](proofs.md), and the
[overview](../README.md).
