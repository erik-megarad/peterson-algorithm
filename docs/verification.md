# Reproduction and verification limits

## Pinned environment

The export places the authoritative Lean project at the repository
root. It retains Lean `v4.34.0-rc2`, direct dependency CSLib
`33e7370a94646c19176dc847f7514559bc5e06fb`, and the complete transitive lock in
`lake-manifest.json`, including Mathlib
`950d27063f377d5ccd80d3eeedcebe319d3eb821`. Dependency source files are fetched
under their own licenses; they are not copied into this public account.

After installing the Lean toolchain manager elan, use a shell at the root of
the assembled public checkout. The pinned toolchain and dependency downloads
require access to their distribution services on a first build. Build the
two claim modules explicitly:

```sh
lake build Peterson.Safety Peterson.Progress
```

The [public claim contract](../publication-checks.toml) lists the selected
modules, source paths and exact theorem declarations for qualification.
These commands describe how to inspect the assembled tree; this page is not
a successful public-root build report.

## Audit the imported CSLib definitions

The two claims rely on CSLib definitions whose exact source can be inspected
without this repository redistributing it. Every upstream link below fixes
revision `33e7370a94646c19176dc847f7514559bc5e06fb`, the revision selected by
both [lakefile.lean](../lakefile.lean) and [lake-manifest.json](../lake-manifest.json).
These are descriptions of the definitions; the links and local commands expose
the original source for checking them.

| Definition at the pinned revision | Meaning used here |
| --- | --- |
| [LTS.Tr, lines 64–66](https://github.com/leanprover/cslib/blob/33e7370a94646c19176dc847f7514559bc5e06fb/Cslib/Foundations/Semantics/LTS/Basic.lean#L64-L66) | The transition proposition relates a starting state, an event label and a resulting state. |
| [MTr and its constructors, lines 91–95](https://github.com/leanprover/cslib/blob/33e7370a94646c19176dc847f7514559bc5e06fb/Cslib/Foundations/Semantics/LTS/Basic.lean#L91-L95) | A finite path has a finite list of labels. An empty path keeps its starting state. A nonempty path requires one transition and then a remaining path from the same intermediate state. |
| [CanReach, lines 198–202](https://github.com/leanprover/cslib/blob/33e7370a94646c19176dc847f7514559bc5e06fb/Cslib/Foundations/Semantics/LTS/Basic.lean#L198-L202) | Some finite label list and path connect the two states. Zero steps are allowed; there is no fixed upper bound on path length. Initiality and fairness are not included. |
| [OmegaExecution, lines 22–27](https://github.com/leanprover/cslib/blob/33e7370a94646c19176dc847f7514559bc5e06fb/Cslib/Foundations/Semantics/LTS/OmegaExecution.lean#L22-L27) | At every natural-number index, the event there must take the state there to the next state using the transition proposition. Events cannot be unrelated annotations. |
| [OmegaSequence storage and coercions, lines 33–44](https://github.com/leanprover/cslib/blob/33e7370a94646c19176dc847f7514559bc5e06fb/Cslib/Foundations/Data/OmegaSequence/Defs.lean#L33-L44) | A sequence stores a function on natural numbers. Applying a sequence reads that function; wrapping a function retains its entries and indices. |

Both [Challenge.lean](../Challenge.lean) and [Solution.lean](../Solution.lean)
import `LTS.Basic` and `LTS.OmegaExecution` directly under
`Cslib.Foundations.Semantics`. The latter imports `LTS.Execution` (which imports
Basic) and `OmegaSequence.Flatten`; Flatten imports Init, and Init imports Defs
under `Cslib.Foundations.Data.OmegaSequence`. This supplies the sequence definition
in the table.

In [Specification.lean](../Peterson/Specification.lean), `petersonLTS` uses the
reviewed `Step` relation directly. `Reachable` requires an `Initial` state and
`CanReach` from it. Initiality sets both flags false and both program counters
before their first write, allowing either turn value. Thus safety covers initial
states and states reached by any finite legal path. An arbitrary state without
such a path does not satisfy its premise.

In [ProgressSpecification.lean](../Peterson/ProgressSpecification.lean),
`ProgressExecution` alone supplies state and event functions. `Valid` adds
initiality at index zero and `OmegaExecution` for `observationLTS`. An absent
event in that adapter preserves the **whole state**. A present action must satisfy
`Step` between the states at that index and the next index. Changed-state padding
and an event inconsistent with the adjacent states fail that validity condition.
`ProtocolFair` and `CriticalCompletes` are separate premises of
`PetersonGlobalProgress`; valid execution alone does not promise progress.

### Inspect the fetched source locally

From the public checkout root with elan installed, run this block in a shell.
The first command fetches any absent packages selected by the lock and reports
the pinned compiler; it does not request a new dependency resolution. Network
access to dependency and toolchain distribution services is required on first
use. Do not use `lake update` for this inspection. No proof rebuild is needed.
The block stops if the fetched CSLib revision or source state does not match.

```sh
set -eu
lake env lean --version
cslib_dir=.lake/packages/cslib
cslib_rev=33e7370a94646c19176dc847f7514559bc5e06fb
test "$(git -C "$cslib_dir" rev-parse HEAD)" = "$cslib_rev"
test -z "$(git -C "$cslib_dir" status --porcelain --untracked-files=all)"
git -C "$cslib_dir" diff --exit-code "$cslib_rev" --
shasum -a 256 "$cslib_dir/Cslib/Foundations/Semantics/LTS/Basic.lean" \
  "$cslib_dir/Cslib/Foundations/Semantics/LTS/OmegaExecution.lean" \
  "$cslib_dir/Cslib/Foundations/Data/OmegaSequence/Defs.lean"
sed -n '64,66p;91,95p;198,202p' "$cslib_dir/Cslib/Foundations/Semantics/LTS/Basic.lean"
sed -n '22,27p' "$cslib_dir/Cslib/Foundations/Semantics/LTS/OmegaExecution.lean"
sed -n '33,44p' "$cslib_dir/Cslib/Foundations/Data/OmegaSequence/Defs.lean"
```

Compare the reported SHA-256 values with these complete-file hashes:

| File (relative to CSLib root) | SHA-256 |
| --- | --- |
| `Cslib/Foundations/Semantics/LTS/Basic.lean` | `02c9a9762c56a729bad9dec5ed2b6c060939efdff75b104e55cc8c9150e86954` |
| `Cslib/Foundations/Semantics/LTS/OmegaExecution.lean` | `ea5a5206942acc1d65516e3a2f6d3132cb821c1cb6829c8623fcdcdb0482ff86` |
| `Cslib/Foundations/Data/OmegaSequence/Defs.lean` | `8c457c72bde4f6df3c58d7edf57b86f259958299d0d05aad5528dee1f0a91a01` |

On 2026-09-09, the public-checkout inspection route passed; unauthenticated HTTPS
access to all three upstream source pages and raw files also passed, with raw
bytes matching these hashes. A separate web-reader tool failed to retrieve two
of the source pages. Palomar reviewer access has **not** been established by
these checks. A reviewer must actually open the linked source or execute the
commands to audit it. This guide addresses the reported evidence-access finding;
resolution still requires a subsequent review verdict. Dependency source and
inspection output are not bundled in this account.

## Inspect the exact logical assumptions

For a manual probe, save the following as `ClaimProbe.lean` at the checkout root:

```lean
import Peterson.Safety
import Peterson.Progress
#check Peterson.peterson_mutual_exclusion
#print axioms Peterson.peterson_mutual_exclusion
#check Peterson.peterson_global_progress
#print axioms Peterson.peterson_global_progress
```

Then run `lake env lean ClaimProbe.lean`. The principal declarations prove
`Peterson.PetersonMutualExclusion` and `Peterson.PetersonGlobalProgress`, whose
full propositions are in [Specification.lean](../Peterson/Specification.lean)
and [ProgressSpecification.lean](../Peterson/ProgressSpecification.lean).

The authoritative clean tracked-source replay reported only `propext`,
`Classical.choice` and `Quot.sound` for the principal theorem paths. These are
standard Lean logical assumptions concerning proposition equality, classical
choice and quotient equality. The development's broader trust checks rejected
project placeholders, unclassified custom axioms and unsafe proof paths.
Dependency build caches were reused after checking their pinned source state.
The manual probe above is a useful inspection, but it does not reproduce the
whole scanner, lock-integrity or publication review procedure.

## Different checks answer different questions

Lean's kernel checks that a proof term establishes its encoded proposition.
A clean build cannot establish that those definitions capture a historical
algorithm, or that prose describes them correctly. Separate source/contract
audits checked that correspondence in the authoritative development.

Likewise, finite examples can expose modeling mistakes but cannot prove an
unbounded theorem. The safety proof covers every finite reachable execution;
the conditional progress proof quantifies over valid observation sequences
under explicit fairness and completion premises. Neither result verifies
machine code or actual processor memory behavior.

The accepted learning artifact and past replay are existing development evidence.
Public prose, rights classifications, exported bytes, dependency recreation
and theorem-specific public qualification require their own checks; past
development acceptance does not establish those verdicts. Separate AI-agent
audits may share errors and are not human mathematical review.

See [status](../STATUS.md), [proof ideas](proofs.md) and [the overview](../README.md).

## Registry verification package

The root [formalization.yaml](../formalization.yaml) identifies Erik Peterson as
human author and discloses model production and agent review. The generated
[Challenge](../Challenge.lean) contains the same specifications and exactly two
intentional statement holes. It is a verifier input, not a proved module.
The generated [Solution](../Solution.lean) contains the complete specifications
and original proofs; [mapping.json](../mapping.json) accounts for every assembled
byte. Neither file imports the other or replaces the authoritative `Peterson`
modules. Build the assembled proof with `lake build Solution`.

[comparator.json](../comparator.json) selects both principal results and permits
only `propext`, `Quot.sound`, and `Classical.choice`. The pinned Palomar verifier
has locally accepted these exact Challenge/Solution bytes with Comparator,
NanoDa and Lean's default kernel. Local verification is separate from remote
intake, editorial review, submission and registration; none is implied here.
