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
