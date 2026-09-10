# Related work and upstream disposition

## Design precedents

Peterson's [1981 article](https://doi.org/10.1016/0020-0190%2881%2990106-X) is the
algorithm source, not a claim that this is a new mutual-exclusion algorithm or
the first mechanization. The investigation examined prior work in Lean,
Isabelle/HOL, Coq, Mizar and TLA-style reasoning, as well as a C11-style treatment.
That was a bounded design survey, not an exhaustive proof inventory.

The main lesson is semantic: superficially similar Peterson programs can differ
in turn assignment, initial turn, whether a whole test is atomic, whether
requests repeat, and what memory guarantees apply. A theorem for one choice
cannot simply be relabeled as a theorem for another. This artifact retains
separate shared reads and its source-facing assignment convention, while
making its uniform read orders and temporal assumptions explicit.

Two accessible starting points from that recorded survey are James Wilcox's
[2015 Coq account](https://jamesrwilcox.com/SharedMem.html), whose separate reads
and turn convention informed target review, and the
[pinned Frisk17 Lean development](https://github.com/Frisk17/Petersons-s-Algorithm/tree/cf4c3322d8f661b277ca66d8087649a0c74bca6c),
which treats the whole guard atomically. Neither was locally replayed in this
investigation. These references report the earlier inspection; they do not
claim a new assessment of the current hosted artifacts. No third-party proof
source is reproduced on this page.

The public account claims only the six explicitly mapped result families described
in [the overview](../README.md); it makes no novelty or best-proof claim. Structured
references are included in the [bibliography](../corpus/bibliography.bib).

## Library reuse and contribution status

The pinned CSLib dependency supplies `LTS`, finite-trace machinery, and
`OmegaExecution`. Mathlib supplies ordinary finite-set cardinality and arithmetic
support for the n-process proof. The source-close state machines, request and
entry observers, fairness interpretation, n-process scan history, and overtaking
count remain specific to this investigation.
Importing library abstractions does not establish that the resulting modules
have an agreed upstream home.

The local dispositions retain all project-specific modules here. No maintainer
placement agreement, upstream packaging qualification, or accepted CSLib
contribution was recorded. A future contribution needs a fresh check
of community scope, APIs and contribution requirements, accurate authorship and
reuse attribution, suitable human contributor readiness, and separate permission
to contact maintainers or submit.

A focused public investigation and an upstream library submission serve different
purposes. This artifact explains and reproduces the learning result. Any upstream
candidate would be separately reviewed and licensed under the receiving
project's applicable terms. No upstream acceptance is implied here.

Return to [the overview](../README.md).
