# Artifact status

Publication version: 1.0.0
Publication status: complete
Corrects: none

This candidate covers the completed core Peterson results. On 2026-09-10 the
public remote had `main` at `5afd7f2cfc96072c6cfbd08f444e94d826bc28b0`
and no tags. Version `1.0.0` therefore remains available for the first immutable
release. Earlier commits bearing that candidate version and their historical
owner acceptance cover only the former two-result bytes; they do not accept,
qualify, or publish this expanded packet.

## Verification

The six claim records map to exact declarations in
[publication-checks.toml](publication-checks.toml). The authoritative private
development separately passed clean Lean builds, theorem-path axiom checks,
source scans, and independent semantic review for each model boundary. The
principal theorem paths report only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` assumptions. Dependency build caches were
reused in those checks.

Release requires revision-bound independent privacy, redistribution,
claim-faithfulness, and public-account review, followed by qualification of the
exact exported root. The private release evidence records whether those gates
passed for a particular source revision. This page does not assert their result
for these bytes and is not itself a review verdict, build report, owner
acceptance, or publication authorization.

## Limitations

The one-passage two-process model covers both source-permitted initial `turn`
values and both uniform fixed short-circuit read orders. Its progress theorem
guarantees a new entry by some process, not service of a named request.

The repeated model adds optional private restart only after the exit flag write.
Its safety theorem needs no fairness. Its per-request theorem and bounded-service
corollary require protocol fairness and eventual critical-work completion. The
sharp overtaking bound counts peer entry events from a request's flag write:
zero before that request's `turn` write, at most one overall, with one achieved
by checked witnesses for both orders, both actors, and both initial turns.

The n-process model covers every finite n at least two, one passage per process,
and ascending individually atomic peer scans. `level_capacity` is a finite-trace
capacity theorem used to derive mutual exclusion. No n-process progress,
repeated-use, arbitrary scan-order, weak-memory, executable refinement, or
wall-clock bound is claimed.

Source review uses an electronic restoration without established
publisher-facsimile identity. AI-assisted source and semantic review is not
independent human mathematical review. The repository's MIT license does not
license the source paper or fetched dependencies.

Read the [overview](README.md), [models](docs/algorithm.md), [proof guide](docs/proofs.md),
[verification guide](docs/verification.md), and [related work](docs/related-work.md).
