# Artifact status

Publication version: 1.0.0
Publication status: complete
Corrects: none

These fields describe the completed safety-and-conditional-progress artifact
and its version identity. They do not certify a published tag or owner
acceptance of this public account.

## Verification

The two principal results are `Peterson.peterson_mutual_exclusion` and
`Peterson.peterson_global_progress`. Their authoritative development passed
clean tracked-source replay, theorem-path trust checks and separate faithfulness
audits. The completed learning artifact was accepted on 2026-09-08. Dependency
build caches were reused; this was not a build of every dependency from scratch.

The [public claim contract](publication-checks.toml) names the two declarations
and their modules for checks of this tree. The [verification guide](docs/verification.md)
gives reproduction commands and distinguishes development evidence from
public-root qualification. This status page is not a build report, content-review
certificate or publication authorization.

## Limitations

Both results cover two processes, one passage, sequential consistency,
individually atomic shared operations, both permitted initial turn values and
either fixed short-circuit read order shared by the two processes. Safety alone
promises no progress. Progress requires weak fairness of participating protocol
steps, including exit flag clearing, and eventual completion of critical work.
Its checked conclusion is some new entry after a pending request, with no delay
bound. Repeated clients, weak memory, n processes and executable refinement are
outside this result.

Source review uses an electronic restoration, without a demonstrated
publisher-facsimile equivalence. Lean validates the encoded propositions, not
that historical correspondence. AI-assisted review is fallible. Upstream
acceptance, publication authorization and paper redistribution rights are not
implied by successful proof checking or learning-artifact acceptance.

Read the [result](README.md), [algorithm](docs/algorithm.md),
[proof ideas](docs/proofs.md) and [related work](docs/related-work.md).
