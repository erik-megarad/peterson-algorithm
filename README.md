# Peterson mutual exclusion in Lean

Two processes sharing a resource need an entry protocol that prevents them from
using it together. This project reconstructs the two-process algorithm from
Gary L. Peterson's 1981 paper and explains two checked Lean results.

This account describes the completed safety-and-conditional-progress learning
artifact for version 1.0.0. The version and completion fields describe its scope;
they do not certify a published release or owner acceptance of this public
account. See [status](STATUS.md).

## Result

**Safety:** the two processes never occupy their critical sections together in
any finitely reachable state. The checked declaration is
`Peterson.peterson_mutual_exclusion` in [Safety.lean](Peterson/Safety.lean).

**Conditional progress:** after any observation of a pending request, some
process eventually makes a new entry, if participating protocol steps are not
permanently neglected and critical-section work eventually finishes. The
separate checked declaration is `Peterson.peterson_global_progress` in
[Progress.lean](Peterson/Progress.lean). Someone already inside does not count
as that new entry.

## Scope

Both results concern two processes making at most one attempt each, individually
atomic shared reads and writes in one sequence preserving program order, either
initial tie-break value, and either fixed short-circuit wait-test order. Both
processes use the same chosen order. A process may choose never to start.

Begin with [the algorithm and model](docs/algorithm.md), then
[the proof ideas](docs/proofs.md). The exact definitions remain in
[Specification.lean](Peterson/Specification.lean) and
[ProgressSpecification.lean](Peterson/ProgressSpecification.lean).

## Assumptions

The memory model is sequential consistency: each shared operation takes effect
as one action in the common sequence. The two reads of the wait condition are
separate actions, so another process can act between them.

Safety needs no fairness assumption. Progress additionally requires weak
fairness for participating protocol steps, including the exit flag clear, and
eventual completion of each critical section. Fairness promises a process a
step, not a successful read or any upper bound on delay. These explicit
sufficient premises are project interpretations of the environment, not exact
formulas supplied by the paper. [The progress explanation](docs/proofs.md)
spells out their roles.

## Non-goals

There is no waiting-time or step bound, repeated-client theorem, weak-memory
result, executable-code refinement or proof of the paper's n-process
construction. The checked progress conclusion is a new entry by some process.
A reviewed mathematical argument also gives eventual entry by the particular
requester in this one-passage model; that consequence has no separately
kernel-checked corollary here.

## Verification

The authoritative development passed clean tracked-source replay and
independent source/contract audits before its learning artifact was accepted
on 2026-09-08. The principal theorem paths report only the standard Lean
assumptions `propext`, `Classical.choice` and `Quot.sound`. No project placeholder,
unclassified custom axiom or unsafe proof path was accepted. Verified dependency
build caches were reused. These are prior development results. The
[public claim contract](publication-checks.toml) identifies the exact declarations
to check in this tree. [Verification details](docs/verification.md) separate
compiler checks, source faithfulness and their limits; this page is not a
public-root build report.

## Source relationship

The governing work is Gary L. Peterson, "Myths about the mutual exclusion
problem," Information Processing Letters 12(3), 1981, pages 115–116,
[DOI 10.1016/0020-0190(81)90106-X](https://doi.org/10.1016/0020-0190%2881%2990106-X).
The reconstruction used an author-marked electronic restoration; identity with
the publisher facsimile has not been established. The paper itself is not part
of this artifact. [The model explanation](docs/algorithm.md) distinguishes the
source algorithm from the explicit execution choices made here.

## AI assistance

AI models produced the research, explanations, tooling and Lean formalization.
Erik Peterson started and directed the project; he did not author those
artifacts. The MIT license names him as holder of any applicable rights he
holds, including rights assigned under applicable tool terms. This does not
assert that every model-generated output is copyrightable or grant rights in
third-party material. The project-name citation is bibliographic credit.

Model-generated outputs were treated as untrusted: saved Lean sources underwent kernel checks,
and separate agents audited correspondence with the source and accepted
contract. Separate-agent review can still share blind spots; it is not a formal
proof of source faithfulness or an independent human mathematical review.
Public-account review is a separate check on the explanations presented here.

## Reproduction

The public tree places its Lean project at the repository root, with Lean
`v4.34.0-rc2`, CSLib `33e7370a94646c19176dc847f7514559bc5e06fb`, and the full
transitive graph in `lake-manifest.json`. Run `lake build Peterson` from that
root. The [reproduction guide](docs/verification.md) gives the exact theorem
probe and explains what these commands establish.

For design precedents and contribution status, see
[related work and upstream disposition](docs/related-work.md).
