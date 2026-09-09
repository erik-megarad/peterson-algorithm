# Why the two results hold

## Safety needs more than the final claim

The checked safety theorem in [Safety.lean](../Peterson/Safety.lean) applies to
every finite execution of the two-process, one-passage, sequentially consistent
model, with either initial turn and either fixed read order. It requires no
scheduling fairness. Its proof maintains an invariant: facts true initially
and preserved by each atomic action.

The invariant in [Specification.lean](../Peterson/Specification.lean) relates
shared memory to current control positions. First, a process that has announced
interest but not cleared its flag has a true flag. Second, if A has passed its
wait but not cleared its flag, and B has written turn but not cleared its flag,
turn cannot name A. Both clauses apply with the actors exchanged.

The second fact describes current passage ranges, not whether a write happened
at any time in the past. Once B clears its flag, A can later write A to turn
and enter on B's false flag without contradicting the invariant.

Initially the relevant control ranges are empty. Preservation checks the
individual writes and each read outcome. A successful turn read supplies the
needed tie-break fact directly. For a successful flag read in either order,
the peer's false flag rules out its being in the range from writing turn through
waiting to clear its flag: the first invariant clause would require a true flag
there. The entering process therefore has no new tie-break requirement against
that peer. The peer's tie-break clause also remains valid, since the entering
process was already in the turn-written range before this read. This argument
uses the state at the individual flag read, even when it is the second test;
the proof never substitutes an atomic two-read test.

If both processes were critical, each would satisfy the second clause's
premises. Turn would then be neither A nor B. Its type permits only those two
values, giving a contradiction. Induction over reachable transitions makes this
argument apply to arbitrarily long finite executions, not just explored examples.

## The extra premises for progress

The separate theorem in [Progress.lean](../Peterson/Progress.lean) guarantees a
new entry by some process after every pending observation. It uses the same
one-passage model and both read orders, plus the exact predicates in
[ProgressSpecification.lean](../Peterson/ProgressSpecification.lean).

`ProtocolFair` says that, from any observation onward, an actor that continuously
has an enabled participating protocol action eventually takes one. This is weak
fairness. It includes the pending turn write, reads and exit flag clear. A failed
read counts as taking a step. It does not force an idle actor to start, promise
a favorable read or bound the wait.

`CriticalCompletes` independently says that every observed critical-section
occupant eventually performs its finishing action. Clearing the flag is a later
action whose scheduling still needs the first premise. These are sufficient
uniform assumptions, not a claim to be the weakest possible conditions or the
paper's exact temporal formulas.

Without scheduling fairness, a pending process can simply be ignored. Without
critical completion, an old occupant can remain inside forever while a peer
waits. Even after the occupant finishes, neglecting its flag clear can keep the
peer waiting. Such failures explain why safety cannot provide progress alone.

## Why a pending request cannot wait forever under those premises

Suppose a request is pending but no new entry ever follows. Each process makes
at most three shared writes during its single passage: flag true, turn, flag
false. Thus there is a later observation after which shared memory stops
changing. The proof derives that stable suffix; it does not assume it.

On that suffix, a process cannot remain waiting to write turn or clear its flag:
fair scheduling would force a further write. Nor can an old occupant remain,
because it must finish and then clear its flag. The original pending request
persists if no entry occurs, so a reader remains.

If the peer flag is false, this reader has a favorable flag test. If it is true,
the peer must be another reader. Whichever reader is opposite the fixed turn
value has a favorable turn test. Either way, a reader has a permanently
favorable test. Fair scheduling eventually brings it to that test, contradicting
the supposition of no new entry.

The two read orders need separate arguments. A process might already be between
reads when memory settles, carrying an old unfavorable observation. With
flag-first order and a now-false peer flag, its pending turn read can fail once
before the next flag read succeeds. With turn-first order and a now-favorable
turn, its pending flag read can fail once before the next turn read succeeds.
The other cases succeed directly or on the following read.

This short suffix argument gives no bound from the request. Memory may settle
arbitrarily late and scheduling each read can take arbitrarily long.

## What about the particular requester

There is a reviewed mathematical consequence for this one-passage model, with
no separately kernel-checked corollary claimed here. If the first new entry is
the peer's, the original requester remains pending. Applying global progress
again must produce the original requester's entry, since the peer cannot enter
twice. This does not establish bounded waiting or starvation freedom for
repeated clients. The two published claim candidates remain the exact safety
and global progress declarations.

See [verification and its limits](verification.md), or return to
[the overview](../README.md).
