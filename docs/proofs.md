# Why the six results hold

## One-passage safety

[Safety.lean](../Peterson/Safety.lean) preserves an invariant over every atomic
step. A process in the interested control range has a true flag. A process past
its wait excludes its own identity from `turn` when its peer has written turn
and not yet cleared its flag. If both processes were critical, the two symmetric
instances would exclude both possible turn values. Finite-trace induction turns
the one-step argument into `Peterson.peterson_mutual_exclusion` for every
reachable state. No fairness is used.

## Conditional one-passage progress

`Peterson.peterson_global_progress` in [Progress.lean](../Peterson/Progress.lean)
says that some new entry follows a pending observation when continuously enabled
protocol work is weakly fair and every critical occupant eventually finishes.
Each one-passage process performs only finitely many shared writes, so a suffix
eventually has stable shared memory. Fairness rules out a process remaining at
an enabled write or read forever; critical completion plus fair exit rules out
a permanent occupant. A remaining reader eventually sees a permanently
favorable flag or turn. The two read orders need separate handling because an
old unfavorable first read may already be stored in control. The conclusion
does not name the requester and gives no delay bound.

## Repeated safety

[Repeated/Safety.lean](../Peterson/Repeated/Safety.lean) keeps the same invariant.
Every protocol edge is an old step, and restart moves privately between two
control points outside all invariant ranges. Thus both kinds of repeated edge
preserve the invariant, yielding
`Peterson.Repeated.repeated_mutual_exclusion`. Checked traces in
[Repeated/TraceTests.lean](../Peterson/Repeated/TraceTests.lean) exercise a
complete restart and multiple passages; they are behavioral examples, not the
unbounded proof.

## Per-request lockout freedom

`Peterson.Repeated.repeated_request_entry` in
[Repeated/Progress.lean](../Peterson/Repeated/Progress.lean) follows one request
from its flag-write tick. Until entry, its pending state persists across peer
steps, padding, and peer restarts. Fairness supplies the requester's next
protocol operations. If the peer later writes turn, that write permanently
favors the requester while it remains a reader. If the peer never writes turn,
turn is constant; fairness and critical completion eventually make the peer's
flag false when the constant turn is unfavorable. Either case forces the
requester through a favorable read. The first later entry serves the same
request. [Repeated/ProgressExamples.lean](../Peterson/Repeated/ProgressExamples.lean)
checks repeated service and shows why each liveness premise matters.

## Arbitrary-n safety and capacity

The central lemma `Peterson.NProcess.level_capacity` in
[NProcessCapacity.lean](../Peterson/NProcessCapacity.lean) says that at most
n−k processes can be past level k without having cleared Q, for
0 ≤ k ≤ n−1. To move a set of at
least two processes past one level, the proof finds the last member to write
that level's TURN. Its individually read scan must encounter another member's
persistent high Q, so its eventual favorable TURN read witnesses an intervening
writer outside the set. Therefore one extra process was past the preceding
level. Induction from level zero gives capacity one at the last level, and
`Peterson.NProcess.arbitrary_mutual_exclusion` follows. The history and scan
lemmas derive this from actual finite traces; no snapshot or fairness premise
is introduced. [NProcessExamples.lean](../Peterson/NProcessExamples.lean)
includes a checked stale-read trace and all transition shapes.

## Sharp repeated overtaking

The paper does not state this numeric bound. It is a derived guarantee of this
project's precise repeated, sequentially consistent model and request boundary.
The interval begins with the requester's flag-true write. Before its turn write,
the true flag and a reachable-state `ReaderTurn` invariant prevent a peer from
entering, proving `repeated_pre_turn_zero`. After the requester writes turn, a
peer may enter once. A second peer entry would require the peer to finish,
clear, restart, request again, and write turn again; that fresh write favors the
still-pending requester and blocks the second entry. Finite interval lemmas in
[Repeated/Overtaking.lean](../Peterson/Repeated/Overtaking.lean) prove the
overall and after-turn bounds without assuming fairness. Combining the bound
with per-request lockout gives `repeated_bounded_service` under the liveness
premises.

[Repeated/OvertakingExamples.lean](../Peterson/Repeated/OvertakingExamples.lean)
constructs an explicit 11-event execution followed by idle padding. Its theorem
`repeated_overtaking_sharp` proves that one peer entry is attainable for both
read orders, both requester identities, and both initial `turn` values. The
bound counts entries, not elapsed time, total actions, or reads.

See [verification and its limits](verification.md), or return to the
[overview](../README.md).
