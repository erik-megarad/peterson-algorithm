# The algorithms and explicit models

## Source boundary

Peterson's [1981 article](https://doi.org/10.1016/0020-0190%2881%2990106-X)
gives a two-process algorithm in Figure 1 and a finite n-process construction
in Figure 3. This project used an author-marked electronic restoration whose
identity with the publisher version is unestablished. This page is newly
written explanation; no paper text, image, or transcription is included.

## Two processes, one passage

Each process sets its interest flag, writes its own identity to shared `turn`,
then waits until it reads either a false peer flag or a `turn` value naming the
peer. Writing one's own identity favors the peer when both are interested.
After the critical section, the process clears its flag.

[Specification.lean](../Peterson/Specification.lean) makes each shared access a
separate transition. A process moves through `beforeFlag`, `betweenWrites`, two
possible read positions, `critical`, `beforeExitWrite`, and `afterPassage`.
The wait test may read flag first or turn first; both processes use the same
fixed order. The source says the whole Boolean wait test is non-atomic, but it
does not fully specify individual-access atomicity, sequential consistency, or
a uniform fixed short-circuit order. Those are explicit project choices. A
favorable first read enters immediately, an unfavorable first
read proceeds to the second, and an unfavorable second read loops. Initial
flags are false and initial `turn` may name either process.

`petersonLTS` wraps this exact relation in CSLib's `LTS`. `Reachable` means a
finite path from an initialized state. [ProgressSpecification.lean](../Peterson/ProgressSpecification.lean)
observes the same transitions in an infinite sequence, allowing identity
padding after finite work. `Request` is the flag-true write, `Entry` is a
transition into `critical`, and `Pending` describes control after requesting
and before entry. `ProtocolFair` and `CriticalCompletes` are extra temporal
premises, not consequences of validity.

## Repeated use

[Repeated/Specification.lean](../Peterson/Repeated/Specification.lean) reuses
every one-passage protocol edge literally and adds one private `restart` edge
from `afterPassage` to `beforeFlag`. Restart changes no shared value. It is
optional, can occur only after the flag-clear exit, and does not itself request
entry. Clients cannot cancel a request or restart early.

A repeated request is identified by actor and flag-write tick. `Serves` pairs
it with a later entry while the same request stays pending throughout the open
interval. This distinguishes per-request lockout freedom from the older global
statement that some process eventually enters. The quantitative observer in
[Repeated/OvertakingSpecification.lean](../Peterson/Repeated/OvertakingSpecification.lean)
counts peer `Entry` events in a finite pending interval; it does not alter the
algorithm state.

## The finite n-process construction

[NProcess.lean](../Peterson/NProcess.lean) models Figure 3 for exactly `m + 2`
processes, covering every finite n at least two. Internal identifiers and
levels are zero-based; adding one recovers the source numbering. Every process
passes through n−1 levels. At each level it announces that level in its Q cell
and writes its identity to that level's TURN cell. It then reads other Q cells
one at a time in ascending identifier order, short-circuiting at the first high
value. A complete low scan passes the level. A high value causes a separate
TURN read: a value naming another process passes the level, while the actor's
own value restarts the scan at its first peer. It clears Q after finishing its
critical section.

The source does not fix the scan/disjunct order. Ascending peers with the Q scan
before TURN is this project's reviewed choice. The scan cursor skips the actor
and can visit every peer. A low read may become
stale before later scan reads; the model deliberately does not replace those
reads with a snapshot. There is one passage, no restart, and no transition from
`done`. Initial Q values are zero and initial TURN values name source process 1,
as recorded by the reviewed source interpretation.

## Shared execution assumptions

As a project modeling choice, shared reads and writes are individually atomic
and interleave in one sequence that preserves each process's control order.
This is sequential consistency.
The models contain no compiler reordering, caches, buffered writes, crashes,
machine instructions, or executable client refinement.

Continue to [the proof guide](proofs.md), [verification](verification.md), or
return to the [overview](../README.md).
