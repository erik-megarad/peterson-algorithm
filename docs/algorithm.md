# The algorithm and the explicit model

## What the source contributes

Peterson's [1981 article](https://doi.org/10.1016/0020-0190%2881%2990106-X) describes
coordination through an interest flag for each process and a shared tie-break
value. Our reading source is an author-marked electronic restoration, not a
verified publisher facsimile. The explanation below is newly written prose
about its two-process algorithm; the paper and its transcriptions are excluded.

For a process called A and its peer B, the passage is: announce interest by
setting A's flag; write A's own identity into the tie-break variable; repeatedly
look for either B's flag being false or the tie-break naming B; enter on such
an observation; finish critical work; then clear A's flag. B follows the same
pattern with the identities exchanged. Initially both flags are false and the
tie-break may name either process.

Writing one's own identity favors the peer when both are interested. This
convention matters: other presentations assign the peer's identity and reverse
the test. The formalization retains the convention just described.

## What the model makes explicit

[Specification.lean](../Peterson/Specification.lean) defines `State`, `Action`
and `Step`. A state contains shared flags and turn plus a private program
position for each process. Each shared read or write is a separate transition.
The relation is wrapped directly by CSLib's `LTS`; the wrapper does not add a
second algorithm.

| Program position | Next part of the passage |
| --- | --- |
| `beforeFlag` | Write the process's flag true; starting is optional. |
| `betweenWrites` | Write the process's own identity to turn. |
| `beforeFirstRead` | Perform the first chosen wait test. |
| `betweenReads` | Perform the second test after an unfavorable first read. |
| `critical` | Perform critical work and eventually finish if the progress premise holds. |
| `beforeExitWrite` | Clear the flag in a separate protocol action. |
| `afterPassage` | No second attempt in this model. |

A favorable first read enters immediately; it skips the second read. An
unfavorable second read restarts at the first. `flagFirst` tests the peer flag
before turn; `turnFirst` tests turn before the peer flag. Both processes share
one order for the entire run. The paper's non-atomic test motivates separate
reads; these two uniform, fixed evaluation orders are explicit project choices.

Sequential consistency is also explicit: all these actions interleave in one
sequence and respect each process's control flow. No transition represents
compiler reordering, caches, buffered writes or machine instructions.

## A collision to follow

Choose flag-first reads. A announces interest and writes A to turn. B announces
interest and writes B to turn. Both flags are now true; turn is B. A's flag read
continues to its turn read, which sees B and enters. B's flag read continues,
but its turn read sees its own identity, so it retries. After A finishes and
clears its flag, B can enter on a false flag read if it is scheduled.

This is an illustrative finite execution, not a proof that all executions
behave safely or that a scheduler will let them finish. Another process may
act between the two reads; the proof must account for such saved partial tests.

## Requests and entries

[ProgressSpecification.lean](../Peterson/ProgressSpecification.lean) adds an
observation sequence over the same steps. A request begins at the true flag
write. `Pending` covers the period after that write and before entry. `Entry`
is a transition into the critical section, not continued occupancy.

An observation is the state before its numbered action. A new entry at that
action or later meets the progress conclusion; one before the observation does
not. Unchanged-state padding allows a completed finite passage to be observed
forever. Padding cannot write memory, advance control or count as entry.

Return to the [overview](../README.md) or continue to [the proofs](proofs.md).
