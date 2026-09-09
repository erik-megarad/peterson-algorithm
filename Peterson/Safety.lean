import Peterson.Specification

/-!
# Safety proof for Peterson's two-process protocol

This module begins with the small helper layer used by the invariant proof.
The lemmas stay specific to the accepted two-process representation and its
three control ranges; they add no transition or reachability definitions.
-/

namespace Peterson

attribute [local simp] Interested TurnWritten PastWait

namespace Proc

/-- Taking the other process twice returns the original process. -/
@[simp] theorem other_other (i : Proc) : i.other.other = i := by
  cases i <;> rfl

/-- The other process is distinct from the original process. -/
@[simp] theorem other_ne (i : Proc) : i.other ≠ i := by
  cases i <;> decide

/-- A process is distinct from its peer. -/
@[simp] theorem ne_other (i : Proc) : i ≠ i.other := by
  cases i <;> decide

/-- Relative to `i`, every process is either `i` itself or its peer. -/
theorem eq_self_or_eq_other (i j : Proc) : j = i ∨ j = i.other := by
  cases i <;> cases j <;> simp [other]

end Proc

namespace State

/-!
The following equations make explicit which component each accepted update
changes.  In particular, an actor's update leaves its peer's indexed field
alone.
-/

@[simp] theorem setFlag_same (s : State) (i : Proc) (value : Bool) :
    (s.setFlag i value).flag i = value := by
  simp [setFlag]

@[simp] theorem setFlag_other (s : State) (i : Proc) (value : Bool) :
    (s.setFlag i value).flag i.other = s.flag i.other := by
  simp [setFlag]

@[simp] theorem setFlag_turn (s : State) (i : Proc) (value : Bool) :
    (s.setFlag i value).turn = s.turn := rfl

@[simp] theorem setFlag_pc (s : State) (i j : Proc) (value : Bool) :
    (s.setFlag i value).pc j = s.pc j := rfl

@[simp] theorem setTurn_flag (s : State) (value i : Proc) :
    (s.setTurn value).flag i = s.flag i := rfl

@[simp] theorem setTurn_value (s : State) (value : Proc) :
    (s.setTurn value).turn = value := rfl

@[simp] theorem setTurn_pc (s : State) (value i : Proc) :
    (s.setTurn value).pc i = s.pc i := rfl

@[simp] theorem setPC_flag (s : State) (i j : Proc) (value : PC) :
    (s.setPC i value).flag j = s.flag j := rfl

@[simp] theorem setPC_turn (s : State) (i : Proc) (value : PC) :
    (s.setPC i value).turn = s.turn := rfl

@[simp] theorem setPC_same (s : State) (i : Proc) (value : PC) :
    (s.setPC i value).pc i = value := by
  simp [setPC]

@[simp] theorem setPC_other (s : State) (i : Proc) (value : PC) :
    (s.setPC i value).pc i.other = s.pc i.other := by
  simp [setPC]

end State

/-!
The accepted control ranges form a strict progression: passing the wait means
the turn write has occurred, and a completed turn write means the process has
announced interest.  Case analysis keeps the exact membership choices visible.
-/

theorem pastWait_subset_turnWritten : PastWait ⊆ TurnWritten := by
  intro pc
  change PastWait pc → TurnWritten pc
  cases pc <;> simp [PastWait, TurnWritten]

theorem turnWritten_subset_interested : TurnWritten ⊆ Interested := by
  intro pc
  change TurnWritten pc → Interested pc
  cases pc <;> simp [TurnWritten, Interested]

theorem pastWait_subset_interested : PastWait ⊆ Interested :=
  Set.Subset.trans pastWait_subset_turnWritten turnWritten_subset_interested

@[simp] theorem mem_interested_iff (pc : PC) :
    pc ∈ Interested ↔ pc ≠ .beforeFlag ∧ pc ≠ .afterPassage := by
  change Interested pc ↔ pc ≠ .beforeFlag ∧ pc ≠ .afterPassage
  cases pc <;> simp [Interested]

@[simp] theorem mem_turnWritten_iff (pc : PC) :
    pc ∈ TurnWritten ↔
      pc ≠ .beforeFlag ∧ pc ≠ .betweenWrites ∧ pc ≠ .afterPassage := by
  change TurnWritten pc ↔
    pc ≠ .beforeFlag ∧ pc ≠ .betweenWrites ∧ pc ≠ .afterPassage
  cases pc <;> simp [TurnWritten]

@[simp] theorem mem_pastWait_iff (pc : PC) :
    pc ∈ PastWait ↔ pc = .critical ∨ pc = .beforeExitWrite := by
  change PastWait pc ↔ pc = .critical ∨ pc = .beforeExitWrite
  cases pc <;> simp [PastWait]

/-- The sole interested location before the turn write is `betweenWrites`. -/
theorem interested_not_turnWritten_iff (pc : PC) :
    pc ∈ Interested ∧ pc ∉ TurnWritten ↔ pc = .betweenWrites := by
  change Interested pc ∧ ¬ TurnWritten pc ↔ pc = .betweenWrites
  cases pc <;> simp [Interested, TurnWritten]

/-- The turn-written locations not past the wait are precisely its read states. -/
theorem turnWritten_not_pastWait_iff (pc : PC) :
    pc ∈ TurnWritten ∧ pc ∉ PastWait ↔
      pc = .beforeFirstRead ∨ pc = .betweenReads := by
  change TurnWritten pc ∧ ¬ PastWait pc ↔
    pc = .beforeFirstRead ∨ pc = .betweenReads
  cases pc <;> simp [TurnWritten, PastWait]

/-!
An initial state puts both processes before their flag-setting writes.  That
control position belongs to none of the invariant's ranges, so both clauses
hold without selecting either of the source-permitted initial `turn` values.
-/

/-- Every source-permitted initial state satisfies the reviewed invariant. -/
theorem invariant_initial {s : State} (hinitial : Initial s) : Invariant s := by
  obtain ⟨_, hpc⟩ := hinitial
  intro i
  constructor
  · intro hinterested
    rw [hpc i] at hinterested
    exact hinterested.elim
  · intro hexcludes
    rw [hpc i] at hexcludes
    exact hexcludes.1.elim

/-!
The following lemmas cover the protocol actions whose preservation argument
does not depend on a successful wait observation.  Keeping one lemma per
action-table row makes the eventual complete `TrInv` proof auditable against
`Step`.
-/

/-- Announcing interest preserves the invariant. -/
theorem invariant_writeFlagTrue {s : State} {i : Proc}
    (_hpc : s.pc i = .beforeFlag) (hinv : Invariant s) :
    Invariant ((s.setFlag i true).setPC i .betweenWrites) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simp [FlagAgrees]
    · simp [TurnExcludes]
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simp [TurnExcludes]

/-- Writing the actor into `turn` preserves both symmetric turn clauses. -/
theorem invariant_writeTurn {s : State} {i : Proc}
    (hpc : s.pc i = .betweenWrites) (hinv : Invariant s) :
    Invariant ((s.setTurn i).setPC i .beforeFirstRead) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · simp [TurnExcludes]
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simp [TurnExcludes]

/-- An unfavorable second read in flag-first order only restarts the wait. -/
theorem invariant_flagFirstReadTurnSelf {s : State} {i : Proc}
    (hpc : s.pc i = .betweenReads) (_hturn : s.turn = i)
    (hinv : Invariant s) : Invariant (s.setPC i .beforeFirstRead) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · simp [TurnExcludes]
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simpa [TurnExcludes, hpc] using (hinv i.other).2

/-- An unfavorable second read in turn-first order only restarts the wait. -/
theorem invariant_turnFirstReadFlagTrue {s : State} {i : Proc}
    (hpc : s.pc i = .betweenReads) (_hflag : s.flag i.other = true)
    (hinv : Invariant s) : Invariant (s.setPC i .beforeFirstRead) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · simp [TurnExcludes]
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simpa [TurnExcludes, hpc] using (hinv i.other).2

/-- Leaving the critical section preserves the same invariant control ranges. -/
theorem invariant_finishCritical {s : State} {i : Proc}
    (hpc : s.pc i = .critical) (hinv : Invariant s) :
    Invariant (s.setPC i .beforeExitWrite) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · simpa [TurnExcludes, hpc] using (hinv i).2
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simpa [TurnExcludes, hpc] using (hinv i.other).2

/-- The exit write removes the actor from all three invariant control ranges. -/
theorem invariant_writeFlagFalse {s : State} {i : Proc}
    (_hpc : s.pc i = .beforeExitWrite) (hinv : Invariant s) :
    Invariant ((s.setFlag i false).setPC i .afterPassage) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simp [FlagAgrees]
    · simp [TurnExcludes]
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simp [TurnExcludes]

/-!
The four successful observations move the actor across the wait boundary.
A successful `turn` read supplies the actor's new exclusion clause directly.
A successful false-flag read makes that clause vacuous whenever the peer has
written `turn`: the peer's invariant would then require the observed flag to
be true.  The peer's own exclusion clause is preserved because the actor was
already in the turn-written range before either successful second read.
-/

/-- A false peer flag lets the actor pass immediately in flag-first order. -/
theorem invariant_flagFirstReadFlagFalse {s : State} {i : Proc}
    (hpc : s.pc i = .beforeFirstRead) (hflag : s.flag i.other = false)
    (hinv : Invariant s) : Invariant (s.setPC i .critical) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · intro ⟨_, hotherWritten⟩
      have hotherWritten' : s.pc i.other ∈ TurnWritten := by
        simpa using hotherWritten
      have hotherInterested := turnWritten_subset_interested hotherWritten'
      have hotherFlag : s.flag i.other = true := (hinv i.other).1 hotherInterested
      simp [hflag] at hotherFlag
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simpa [TurnExcludes, hpc] using (hinv i.other).2

/-- Reading the peer in `turn` completes the flag-first wait. -/
theorem invariant_flagFirstReadTurnOther {s : State} {i : Proc}
    (hpc : s.pc i = .betweenReads) (hturn : s.turn = i.other)
    (hinv : Invariant s) : Invariant (s.setPC i .critical) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · simp [TurnExcludes, hturn]
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simpa [TurnExcludes, hpc] using (hinv i.other).2

/-- A true peer flag continues flag-first evaluation to its second read. -/
theorem invariant_flagFirstReadFlagTrue {s : State} {i : Proc}
    (hpc : s.pc i = .beforeFirstRead) (_hflag : s.flag i.other = true)
    (hinv : Invariant s) : Invariant (s.setPC i .betweenReads) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · simp [TurnExcludes]
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simpa [TurnExcludes, hpc] using (hinv i.other).2

/-- Reading the peer in `turn` completes the turn-first wait immediately. -/
theorem invariant_turnFirstReadTurnOther {s : State} {i : Proc}
    (hpc : s.pc i = .beforeFirstRead) (hturn : s.turn = i.other)
    (hinv : Invariant s) : Invariant (s.setPC i .critical) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · simp [TurnExcludes, hturn]
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simpa [TurnExcludes, hpc] using (hinv i.other).2

/-- Reading self in `turn` continues turn-first evaluation to its flag read. -/
theorem invariant_turnFirstReadTurnSelf {s : State} {i : Proc}
    (hpc : s.pc i = .beforeFirstRead) (_hturn : s.turn = i)
    (hinv : Invariant s) : Invariant (s.setPC i .betweenReads) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · simp [TurnExcludes]
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simpa [TurnExcludes, hpc] using (hinv i.other).2

/-- A false peer flag completes the second read in turn-first order. -/
theorem invariant_turnFirstReadFlagFalse {s : State} {i : Proc}
    (hpc : s.pc i = .betweenReads) (hflag : s.flag i.other = false)
    (hinv : Invariant s) : Invariant (s.setPC i .critical) := by
  intro j
  rcases Proc.eq_self_or_eq_other i j with h | h
  · subst j
    constructor
    · simpa [FlagAgrees, hpc] using (hinv i).1
    · intro ⟨_, hotherWritten⟩
      have hotherWritten' : s.pc i.other ∈ TurnWritten := by
        simpa using hotherWritten
      have hotherInterested := turnWritten_subset_interested hotherWritten'
      have hotherFlag : s.flag i.other = true := (hinv i.other).1 hotherInterested
      simp [hflag] at hotherFlag
  · subst j
    constructor
    · simpa [FlagAgrees] using (hinv i.other).1
    · simpa [TurnExcludes, hpc] using (hinv i.other).2

/-- Every accepted atomic action preserves the reviewed invariant. -/
theorem invariant_step (order : WaitOrder) :
    (petersonLTS order).TrInv Invariant := by
  intro s _action s' hstep hinv
  cases hstep with
  | writeFlagTrue hpc => exact invariant_writeFlagTrue hpc hinv
  | writeTurn hpc => exact invariant_writeTurn hpc hinv
  | flagFirstReadFlagFalse _ hpc hflag =>
      exact invariant_flagFirstReadFlagFalse hpc hflag hinv
  | flagFirstReadFlagTrue _ hpc hflag =>
      exact invariant_flagFirstReadFlagTrue hpc hflag hinv
  | flagFirstReadTurnOther _ hpc hturn =>
      exact invariant_flagFirstReadTurnOther hpc hturn hinv
  | flagFirstReadTurnSelf _ hpc hturn =>
      exact invariant_flagFirstReadTurnSelf hpc hturn hinv
  | turnFirstReadTurnOther _ hpc hturn =>
      exact invariant_turnFirstReadTurnOther hpc hturn hinv
  | turnFirstReadTurnSelf _ hpc hturn =>
      exact invariant_turnFirstReadTurnSelf hpc hturn hinv
  | turnFirstReadFlagFalse _ hpc hflag =>
      exact invariant_turnFirstReadFlagFalse hpc hflag hinv
  | turnFirstReadFlagTrue _ hpc hflag =>
      exact invariant_turnFirstReadFlagTrue hpc hflag hinv
  | finishCritical hpc => exact invariant_finishCritical hpc hinv
  | writeFlagFalse hpc => exact invariant_writeFlagFalse hpc hinv

/-!
One-step preservation now lifts through CSLib's finite labelled traces.  The
local `Reachable` wrapper contributes only its choice of a source-permitted
initial state; it does not introduce another multistep relation.
-/

/-- Every finitely reachable state satisfies the reviewed invariant. -/
theorem invariant_reachable {order : WaitOrder} {s : State}
    (hreachable : Reachable order s) : Invariant s := by
  obtain ⟨s₀, hinitial, actions, htrace⟩ := hreachable
  exact (Cslib.LTS.mtrInv_of_trInv (invariant_step order))
    s₀ actions s htrace (invariant_initial hinitial)

/-!
If both processes occupied their critical sections, each process's
`TurnExcludes` clause would apply: `critical` is past the wait, and the peer's
`critical` position is in the turn-written range.  The two clauses would say
that the two-valued `turn` field is neither process, which is impossible.
-/

/-- The reviewed invariant rules out simultaneous critical-section occupancy. -/
theorem invariant_mutuallyExclusive {s : State} (hinv : Invariant s) :
    MutuallyExclusive s := by
  rintro ⟨hpc1, hpc2⟩
  change s.pc .p1 = .critical at hpc1
  change s.pc .p2 = .critical at hpc2
  have hp1Past : s.pc .p1 ∈ PastWait := by simp [hpc1]
  have hp2Past : s.pc .p2 ∈ PastWait := by simp [hpc2]
  have hp1Written : s.pc .p1 ∈ TurnWritten := by simp [hpc1]
  have hp2Written : s.pc .p2 ∈ TurnWritten := by simp [hpc2]
  have hturn_ne_p1 : s.turn ≠ .p1 :=
    (hinv .p1).2 ⟨hp1Past, by simpa [Proc.other] using hp2Written⟩
  have hturn_ne_p2 : s.turn ≠ .p2 :=
    (hinv .p2).2 ⟨hp2Past, by simpa [Proc.other] using hp1Written⟩
  cases hturn : s.turn with
  | p1 => exact hturn_ne_p1 hturn
  | p2 => exact hturn_ne_p2 hturn

/-- Mutual exclusion for both fixed wait orders and both permitted initial turns. -/
theorem peterson_mutual_exclusion : PetersonMutualExclusion := by
  intro order s hreachable
  exact invariant_mutuallyExclusive (invariant_reachable hreachable)

end Peterson
