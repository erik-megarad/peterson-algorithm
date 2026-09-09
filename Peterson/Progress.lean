import Peterson.ProgressSpecification

/-!
# Observation correspondence

The infinite observation representation preserves the original individually
atomic transitions. Padding erasure below changes only the finite label list,
never the endpoint states or a shared-memory action.
-/

namespace Peterson

/-- The CSLib adapter is exactly the two pointwise clauses of the accepted contract. -/
theorem valid_iff {order : WaitOrder} {E : ProgressExecution} :
    Valid order E ↔ Initial (E.state 0) ∧
      (∀ n, E.event n = none → E.state (n + 1) = E.state n) ∧
      (∀ n a, E.event n = some a → Step order (E.state n) a (E.state (n + 1))) := by
  constructor
  · rintro ⟨hi, ht⟩
    refine ⟨hi, ?_, ?_⟩
    · intro n hn
      have h := ht n
      simpa [observationLTS, hn] using h
    · intro n a ha
      have h := ht n
      simpa [observationLTS, ha] using h
  · rintro ⟨hi, hn, ha⟩
    refine ⟨hi, ?_⟩
    intro n
    cases h : E.event n with
    | none => simpa [observationLTS, h] using hn n h
    | some a => simpa [observationLTS, h] using ha n a h

/-- Erasing padding from a finite observation trace preserves both endpoints. -/
theorem observation_mTr_erase {order : WaitOrder} {s t : State}
    {labels : List (Option Action)} (h : (observationLTS order).MTr s labels t) :
    (petersonLTS order).MTr s (labels.filterMap id) t := by
  induction h with
  | refl => exact .refl
  | @stepL s label u labels t hstep _ ih =>
    cases label with
    | none =>
      change u = s at hstep
      subst u
      simpa using ih
    | some a =>
      exact .stepL hstep ih

/-- Every finite observation interval is an original trace with padding removed. -/
theorem valid_prefix_mTr {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {m n : ℕ} (hmn : m ≤ n) :
    (petersonLTS order).MTr (E.state m)
      (((Cslib.ωSequence.mk E.event).extract m n).filterMap id) (E.state n) := by
  exact observation_mTr_erase (h.2.extract_mTr hmn)

/-- Every observed state is reachable in the original finite-trace semantics. -/
theorem valid_reachable {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (n : ℕ) : Reachable order (E.state n) := by
  exact ⟨E.state 0, h.1, _, valid_prefix_mTr h (Nat.zero_le n)⟩

/-- An original finite trace embeds with one `some` label per atomic action. -/
theorem mTr_observation {order : WaitOrder} {s t : State} {actions : List Action}
    (h : (petersonLTS order).MTr s actions t) :
    (observationLTS order).MTr s (actions.map some) t := by
  induction h with
  | refl => exact .refl
  | stepL hstep _ ih => exact .stepL hstep ih

open Cslib.ωSequence in
/--
Every initialized finite original trace has a valid infinite extension that
pads its terminal state forever. Its original labels occur at exactly their
original indices. This establishes validity only, not fairness or completion.
-/
theorem mTr_exists_valid_padding {order : WaitOrder} {s t : State}
    {actions : List Action} (hi : Initial s)
    (h : (petersonLTS order).MTr s actions t) :
    ∃ E : ProgressExecution, Valid order E ∧ E.state 0 = s ∧
      (∀ n (hn : n < actions.length), E.event n = some actions[n]) ∧
      (∀ n, E.state (actions.length + n) = t ∧ E.event (actions.length + n) = none) := by
  let tailStates : Cslib.ωSequence State := ⟨fun _ => t⟩
  let tailEvents : Cslib.ωSequence (Option Action) := ⟨fun _ => none⟩
  have htail : (observationLTS order).OmegaExecution tailStates tailEvents := by
    intro n
    rfl
  obtain ⟨ss, hs, hzero, _, hdrop⟩ :=
    Cslib.LTS.OmegaExecution.append (mTr_observation h) htail (show tailStates 0 = t from rfl)
  let events := actions.map some ++ω tailEvents
  refine ⟨⟨fun n => ss n, fun n => events n⟩, ⟨?_, hs⟩, hzero, ?_, ?_⟩
  · simpa [hzero] using hi
  · intro n hn
    change (actions.map some ++ω tailEvents) n = some actions[n]
    rw [get_append_left n (actions.map some) tailEvents (by simpa using hn)]
    simp
  · intro n
    constructor
    · have hd := congrArg (fun seq : Cslib.ωSequence State => seq n) hdrop
      simpa [get_drop, Nat.add_comm, tailStates] using hd
    · simpa [events, tailEvents] using get_append_right n (actions.map some) tailEvents

/-- An atomic action changes only its actor's private counter. -/
theorem step_pc_of_ne_actor {order : WaitOrder} {s t : State} {a : Action}
    (h : Step order s a t) {i : Proc} (hi : i ≠ actor a) : t.pc i = s.pc i := by
  cases h <;> simp_all [actor, State.setPC, State.setFlag, State.setTurn, Function.update]

/-- The request write puts its actor at the first pending position. -/
theorem request_pending {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {n : ℕ} (hr : Request E i n) :
    Pending i (E.state (n + 1)) := by
  have hs := (valid_iff.mp h).2.2 n (.writeFlagTrue i) hr
  generalize hdst : E.state (n + 1) = t at hs
  cases hs
  simp [Pending, State.setPC, Function.update]

/-- The four successful read families are exactly the possible entry edges. -/
theorem entry_iff_read {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {n : ℕ} : Entry E i n ↔
      (order = .flagFirst ∧ (E.state n).pc i = .beforeFirstRead ∧
        E.event n = some (.readFlag i i.other false)) ∨
      (order = .flagFirst ∧ (E.state n).pc i = .betweenReads ∧
        E.event n = some (.readTurn i i.other)) ∨
      (order = .turnFirst ∧ (E.state n).pc i = .beforeFirstRead ∧
        E.event n = some (.readTurn i i.other)) ∨
      (order = .turnFirst ∧ (E.state n).pc i = .betweenReads ∧
        E.event n = some (.readFlag i i.other false)) := by
  constructor
  · rintro ⟨a, ha, hi, hn, ht⟩
    have hs := (valid_iff.mp h).2.2 n a ha
    generalize hdst : E.state (n + 1) = t at hs
    cases hs <;> simp_all [actor, State.setPC, State.setFlag, State.setTurn, Function.update]
  · intro he
    rcases he with ⟨ho, hp, he⟩ | ⟨ho, hp, he⟩ | ⟨ho, hp, he⟩ | ⟨ho, hp, he⟩
    all_goals
      have hs := (valid_iff.mp h).2.2 n _ he
      generalize hdst : E.state (n + 1) = t at hs
      cases i <;> cases hs <;> simp_all [Entry, actor, State.setPC, Function.update, Proc.other]

/-- Entry consumes the pending request at the destination observation. -/
theorem entry_not_pending {E : ProgressExecution} {i : Proc} {n : ℕ}
    (he : Entry E i n) : ¬ Pending i (E.state (n + 1)) := by
  obtain ⟨_, _, _, _, ht⟩ := he
  simp [Pending, ht]

/-- Padding cannot be mistaken for a new entry. -/
theorem padding_not_entry {E : ProgressExecution} {n : ℕ} (hn : E.event n = none)
    (i : Proc) : ¬ Entry E i n := by
  rintro ⟨a, ha, _⟩
  simp [hn] at ha

/-- Existing critical occupancy is not a new entry at the same observation. -/
theorem critical_not_entry {E : ProgressExecution} {i : Proc} {n : ℕ}
    (hp : (E.state n).pc i = .critical) : ¬ Entry E i n := by
  rintro ⟨_, _, _, hn, _⟩
  exact hn hp

/-- A pending actor either remains pending or takes its own entry edge. -/
theorem step_pending_or_entry {order : WaitOrder} {s t : State} {a : Action}
    (h : Step order s a t) {i : Proc} (hp : Pending i s) :
    Pending i t ∨ (actor a = i ∧ s.pc i ≠ .critical ∧ t.pc i = .critical) := by
  by_cases hi : i = actor a
  · subst i
    cases h <;> simp_all [Pending, actor, State.setPC, State.setTurn, Function.update]
  · exact Or.inl (by simpa [Pending, step_pc_of_ne_actor h hi] using hp)

/-- A tick without this actor's entry preserves its pending request. -/
theorem pending_succ_of_not_entry {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {n : ℕ} (hp : Pending i (E.state n))
    (hn : ¬ Entry E i n) : Pending i (E.state (n + 1)) := by
  cases he : E.event n with
  | none => simpa [(valid_iff.mp h).2.1 n he] using hp
  | some a =>
    rcases step_pending_or_entry ((valid_iff.mp h).2.2 n a he) hp with hp' | hent
    · exact hp'
    · exact (hn ⟨a, he, hent⟩).elim

/-- Pending requests persist through every finite interval without an actor entry. -/
theorem pending_of_no_entry {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {m n : ℕ} (hmn : m ≤ n)
    (hp : Pending i (E.state m))
    (hn : ∀ r, m ≤ r → r < n → ¬ Entry E i r) : Pending i (E.state n) := by
  induction n, hmn using Nat.le_induction with
  | base => exact hp
  | succ n hmn ih =>
    exact pending_succ_of_not_entry h
      (ih (fun r hmr hrn => hn r hmr (Nat.lt_trans hrn (Nat.lt_succ_self n))))
      (hn n hmn (Nat.lt_succ_self n))

/-- Pending after an atomic step was already pending or has just requested entry. -/
theorem step_pending_predecessor {order : WaitOrder} {s t : State} {a : Action}
    (h : Step order s a t) {i : Proc} (hp : Pending i t) :
    Pending i s ∨ a = .writeFlagTrue i := by
  by_cases hi : i = actor a
  · subst i
    cases h <;> simp_all [Pending, actor, State.setPC, State.setFlag, State.setTurn, Function.update]
  · exact Or.inl (by simpa [Pending, step_pc_of_ne_actor h hi] using hp)

/-- Pending at the next observation either persists or comes from this tick's request. -/
theorem pending_predecessor {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {n : ℕ} (hp : Pending i (E.state (n + 1))) :
    Pending i (E.state n) ∨ Request E i n := by
  cases he : E.event n with
  | none => exact Or.inl (by simpa [(valid_iff.mp h).2.1 n he] using hp)
  | some a =>
    rcases step_pending_predecessor ((valid_iff.mp h).2.2 n a he) hp with hs | ha
    · exact Or.inl hs
    · exact Or.inr (by simpa [Request, ha] using he)

/--
Pending at observation `m` is exactly a prior request at `k < m` with no
actor entry at a tick strictly between `k` and `m`. Initiality supplies the
base case; this history property is proved, not assumed as an invariant.
-/
theorem pending_iff_request_history {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (i : Proc) (m : ℕ) :
    Pending i (E.state m) ↔ ∃ k, k < m ∧ Request E i k ∧
      ∀ r, k < r → r < m → ¬ Entry E i r := by
  constructor
  · intro hp
    induction m with
    | zero => simp [Pending, h.1.2 i] at hp
    | succ m ih =>
      rcases pending_predecessor h hp with hprev | hr
      · obtain ⟨k, hkm, hk, hno⟩ := ih hprev
        refine ⟨k, Nat.lt_trans hkm (Nat.lt_succ_self m), hk, ?_⟩
        intro r hkr hrm he
        by_cases hr : r < m
        · exact hno r hkr hr he
        · have heq : r = m := by omega
          subst r
          exact entry_not_pending he hp
      · exact ⟨m, Nat.lt_succ_self m, hr, by intro r hmr hrm; omega⟩
  · rintro ⟨k, hkm, hr, hno⟩
    exact pending_of_no_entry h (Nat.succ_le_of_lt hkm) (request_pending h hr)
      (fun r hkr hrm => hno r (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hkr) hrm)

/-- Initially a flag is true exactly at an interested counter (both sides are false). -/
theorem flag_iff_interested_initial {s : State} (h : Initial s) :
    ∀ i, s.flag i = true ↔ Interested (s.pc i) := by
  intro i
  simp [h.1 i, h.2 i, Interested]

/-- Each atomic action preserves full flag/counter correspondence for both actors. -/
theorem flag_iff_interested_step {order : WaitOrder} {s t : State} {a : Action}
    (h : Step order s a t)
    (hf : ∀ i, s.flag i = true ↔ Interested (s.pc i)) :
    ∀ i, t.flag i = true ↔ Interested (t.pc i) := by
  intro i
  by_cases hi : i = actor a
  · subst i
    cases h <;> simp_all [actor, State.setPC, State.setFlag, State.setTurn,
      Function.update, Interested]
  · cases h <;> simp_all [actor, State.setPC, State.setFlag, State.setTurn,
      Function.update]

/-- Full flag correspondence follows from initiality and original finite traces. -/
theorem flag_iff_interested_reachable {order : WaitOrder} {s : State}
    (h : Reachable order s) (i : Proc) :
    s.flag i = true ↔ s.pc i ∈ Interested := by
  obtain ⟨s₀, hi, actions, ht⟩ := h
  have hinv : (petersonLTS order).TrInv
      (fun s => ∀ j, s.flag j = true ↔ Interested (s.pc j)) := by
    intro s a t hs hf
    exact flag_iff_interested_step hs hf
  exact (Cslib.LTS.mtrInv_of_trInv hinv s₀ actions s ht
    (flag_iff_interested_initial hi)) i

/-- A false flag means precisely that no request has started or the passage has ended. -/
theorem flag_false_iff_reachable {order : WaitOrder} {s : State}
    (h : Reachable order s) (i : Proc) :
    s.flag i = false ↔ s.pc i = .beforeFlag ∨ s.pc i = .afterPassage := by
  have hf : s.flag i = true ↔ Interested (s.pc i) := flag_iff_interested_reachable h i
  cases hpc : s.pc i <;> cases hflag : s.flag i <;> simp_all [Interested]

/-- Padding preserves the same exact true-flag correspondence at every observation. -/
theorem valid_flag_iff_interested {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (i : Proc) (n : ℕ) :
    (E.state n).flag i = true ↔ (E.state n).pc i ∈ Interested := by
  exact flag_iff_interested_reachable (valid_reachable h n) i

/-- False flags before request and after passage remain exact even with padding. -/
theorem valid_flag_false_iff {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (i : Proc) (n : ℕ) :
    (E.state n).flag i = false ↔
      (E.state n).pc i = .beforeFlag ∨ (E.state n).pc i = .afterPassage := by
  exact flag_false_iff_reachable (valid_reachable h n) i

/-- One-passage stages identify both read positions, allowing their waiting loop. -/
def passageStage : PC → ℕ
  | .beforeFlag => 0
  | .betweenWrites => 1
  | .beforeFirstRead | .betweenReads => 2
  | .critical => 3
  | .beforeExitWrite => 4
  | .afterPassage => 5

/-- Original steps never move either actor back to an earlier passage stage. -/
theorem step_passageStage {order : WaitOrder} {s t : State} {a : Action}
    (h : Step order s a t) (i : Proc) : passageStage (s.pc i) ≤ passageStage (t.pc i) := by
  by_cases hi : i = actor a
  · subst i
    cases h <;> simp_all [actor, State.setPC, State.setFlag, State.setTurn,
      Function.update, passageStage]
  · rw [step_pc_of_ne_actor h hi]

/-- Stage monotonicity includes padding and arbitrary finite observation intervals. -/
theorem valid_passageStage_mono {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (i : Proc) : Monotone (fun n => passageStage ((E.state n).pc i)) := by
  apply monotone_nat_of_le_succ
  intro n
  cases he : E.event n with
  | none => rw [(valid_iff.mp h).2.1 n he]
  | some a => exact step_passageStage ((valid_iff.mp h).2.2 n a he) i

/-- A monotone passage stage can cross a fixed boundary at only one tick. -/
private theorem stage_crossing_unique {f : ℕ → ℕ} (hf : Monotone f) {k m n : ℕ}
    (hm : f m = k ∧ k < f (m + 1)) (hn : f n = k ∧ k < f (n + 1)) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · have : f (m + 1) ≤ f n := hf (by omega)
    omega
  · exact h
  · have : f (n + 1) ≤ f m := hf (by omega)
    omega

/-- A request crosses from the initial stage to the first participating stage. -/
theorem request_stage {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {n : ℕ} (hr : Request E i n) :
    passageStage ((E.state n).pc i) = 0 ∧
      0 < passageStage ((E.state (n + 1)).pc i) := by
  have hs := (valid_iff.mp h).2.2 n (.writeFlagTrue i) hr
  generalize hdst : E.state (n + 1) = t at hs
  cases hs
  simp_all [passageStage, State.setPC, Function.update]

/-- The turn write crosses from the between-writes stage into the wait loop. -/
theorem writeTurn_stage {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i v : Proc} {n : ℕ}
    (he : E.event n = some (.writeTurn i v)) :
    passageStage ((E.state n).pc i) = 1 ∧
      1 < passageStage ((E.state (n + 1)).pc i) := by
  have hs := (valid_iff.mp h).2.2 n (.writeTurn i v) he
  generalize hdst : E.state (n + 1) = t at hs
  cases hs
  simp_all [passageStage, State.setPC, Function.update]

/-- The exit flag write crosses from exit preparation to the final stage. -/
theorem writeFlagFalse_stage {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {n : ℕ}
    (he : E.event n = some (.writeFlagFalse i)) :
    passageStage ((E.state n).pc i) = 4 ∧
      4 < passageStage ((E.state (n + 1)).pc i) := by
  have hs := (valid_iff.mp h).2.2 n (.writeFlagFalse i) he
  generalize hdst : E.state (n + 1) = t at hs
  cases hs
  simp_all [passageStage, State.setPC, Function.update]

/-- Each entry crosses from the waiting stage into the critical stage. -/
theorem entry_stage {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {n : ℕ} (he : Entry E i n) :
    passageStage ((E.state n).pc i) = 2 ∧
      2 < passageStage ((E.state (n + 1)).pc i) := by
  obtain ⟨a, ha, hi, hn, ht⟩ := he
  have hs := (valid_iff.mp h).2.2 n a ha
  generalize hdst : E.state (n + 1) = t at hs
  cases hs <;> simp_all [actor, passageStage, State.setPC, State.setFlag,
    State.setTurn, Function.update]

/-- An actor makes its optional request write at most once, including padded runs. -/
theorem request_unique {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {m n : ℕ}
    (hm : Request E i m) (hn : Request E i n) : m = n := by
  exact stage_crossing_unique (valid_passageStage_mono h i)
    (request_stage h hm) (request_stage h hn)

/-- An actor writes turn at most once, regardless of the label's value argument. -/
theorem writeTurn_unique {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i v w : Proc} {m n : ℕ}
    (hm : E.event m = some (.writeTurn i v))
    (hn : E.event n = some (.writeTurn i w)) : m = n := by
  exact stage_crossing_unique (valid_passageStage_mono h i)
    (writeTurn_stage h hm) (writeTurn_stage h hn)

/-- An actor clears its flag at most once. -/
theorem writeFlagFalse_unique {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {m n : ℕ}
    (hm : E.event m = some (.writeFlagFalse i))
    (hn : E.event n = some (.writeFlagFalse i)) : m = n := by
  exact stage_crossing_unique (valid_passageStage_mono h i)
    (writeFlagFalse_stage h hm) (writeFlagFalse_stage h hn)

/-- An actor enters at most once; continued old occupancy is not another entry. -/
theorem entry_unique {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {m n : ℕ}
    (hm : Entry E i m) (hn : Entry E i n) : m = n := by
  exact stage_crossing_unique (valid_passageStage_mono h i)
    (entry_stage h hm) (entry_stage h hn)

/-- Every participating position enables an actual outcome, favorable or otherwise. -/
theorem protocol_enabled (order : WaitOrder) (i : Proc) (s : State)
    (hp : Protocol i s) : Enabled order i s := by
  refine ⟨hp, ?_⟩
  rcases hp with (hp | hp | hp) | hp
  · exact ⟨_, _, rfl, Step.writeTurn hp⟩
  · cases order with
    | flagFirst =>
      cases hf : s.flag i.other with
      | false => exact ⟨_, _, rfl, Step.flagFirstReadFlagFalse rfl hp hf⟩
      | true => exact ⟨_, _, rfl, Step.flagFirstReadFlagTrue rfl hp hf⟩
    | turnFirst =>
      have ht : s.turn = i ∨ s.turn = i.other := by cases i <;> cases s.turn <;> simp [Proc.other]
      rcases ht with ht | ht
      · exact ⟨_, _, rfl, Step.turnFirstReadTurnSelf rfl hp ht⟩
      · exact ⟨_, _, rfl, Step.turnFirstReadTurnOther rfl hp ht⟩
  · cases order with
    | flagFirst =>
      have ht : s.turn = i ∨ s.turn = i.other := by cases i <;> cases s.turn <;> simp [Proc.other]
      rcases ht with ht | ht
      · exact ⟨_, _, rfl, Step.flagFirstReadTurnSelf rfl hp ht⟩
      · exact ⟨_, _, rfl, Step.flagFirstReadTurnOther rfl hp ht⟩
    | turnFirst =>
      cases hf : s.flag i.other with
      | false => exact ⟨_, _, rfl, Step.turnFirstReadFlagFalse rfl hp hf⟩
      | true => exact ⟨_, _, rfl, Step.turnFirstReadFlagTrue rfl hp hf⟩
  · exact ⟨_, _, rfl, Step.writeFlagFalse hp⟩

/-- Without a participating actor step, its protocol counter stays fixed. -/
theorem protocol_pc_succ_of_not_taken {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {n : ℕ}
    (hp : Protocol i (E.state n)) (hn : ¬ Taken E i n) :
    (E.state (n + 1)).pc i = (E.state n).pc i := by
  cases he : E.event n with
  | none => rw [(valid_iff.mp h).2.1 n he]
  | some a =>
    apply step_pc_of_ne_actor ((valid_iff.mp h).2.2 n a he)
    intro hi
    exact hn ⟨hp, a, he, hi.symm⟩

/-- Exact weak fairness supplies a next step from any participating observation. -/
theorem next_protocol_step {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (hf : ProtocolFair order E) {i : Proc} {m : ℕ}
    (hp : Protocol i (E.state m)) : ∃ n, m ≤ n ∧ Taken E i n := by
  by_contra hn
  have hnot : ∀ n, m ≤ n → ¬ Taken E i n := by
    intro n hmn ht
    exact hn ⟨n, hmn, ht⟩
  have persists : ∀ k, m ≤ k → Protocol i (E.state k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hp
    | succ k hk ih =>
      have he := protocol_pc_succ_of_not_taken h ih (hnot k hk)
      simpa only [Protocol, Pending, he] using ih
  exact hn (hf i m (fun k hk => protocol_enabled order i (E.state k) (persists k hk)))

/-- A one-time event has some later suffix on which it never occurs. -/
private theorem eventually_not_of_unique {P : ℕ → Prop}
    (hu : ∀ m n, P m → P n → m = n) : ∃ N, ∀ n, N ≤ n → ¬ P n := by
  by_cases hex : ∃ m, P m
  · obtain ⟨m, hm⟩ := hex
    refine ⟨m + 1, ?_⟩
    intro n hn hp
    have he := hu m n hm hp
    omega
  · exact ⟨0, fun n _ hp => hex ⟨n, hp⟩⟩

/-- Precisely the three kinds of shared-memory write in the original model. -/
def SharedWrite : Action → Prop
  | .writeFlagTrue _ | .writeTurn _ _ | .writeFlagFalse _ => True
  | _ => False

/-- Each actor eventually has no remaining shared writes, even if it starts late. -/
theorem actor_writes_eventually_absent {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (i : Proc) :
    ∃ N, ∀ n, N ≤ n → ∀ a, E.event n = some a → actor a = i → ¬ SharedWrite a := by
  obtain ⟨R, hR⟩ := eventually_not_of_unique (fun _ _ => @request_unique order E h i _ _)
  obtain ⟨T, hT⟩ := eventually_not_of_unique (P := fun n => ∃ v, E.event n = some (.writeTurn i v))
    (by
      intro m n hm hn
      obtain ⟨v, hv⟩ := hm
      obtain ⟨w, hw⟩ := hn
      exact writeTurn_unique h hv hw)
  obtain ⟨F, hF⟩ := eventually_not_of_unique
    (fun _ _ => @writeFlagFalse_unique order E h i _ _)
  refine ⟨max R (max T F), ?_⟩
  intro n hn a he hi hw
  have hr : R ≤ n := by omega
  have ht : T ≤ n := by omega
  have hf : F ≤ n := by omega
  cases a <;> simp_all [SharedWrite, actor, Request]

/-- All actual shared writes lie before some observation, without a time bound. -/
theorem shared_writes_eventually_absent {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) :
    ∃ N, ∀ n, N ≤ n → ∀ a, E.event n = some a → ¬ SharedWrite a := by
  obtain ⟨A, hA⟩ := actor_writes_eventually_absent h .p1
  obtain ⟨B, hB⟩ := actor_writes_eventually_absent h .p2
  refine ⟨max A B, ?_⟩
  intro n hn a he
  cases hi : actor a with
  | p1 => exact hA n (by omega) a he hi
  | p2 => exact hB n (by omega) a he hi

/-- Reads and opaque critical completion leave both shared fields untouched. -/
theorem step_shared_eq_of_not_write {order : WaitOrder} {s t : State} {a : Action}
    (h : Step order s a t) (hw : ¬ SharedWrite a) :
    t.flag = s.flag ∧ t.turn = s.turn := by
  cases h <;> simp_all [SharedWrite, State.setPC]

/-- A write-free tick, including padding, preserves shared memory exactly. -/
theorem valid_shared_succ_of_no_write {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {n : ℕ}
    (hw : ∀ a, E.event n = some a → ¬ SharedWrite a) :
    (E.state (n + 1)).flag = (E.state n).flag ∧
      (E.state (n + 1)).turn = (E.state n).turn := by
  cases he : E.event n with
  | none => rw [(valid_iff.mp h).2.1 n he]; exact ⟨rfl, rfl⟩
  | some a => exact step_shared_eq_of_not_write ((valid_iff.mp h).2.2 n a he) (hw a he)

/-- A suffix after all actual writes has constant flags and turn; counters may move. -/
theorem shared_fields_stabilize {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) :
    ∃ N, (∀ n, N ≤ n → ∀ a, E.event n = some a → ¬ SharedWrite a) ∧
      ∀ n, N ≤ n → (E.state n).flag = (E.state N).flag ∧
        (E.state n).turn = (E.state N).turn := by
  obtain ⟨N, hN⟩ := shared_writes_eventually_absent h
  refine ⟨N, hN, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ n hn ih =>
    obtain ⟨hf, ht⟩ := valid_shared_succ_of_no_write h (hN n hn)
    exact ⟨hf.trans ih.1, ht.trans ih.2⟩

/-- An actor at either shared-write counter can only take a shared write. -/
theorem step_write_counter {order : WaitOrder} {s t : State} {a : Action} {i : Proc}
    (h : Step order s a t) (hi : actor a = i)
    (hp : s.pc i = .betweenWrites ∨ s.pc i = .beforeExitWrite) : SharedWrite a := by
  cases h <;> simp_all [actor, SharedWrite]

/-- Exact protocol fairness excludes write counters throughout a write-free suffix. -/
theorem no_write_suffix_write_counters {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (hf : ProtocolFair order E) {N : ℕ}
    (hw : ∀ n, N ≤ n → ∀ a, E.event n = some a → ¬ SharedWrite a)
    {m : ℕ} (hm : N ≤ m) (i : Proc) :
    (E.state m).pc i ≠ .betweenWrites ∧ (E.state m).pc i ≠ .beforeExitWrite := by
  have exclude (hp : (E.state m).pc i = .betweenWrites ∨
      (E.state m).pc i = .beforeExitWrite) : False := by
    have persists : ∀ k, m ≤ k → (E.state k).pc i = (E.state m).pc i := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih =>
        have hpk : Protocol i (E.state k) := by
          rcases hp with hp | hp
          · exact Or.inl (Or.inl (ih.trans hp))
          · exact Or.inr (ih.trans hp)
        have hn : ¬ Taken E i k := by
          rintro ⟨_, a, he, hi⟩
          exact hw k (by omega) a he
            (step_write_counter ((valid_iff.mp h).2.2 k a he) hi (by simpa [ih] using hp))
        exact (protocol_pc_succ_of_not_taken h hpk hn).trans ih
    have hpm : Protocol i (E.state m) := by
      rcases hp with hp | hp
      · exact Or.inl (Or.inl hp)
      · exact Or.inr hp
    obtain ⟨n, hn, _, a, he, hi⟩ := next_protocol_step h hf hpm
    exact hw n (by omega) a he
      (step_write_counter ((valid_iff.mp h).2.2 n a he) hi
        (by simpa [persists n hn] using hp))
  exact ⟨fun hp => exclude (Or.inl hp), fun hp => exclude (Or.inr hp)⟩

/-- Completion discharges old occupants: their exit write contradicts the suffix. -/
theorem no_write_suffix_no_critical {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (hf : ProtocolFair order E) (hc : CriticalCompletes E) {N : ℕ}
    (hw : ∀ n, N ≤ n → ∀ a, E.event n = some a → ¬ SharedWrite a)
    {m : ℕ} (hm : N ≤ m) (i : Proc) : (E.state m).pc i ≠ .critical := by
  intro hp
  obtain ⟨n, hn, he⟩ := hc i m hp
  have hs := (valid_iff.mp h).2.2 n (.finishCritical i) he
  have hexit : (E.state (n + 1)).pc i = .beforeExitWrite := by
    generalize ht : E.state (n + 1) = t at hs ⊢
    cases hs
    simp [State.setPC]
  exact (no_write_suffix_write_counters h hf hw (by omega) i).2 hexit

/-- Without future entry, an original pending actor is a reader on the suffix. -/
theorem pending_reader_on_no_write_suffix {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (hf : ProtocolFair order E) {N m : ℕ}
    (hw : ∀ n, N ≤ n → ∀ a, E.event n = some a → ¬ SharedWrite a)
    {i : Proc} (hp : Pending i (E.state m))
    (hne : ∀ j n, m ≤ n → ¬ Entry E j n) :
    ∀ n, max N m ≤ n →
      (E.state n).pc i = .beforeFirstRead ∨ (E.state n).pc i = .betweenReads := by
  intro n hn
  have hpn := pending_of_no_entry h (n := n) (by omega) hp (fun r hr _ => hne i r hr)
  rcases hpn with hb | hr
  · exact False.elim ((no_write_suffix_write_counters h hf hw (by omega) i).1 hb)
  · exact hr

/-- The first later participating step still sees the actor's original counter. -/
theorem first_protocol_step {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) (hf : ProtocolFair order E) {i : Proc} {m : ℕ}
    (hp : Protocol i (E.state m)) :
    ∃ n, m ≤ n ∧ Taken E i n ∧ (E.state n).pc i = (E.state m).pc i := by
  classical
  have hex := next_protocol_step h hf hp
  let n := Nat.find hex
  have hn : m ≤ n ∧ Taken E i n := Nat.find_spec hex
  refine ⟨n, hn.1, hn.2, ?_⟩
  have persists : ∀ k, m ≤ k → k ≤ n → (E.state k).pc i = (E.state m).pc i := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; rfl
    | succ k hk ih =>
      intro hkn
      have he := ih (by omega)
      have hpk : Protocol i (E.state k) := by simpa only [Protocol, Pending, he] using hp
      have hnot : ¬ Taken E i k := by
        intro ht
        have hmin := Nat.find_min' hex (show m ≤ k ∧ Taken E i k from ⟨hk, ht⟩)
        change n ≤ k at hmin
        omega
      exact (protocol_pc_succ_of_not_taken h hpk hnot).trans he
  exact persists n hn.1 le_rfl

/-- A flag-first reader enters or advances exactly one of its two separate reads. -/
theorem flagFirst_step_read {s t : State} {a : Action} {i : Proc}
    (h : Step .flagFirst s a t) (hi : actor a = i)
    (hp : s.pc i = .beforeFirstRead ∨ s.pc i = .betweenReads) :
    t.pc i = .critical ∨
      (s.pc i = .beforeFirstRead ∧ s.flag i.other = true ∧ t.pc i = .betweenReads) ∨
      (s.pc i = .betweenReads ∧ s.turn = i ∧ t.pc i = .beforeFirstRead) := by
  cases h <;> simp_all [actor, State.setPC]

/-- The next flag-first actor read preserves the saved position until that read. -/
theorem flagFirst_next_read {E : ProgressExecution}
    (h : Valid .flagFirst E) (hf : ProtocolFair .flagFirst E) {i : Proc} {m : ℕ}
    (hp : (E.state m).pc i = .beforeFirstRead ∨ (E.state m).pc i = .betweenReads) :
    ∃ n, m ≤ n ∧ (Entry E i n ∨
      ((E.state m).pc i = .beforeFirstRead ∧ (E.state n).flag i.other = true ∧
        (E.state (n + 1)).pc i = .betweenReads) ∨
      ((E.state m).pc i = .betweenReads ∧ (E.state n).turn = i ∧
        (E.state (n + 1)).pc i = .beforeFirstRead)) := by
  obtain ⟨n, hn, ht, hpc⟩ := first_protocol_step h hf (Or.inl (Or.inr hp))
  obtain ⟨_, a, he, hi⟩ := ht
  have hpn : (E.state n).pc i = .beforeFirstRead ∨ (E.state n).pc i = .betweenReads := by
    simpa [hpc] using hp
  rcases flagFirst_step_read ((valid_iff.mp h).2.2 n a he) hi hpn with hc | hr
  · refine ⟨n, hn, Or.inl ⟨a, he, hi, ?_, hc⟩⟩
    rcases hpn with hp | hp <;> simp [hp]
  · exact ⟨n, hn, Or.inr (by simpa [hpc] using hr)⟩

/--
A flag-first reader with a permanently false peer flag or favorable turn enters
at a later tick. Either saved read position is allowed; each scheduling witness
still performs just one original atomic read.
-/
theorem flagFirst_favorable_reader_entry {E : ProgressExecution}
    (h : Valid .flagFirst E) (hf : ProtocolFair .flagFirst E) {i : Proc} {m : ℕ}
    (hp : (E.state m).pc i = .beforeFirstRead ∨ (E.state m).pc i = .betweenReads)
    (hs : (∀ n, m ≤ n → (E.state n).flag i.other = false) ∨
      (∀ n, m ≤ n → (E.state n).turn = i.other)) :
    ∃ n, m ≤ n ∧ Entry E i n := by
  obtain ⟨n, hn, he | ⟨_, hflag, hpnext⟩ | ⟨_, hturn, hpnext⟩⟩ :=
    flagFirst_next_read h hf hp
  · exact ⟨n, hn, he⟩
  · rcases hs with hs | hs
    · simp [hs n hn] at hflag
    · obtain ⟨r, hr, he | ⟨hbad, _, _⟩ | ⟨_, hbad, _⟩⟩ :=
        flagFirst_next_read h hf (Or.inr hpnext)
      · exact ⟨r, by omega, he⟩
      · simp [hpnext] at hbad
      · have hother := hs r (by omega)
        cases i <;> simp_all [Proc.other]
  · rcases hs with hs | hs
    · obtain ⟨r, hr, he | ⟨_, hbad, _⟩ | ⟨hbad, _, _⟩⟩ :=
        flagFirst_next_read h hf (Or.inl hpnext)
      · exact ⟨r, by omega, he⟩
      · simp [hs r (by omega)] at hbad
      · simp [hpnext] at hbad
    · have hother := hs n hn
      cases i <;> simp_all [Proc.other]

/-- The accepted future-entry conclusion for the fixed flag-first guard order. -/
theorem flagFirst_progress {E : ProgressExecution}
    (h : Valid .flagFirst E) (hf : ProtocolFair .flagFirst E) (hc : CriticalCompletes E)
    (m : ℕ) (hp : ∃ i, Pending i (E.state m)) :
    ∃ j n, m ≤ n ∧ Entry E j n := by
  by_contra hno
  have hne : ∀ j n, m ≤ n → ¬ Entry E j n := by
    intro j n hn he
    exact hno ⟨j, n, hn, he⟩
  obtain ⟨N, hw, hs⟩ := shared_fields_stabilize h
  obtain ⟨i, hp⟩ := hp
  let k := max N m
  have hNk : N ≤ k := Nat.le_max_left _ _
  have hmk : m ≤ k := Nat.le_max_right _ _
  have hi := pending_reader_on_no_write_suffix h hf hw hp hne k le_rfl
  have force (j : Proc)
      (hj : (E.state k).pc j = .beforeFirstRead ∨ (E.state k).pc j = .betweenReads)
      (hfavorable : (∀ n, k ≤ n → (E.state n).flag j.other = false) ∨
        (∀ n, k ≤ n → (E.state n).turn = j.other)) : False := by
    obtain ⟨n, hn, he⟩ := flagFirst_favorable_reader_entry h hf hj hfavorable
    exact hne j n (by omega) he
  cases hflag : (E.state k).flag i.other with
  | false =>
    apply force i hi (Or.inl ?_)
    intro n hn
    rw [(hs n (by omega)).1, ← (hs k hNk).1]
    exact hflag
  | true =>
    by_cases ht : (E.state N).turn = i.other
    · apply force i hi (Or.inr ?_)
      intro n hn
      exact (hs n (by omega)).2.trans ht
    · have hpeer := (valid_flag_iff_interested h i.other k).mp hflag
      obtain ⟨hb, he⟩ := no_write_suffix_write_counters h hf hw hNk i.other
      have hcpeer := no_write_suffix_no_critical h hf hc hw hNk i.other
      have hj : (E.state k).pc i.other = .beforeFirstRead ∨
          (E.state k).pc i.other = .betweenReads := by
        change Interested ((E.state k).pc i.other) at hpeer
        cases hpc : (E.state k).pc i.other <;> simp_all [Interested]
      apply force i.other hj (Or.inr ?_)
      intro n hn
      rw [(hs n (by omega)).2]
      cases i <;> cases hturn : (E.state N).turn <;> simp_all [Proc.other]

/-- A turn-first reader enters or advances exactly one of its two separate reads. -/
theorem turnFirst_step_read {s t : State} {a : Action} {i : Proc}
    (h : Step .turnFirst s a t) (hi : actor a = i)
    (hp : s.pc i = .beforeFirstRead ∨ s.pc i = .betweenReads) :
    t.pc i = .critical ∨
      (s.pc i = .beforeFirstRead ∧ s.turn = i ∧ t.pc i = .betweenReads) ∨
      (s.pc i = .betweenReads ∧ s.flag i.other = true ∧ t.pc i = .beforeFirstRead) := by
  cases h <;> simp_all [actor, State.setPC]

/-- The next turn-first actor read preserves the saved position until that read. -/
theorem turnFirst_next_read {E : ProgressExecution}
    (h : Valid .turnFirst E) (hf : ProtocolFair .turnFirst E) {i : Proc} {m : ℕ}
    (hp : (E.state m).pc i = .beforeFirstRead ∨ (E.state m).pc i = .betweenReads) :
    ∃ n, m ≤ n ∧ (Entry E i n ∨
      ((E.state m).pc i = .beforeFirstRead ∧ (E.state n).turn = i ∧
        (E.state (n + 1)).pc i = .betweenReads) ∨
      ((E.state m).pc i = .betweenReads ∧ (E.state n).flag i.other = true ∧
        (E.state (n + 1)).pc i = .beforeFirstRead)) := by
  obtain ⟨n, hn, ht, hpc⟩ := first_protocol_step h hf (Or.inl (Or.inr hp))
  obtain ⟨_, a, he, hi⟩ := ht
  have hpn : (E.state n).pc i = .beforeFirstRead ∨ (E.state n).pc i = .betweenReads := by
    simpa [hpc] using hp
  rcases turnFirst_step_read ((valid_iff.mp h).2.2 n a he) hi hpn with hc | hr
  · refine ⟨n, hn, Or.inl ⟨a, he, hi, ?_, hc⟩⟩
    rcases hpn with hp | hp <;> simp [hp]
  · exact ⟨n, hn, Or.inr (by simpa [hpc] using hr)⟩

/-- A turn-first reader enters after at most two separately scheduled favorable reads. -/
theorem turnFirst_favorable_reader_entry {E : ProgressExecution}
    (h : Valid .turnFirst E) (hf : ProtocolFair .turnFirst E) {i : Proc} {m : ℕ}
    (hp : (E.state m).pc i = .beforeFirstRead ∨ (E.state m).pc i = .betweenReads)
    (hs : (∀ n, m ≤ n → (E.state n).flag i.other = false) ∨
      (∀ n, m ≤ n → (E.state n).turn = i.other)) :
    ∃ n, m ≤ n ∧ Entry E i n := by
  obtain ⟨n, hn, he | ⟨_, hturn, hpnext⟩ | ⟨_, hflag, hpnext⟩⟩ :=
    turnFirst_next_read h hf hp
  · exact ⟨n, hn, he⟩
  · rcases hs with hs | hs
    · obtain ⟨r, hr, he | ⟨hbad, _, _⟩ | ⟨_, hbad, _⟩⟩ :=
        turnFirst_next_read h hf (Or.inr hpnext)
      · exact ⟨r, by omega, he⟩
      · simp [hpnext] at hbad
      · simp [hs r (by omega)] at hbad
    · have hother := hs n hn
      cases i <;> simp_all [Proc.other]
  · rcases hs with hs | hs
    · simp [hs n hn] at hflag
    · obtain ⟨r, hr, he | ⟨_, hbad, _⟩ | ⟨hbad, _, _⟩⟩ :=
        turnFirst_next_read h hf (Or.inl hpnext)
      · exact ⟨r, by omega, he⟩
      · have hother := hs r (by omega)
        cases i <;> simp_all [Proc.other]
      · simp [hpnext] at hbad

/-- The accepted future-entry conclusion for the fixed turn-first guard order. -/
theorem turnFirst_progress {E : ProgressExecution}
    (h : Valid .turnFirst E) (hf : ProtocolFair .turnFirst E) (hc : CriticalCompletes E)
    (m : ℕ) (hp : ∃ i, Pending i (E.state m)) :
    ∃ j n, m ≤ n ∧ Entry E j n := by
  by_contra hno
  have hne : ∀ j n, m ≤ n → ¬ Entry E j n := by
    intro j n hn he
    exact hno ⟨j, n, hn, he⟩
  obtain ⟨N, hw, hs⟩ := shared_fields_stabilize h
  obtain ⟨i, hp⟩ := hp
  let k := max N m
  have hNk : N ≤ k := Nat.le_max_left _ _
  have hmk : m ≤ k := Nat.le_max_right _ _
  have hi := pending_reader_on_no_write_suffix h hf hw hp hne k le_rfl
  have force (j : Proc)
      (hj : (E.state k).pc j = .beforeFirstRead ∨ (E.state k).pc j = .betweenReads)
      (hfavorable : (∀ n, k ≤ n → (E.state n).flag j.other = false) ∨
        (∀ n, k ≤ n → (E.state n).turn = j.other)) : False := by
    obtain ⟨n, hn, he⟩ := turnFirst_favorable_reader_entry h hf hj hfavorable
    exact hne j n (by omega) he
  cases hflag : (E.state k).flag i.other with
  | false =>
    apply force i hi (Or.inl ?_)
    intro n hn
    rw [(hs n (by omega)).1, ← (hs k hNk).1]
    exact hflag
  | true =>
    by_cases ht : (E.state N).turn = i.other
    · apply force i hi (Or.inr ?_)
      intro n hn
      exact (hs n (by omega)).2.trans ht
    · have hpeer := (valid_flag_iff_interested h i.other k).mp hflag
      obtain ⟨hb, he⟩ := no_write_suffix_write_counters h hf hw hNk i.other
      have hcpeer := no_write_suffix_no_critical h hf hc hw hNk i.other
      have hj : (E.state k).pc i.other = .beforeFirstRead ∨
          (E.state k).pc i.other = .betweenReads := by
        change Interested ((E.state k).pc i.other) at hpeer
        cases hpc : (E.state k).pc i.other <;> simp_all [Interested]
      apply force i.other hj (Or.inr ?_)
      intro n hn
      rw [(hs n (by omega)).2]
      cases i <;> cases hturn : (E.state N).turn <;> simp_all [Proc.other]

/-- The exact protected global future-entry theorem for both fixed read orders. -/
theorem peterson_global_progress : PetersonGlobalProgress := by
  intro order E h hf hc m hp
  cases order with
  | flagFirst => exact flagFirst_progress h hf hc m hp
  | turnFirst => exact turnFirst_progress h hf hc m hp

end Peterson
