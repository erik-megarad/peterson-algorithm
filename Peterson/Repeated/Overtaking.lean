import Peterson.Repeated.OvertakingSpecification
import Peterson.Repeated.Progress

namespace Peterson.Repeated

/-- A peer still reading owns TURN when this actor has not yet written it. -/
def ReaderTurn (s : State) : Prop :=
  ∀ i, Reader i.other s → ¬ TurnWritten (s.pc i) → s.turn = i.other

theorem readerTurn_step {order : WaitOrder} {s t : State} {a : RepeatedAction}
    (hs : Step order s a t) (hi : Invariant s) (hr : ReaderTurn s) : ReaderTurn t := by
  intro i
  have hr1 := hr i
  have hr2 := hr i.other
  have hi1 := (hi i).2
  have hi2 := (hi i.other).2
  cases hs with
  | protocol hs =>
    cases hs with
    | writeFlagTrue hp =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | writeTurn hp =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | flagFirstReadFlagFalse ho hp hv =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | flagFirstReadFlagTrue ho hp hv =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | flagFirstReadTurnOther ho hp hv =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | flagFirstReadTurnSelf ho hp hv =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | turnFirstReadTurnOther ho hp hv =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | turnFirstReadTurnSelf ho hp hv =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | turnFirstReadFlagFalse ho hp hv =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | turnFirstReadFlagTrue ho hp hv =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | finishCritical hp =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
    | writeFlagFalse hp =>
      rename_i j
      rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
        simp_all [Reader, TurnWritten, ReaderTurn, TurnExcludes, State.setPC, Function.update]
      intro hread
      rcases hread with hread | hread <;>
        cases j <;> cases ht : s.turn <;> simp_all [Proc.other]
  | restart hp =>
    rename_i j
    rcases Proc.eq_self_or_eq_other i j with rfl | rfl <;>
      simp_all [Reader, TurnWritten]

theorem readerTurn_reachable {order : WaitOrder} {s : State}
    (h : Reachable order s) : ReaderTurn s := by
  obtain ⟨s₀, hi, actions, ht⟩ := h
  have hinv : (repeatedLTS order).TrInv (fun s => Invariant s ∧ ReaderTurn s) := by
    intro s a t hs hh
    exact ⟨invariant_step order s a t hs hh.1, readerTurn_step hs hh.1 hh.2⟩
  apply (Cslib.LTS.mtrInv_of_trInv hinv s₀ actions s ht ?_).2
  refine ⟨Peterson.invariant_initial hi, ?_⟩
  intro i hr
  simp [Reader, hi.2] at hr

/-- All four successful read constructors satisfy this entry guard. -/
theorem entry_guard {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {n : ℕ} (he : Entry E i n) :
    Reader i (E.state n) ∧
      ((E.state n).flag i.other = false ∨ (E.state n).turn = i.other) := by
  obtain ⟨a, ha, hi, hn, hc⟩ := he
  have hs := protocol_step h ha
  generalize hdst : E.state (n + 1) = t at hs hc
  cases hs <;> simp_all [actor, Reader, State.setPC]

theorem pending_flag {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {n : ℕ} (hp : Pending i (E.state n)) : (E.state n).flag i = true := by
  apply (invariant_reachable (valid_reachable h n) i).1
  rcases hp with hp | hp | hp <;> simp [hp]

theorem no_peer_entry_betweenWrites {order : WaitOrder} {E : Execution}
    (h : Valid order E) {i : Proc} {n : ℕ}
    (hp : (E.state n).pc i = .betweenWrites) : ¬ Entry E i.other n := by
  intro he
  obtain ⟨hr, hg⟩ := entry_guard h he
  have ht := readerTurn_reachable (valid_reachable h n) i hr (by simp [hp, TurnWritten])
  have hf := pending_flag h (Or.inl hp)
  rcases hg with hg | hg <;> simp_all

theorem betweenWrites_succ {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {n : ℕ} (hp : (E.state n).pc i = .betweenWrites)
    (hw : ¬ TurnWrite E i n) : (E.state (n + 1)).pc i = .betweenWrites := by
  cases he : E.event n with
  | none => simpa [(valid_iff.mp h).2.1 n he] using hp
  | some a =>
    have hs := (valid_iff.mp h).2.2 n a he
    generalize hdst : E.state (n + 1) = t at hs ⊢
    cases hs with
    | protocol hs =>
      rename_i action
      by_cases hi : i = actor action
      · cases hs <;> simp_all [actor, TurnWrite]
      · exact (Peterson.step_pc_of_ne_actor hs hi).trans hp
    | restart hs => exact (restart_pc_eq hs (by simp [hp])).trans hp

theorem request_betweenWrites {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {r : ℕ} (hr : Request E i r) :
    (E.state (r + 1)).pc i = .betweenWrites := by
  have hs := protocol_step h hr
  generalize hdst : E.state (r + 1) = t at hs ⊢
  cases hs
  simp

/-- Finite history from the original flag edge to any later peer entry includes TURN. -/
theorem turn_before_peer_entry {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {r e : ℕ} (hr : Request E i r) (hre : r < e)
    (he : Entry E i.other e) : ∃ t, r < t ∧ t < e ∧ TurnWrite E i t := by
  by_contra hn
  have hp : ∀ k, r + 1 ≤ k → k ≤ e → (E.state k).pc i = .betweenWrites := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact request_betweenWrites h hr
    | succ k hk ih =>
      intro hke
      apply betweenWrites_succ h (ih (by omega))
      intro hw
      exact hn ⟨k, by omega, by omega, hw⟩
  exact no_peer_entry_betweenWrites h (hp e (by omega) le_rfl) he

/-- Finite reader persistence uses pending only up to the named endpoint. -/
theorem reader_interval {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {m b : ℕ} (hr : Reader i (E.state m))
    (hp : ∀ k, m < k → k ≤ b → Pending i (E.state k)) :
    ∀ k, m ≤ k → k ≤ b → Reader i (E.state k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; exact hr
  | succ k hk ih => intro hkb; exact reader_succ h (ih (by omega)) (hp _ (by omega) hkb)

/-- Finite TURN persistence: the pending reader cannot overwrite the peer's value. -/
theorem favorable_turn_interval {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {m b : ℕ} (hr : ∀ k, m ≤ k → k < b → Reader i (E.state k))
    (ht : (E.state m).turn = i.other) :
    ∀ k, m ≤ k → k ≤ b → (E.state k).turn = i.other := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; exact ht
  | succ k hk ih =>
    intro hkb
    rcases turn_succ h k with he | ⟨j, he, hj⟩
    · exact he.trans (ih (by omega))
    · rcases Proc.eq_self_or_eq_other i j with rfl | rfl
      · exact (reader_no_turn_write h (hr k hk (by omega)) he).elim
      · exact hj

/-- Entering the reader range from outside requires a fresh TURN edge. -/
theorem reader_succ_origin {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {k : ℕ} (hr : Reader i (E.state (k + 1))) :
    Reader i (E.state k) ∨ TurnWrite E i k := by
  cases he : E.event k with
  | none => exact Or.inl (by simpa [(valid_iff.mp h).2.1 k he] using hr)
  | some a =>
    have hs := (valid_iff.mp h).2.2 k a he
    generalize hdst : E.state (k + 1) = t at hs hr
    cases hs with
    | protocol hs =>
      rename_i action
      by_cases hi : i = actor action
      · cases hs <;> simp_all [Reader, actor, State.setPC, TurnWrite]
      · exact Or.inl (by simpa only [Reader, Peterson.step_pc_of_ne_actor hs hi] using hr)
    | restart hs =>
      rename_i j
      by_cases hij : i = j
      · subst j; simp [Reader] at hr
      · exact Or.inl (by simpa [Reader, State.setPC, Function.update, hij] using hr)

/-- Actual event history between any two entries contains a fresh peer TURN write.
Backward reader history suffices; it cannot cross the first critical state. -/
theorem turn_between_entries {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {a b : ℕ} (ha : Entry E i a) (hb : Entry E i b) (hab : a < b) :
    ∃ t, a < t ∧ t < b ∧ TurnWrite E i t := by
  by_contra hn
  have back : ∀ d, a + 1 ≤ b - d → Reader i (E.state (b - d)) := by
    intro d
    induction d with
    | zero => intro _; simpa using (entry_guard h hb).1
    | succ d ih =>
      intro hd
      have hp := ih (by omega)
      have heq : b - d = (b - (d + 1)) + 1 := by omega
      rw [heq] at hp
      rcases reader_succ_origin h hp with hp | hw
      · exact hp
      · exact (hn ⟨b - (d + 1), by omega, by omega, hw⟩).elim
  have hr := back (b - (a + 1)) (by omega)
  have hc := ha.choose_spec.2.2.2
  have heq : b - (b - (a + 1)) = a + 1 := by omega
  simp [heq, Reader, hc] at hr

/-- Two ordered counted entries contradict the fresh peer write and finite persistence. -/
theorem no_two_peer_entries {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {r b e f : ℕ} (hr : Request E i r) (hp : PendingThrough E i r b)
    (hre : r < e) (hef : e < f) (hfb : f < b)
    (he : Entry E i.other e) (hf : Entry E i.other f) : False := by
  obtain ⟨t, hrt, hte, htw⟩ := turn_before_peer_entry h hr hre he
  have hreader := reader_interval h
    (Or.inl (writeTurn_facts h htw).2.1 : Reader i (E.state (t + 1)))
    (fun k hk hkb => hp.2 k ⟨by omega, hkb⟩)
  obtain ⟨u, heu, huf, huw⟩ := turn_between_entries h he hf hef
  have hturn := favorable_turn_interval h (b := f)
    (fun k hk hkf => hreader k (by omega) (by omega)) (writeTurn_facts h huw).2.2
  have ht := hturn f (by omega) le_rfl
  have hflag := pending_flag h (hp.2 f ⟨by omega, by omega⟩)
  rcases (entry_guard h hf).2 with hg | hg <;> simp_all

@[simp] theorem mem_peerEntryIndices {E : Execution} {i : Proc} {a b k : ℕ} :
    k ∈ peerEntryIndices E i a b ↔ k < b ∧ a < k ∧ Entry E i.other k := by
  classical
  simp [peerEntryIndices]

/-- The reviewed primary bound starts at the original flag-write request. -/
theorem repeated_overtaking_bound : RepeatedOvertakingBound := by
  intro order E h i r b hr hp
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨heb, hre, he⟩ := mem_peerEntryIndices.mp he
  obtain ⟨hfb, hrf, hf⟩ := mem_peerEntryIndices.mp hf
  rcases lt_trichotomy e f with hef | hef | hfe
  · exact (no_two_peer_entries h hr hp hre hef hfb he hf).elim
  · exact hef
  · exact (no_two_peer_entries h hr hp hrf hfe heb hf he).elim

theorem repeated_pre_turn_zero : RepeatedPreTurnZero := by
  intro order E h i r b hr _ hw
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heb, hre, he⟩ := mem_peerEntryIndices.mp he
  obtain ⟨t, hrt, hte, ht⟩ := turn_before_peer_entry h hr hre he
  exact hw t ⟨hrt, by omega⟩ ht

theorem repeated_after_turn_bound : RepeatedAfterTurnBound := by
  intro order E h i r t b hr hp hrt _ _
  apply Nat.le_trans (Finset.card_le_card (show peerEntryIndices E i t b ⊆
      peerEntryIndices E i r b from ?_)) (repeated_overtaking_bound order E h i r b hr hp)
  intro k hk
  obtain ⟨hkb, htk, he⟩ := mem_peerEntryIndices.mp hk
  exact mem_peerEntryIndices.mpr ⟨hkb, by omega, he⟩

/-- Liveness retains exactly the existing fairness and completion premises. -/
theorem repeated_bounded_service : RepeatedBoundedService := by
  intro order E h hf hc i r hr
  obtain ⟨n, hn⟩ := repeated_request_entry order E h hf hc i r hr
  exact ⟨n, hn, repeated_overtaking_bound order E h i r n hr ⟨hn.1, hn.2.2⟩⟩

end Peterson.Repeated
