import Peterson.Repeated.Progress
import Peterson.Repeated.TraceTests
import Peterson.ProgressExamples

/-! Infinite padded repeated runs and premise-removal witnesses. -/
namespace Peterson.Repeated

theorem protocolFair_of_eventually_not_protocol {order : WaitOrder} {E : Execution}
    (h : ∀ i m, ∃ n, m ≤ n ∧ ¬ Protocol i (E.state n)) : ProtocolFair order E := by
  intro i m hen
  obtain ⟨n, hmn, hn⟩ := h i m
  exact (hn (hen n hmn).1).elim

theorem critical_succ_of_not_finish {order : WaitOrder} {E : Execution}
    (h : Valid order E) {i : Proc} {n : ℕ}
    (hc : (E.state n).pc i = .critical) (hf : ¬ Finish E i n) :
    (E.state (n + 1)).pc i = .critical :=
  boundary_pc_succ h (Or.inl ⟨rfl, rfl⟩) hc hf

theorem completes_of_exit {order : WaitOrder}
    {E : Execution} (h : Valid order E)
    (ht : ∀ i m, ∃ n, m ≤ n ∧ (E.state n).pc i ≠ .critical) :
    CriticalCompletes E := by
  intro i m hc
  by_contra hf
  obtain ⟨n, hmn, hn⟩ := ht i m
  have hp : ∀ d, (E.state (m + d)).pc i = .critical := by
    intro d
    induction d with
    | zero => simpa using hc
    | succ d ih =>
      have hnf : ¬ Finish E i (m + d) := by
        intro he
        exact hf ⟨m + d, Nat.le_add_right m d, he⟩
      exact critical_succ_of_not_finish h ih hnf
  exact hn (by simpa [Nat.add_sub_of_le hmn] using hp (n - m))

theorem terminal_padding_admissible {order : WaitOrder} {E : Execution}
    {t : State} {N : ℕ} (h : Valid order E)
    (ht : ∀ n, E.state (N + n) = t)
    (hp : ∀ i, ¬ Protocol i t) (hc : ∀ i, t.pc i ≠ .critical) :
    ProtocolFair order E ∧ CriticalCompletes E := by
  constructor
  · apply protocolFair_of_eventually_not_protocol
    intro i m
    exact ⟨N + m, Nat.le_add_left m N, by rw [ht m]; exact hp i⟩
  · apply completes_of_exit h
    intro i m
    exact ⟨N + m, Nat.le_add_left m N, by rw [ht m]; exact hc i⟩

/-- Every finite list of complete passages has an admissible infinite padded continuation. -/
theorem cycles_admissible (order : WaitOrder) (turn : Proc) (actors : List Proc) :
    ∃ E : Execution, Valid order E ∧ ProtocolFair order E ∧ CriticalCompletes E ∧
      ∀ n (hn : n < (actors.flatMap (TraceTests.cycleActions order)).length),
        E.event n = some ((actors.flatMap (TraceTests.cycleActions order))[n]) := by
  obtain ⟨finalTurn, htrace⟩ := TraceTests.cycles order turn actors
  obtain ⟨E, hv, _, hevents, htail⟩ :=
    mTr_exists_valid_padding (Peterson.TraceTests.root_initial turn) htrace
  have hadm := terminal_padding_admissible hv (fun n => (htail n).1)
    (by intro i; simp [Protocol, Pending, Peterson.TraceTests.root])
    (by intro i; simp [Peterson.TraceTests.root])
  exact ⟨E, hv, hadm.1, hadm.2, hevents⟩

/-- Two requests by one actor are genuinely present and individually served. -/
theorem two_requests_served (order : WaitOrder) (turn i : Proc) :
    ∃ E : Execution, Valid order E ∧ ProtocolFair order E ∧ CriticalCompletes E ∧
      Request E i 0 ∧ Request E i (TraceTests.cycleActions order i).length ∧
      (∃ n, Serves E i 0 n) ∧
      (∃ n, Serves E i (TraceTests.cycleActions order i).length n) := by
  obtain ⟨E, hv, hf, hc, he⟩ := cycles_admissible order turn [i, i]
  have hr : Request E i 0 := by
    have hh := he 0 (by cases order <;> simp [TraceTests.cycleActions])
    cases order <;> simpa [Request, TraceTests.cycleActions] using hh
  have hr2 : Request E i (TraceTests.cycleActions order i).length := by
    have hh := he (TraceTests.cycleActions order i).length (by cases order <;> simp [TraceTests.cycleActions])
    cases order <;> simpa [Request, TraceTests.cycleActions] using hh
  exact ⟨E, hv, hf, hc, hr, hr2, repeated_request_entry order E hv hf hc i 0 hr,
    repeated_request_entry order E hv hf hc i _ hr2⟩

/-- Old-model executions embed only in this direction; they supply valid special-case tests. -/
def embed (E : ProgressExecution) : Execution where
  state := E.state
  event n := (E.event n).map RepeatedAction.protocol

theorem embed_valid {order : WaitOrder} {E : ProgressExecution} (h : Peterson.Valid order E) :
    Valid order (embed E) := by
  refine ⟨h.1, ?_⟩
  intro n
  have hs := h.2 n
  cases he : E.event n with
  | none => simpa [embed, observationLTS, Peterson.observationLTS, he] using hs
  | some a =>
    have hp : Peterson.Step order (E.state n) a (E.state (n + 1)) := by
      simpa [Peterson.observationLTS, he] using hs
    simpa [embed, observationLTS, he] using Step.protocol hp

theorem embed_taken (E : ProgressExecution) (i : Proc) (n : ℕ) :
    Taken (embed E) i n ↔ Peterson.Taken E i n := by
  simp [Taken, Peterson.Taken, embed]

theorem embed_entry (E : ProgressExecution) (i : Proc) (n : ℕ) :
    Entry (embed E) i n ↔ Peterson.Entry E i n := by
  simp [Entry, Peterson.Entry, embed]

theorem embed_fair {order : WaitOrder} {E : ProgressExecution} :
    ProtocolFair order (embed E) ↔ Peterson.ProtocolFair order E := by
  simp only [ProtocolFair, Peterson.ProtocolFair, embed_taken]
  rfl

theorem embed_completes {E : ProgressExecution} :
    CriticalCompletes (embed E) ↔ Peterson.CriticalCompletes E := by
  simp [CriticalCompletes, Peterson.CriticalCompletes, Finish, Peterson.Finish, embed]

/-- Neglecting a participant still defeats progress in the repeated model. -/
theorem protocol_neglect_counterexample (order : WaitOrder) (turn i : Proc) :
    Valid order (embed (Peterson.protocolNeglect order turn i)) ∧
    CriticalCompletes (embed (Peterson.protocolNeglect order turn i)) ∧
    ¬ ProtocolFair order (embed (Peterson.protocolNeglect order turn i)) ∧
    (∀ j n, ¬ Entry (embed (Peterson.protocolNeglect order turn i)) j n) := by
  refine ⟨embed_valid (Peterson.protocolNeglect_valid order turn i),
    embed_completes.mpr (Peterson.protocolNeglect_completion_no_entry order turn i).1,
    fun hf => Peterson.protocolNeglect_not_fair order turn i (embed_fair.mp hf), ?_⟩
  intro j n he
  exact (Peterson.protocolNeglect_completion_no_entry order turn i).2 j n
    ((embed_entry _ _ _).mp he)

/-- Fair reads do not compensate for an occupant that never finishes critical work. -/
theorem critical_neglect_counterexample (order : WaitOrder) (turn i : Proc) :
    Valid order (embed (Peterson.criticalNeglect order turn i)) ∧
    ProtocolFair order (embed (Peterson.criticalNeglect order turn i)) ∧
    ¬ CriticalCompletes (embed (Peterson.criticalNeglect order turn i)) ∧
    ¬ ∃ j n, (if order = .flagFirst then 5 else 6) ≤ n ∧
      Entry (embed (Peterson.criticalNeglect order turn i)) j n := by
  obtain ⟨hv, hf, hc, _, hno⟩ := Peterson.criticalNeglect_counterexample order turn i
  refine ⟨embed_valid hv, embed_fair.mpr hf, fun h => hc (embed_completes.mp h), ?_⟩
  rintro ⟨j, n, hn, he⟩
  exact hno ⟨j, n, hn, (embed_entry _ _ _).mp he⟩

/-- Fairness must cover the exit write, not just the pending readers. -/
theorem exit_neglect_counterexample (order : WaitOrder) (turn i : Proc) :
    Valid order (embed (Peterson.exitNeglect order turn i)) ∧
    CriticalCompletes (embed (Peterson.exitNeglect order turn i)) ∧
    ¬ ProtocolFair order (embed (Peterson.exitNeglect order turn i)) ∧
    ¬ ∃ j n, (if order = .flagFirst then 6 else 7) ≤ n ∧
      Entry (embed (Peterson.exitNeglect order turn i)) j n := by
  obtain ⟨hv, hc, _, hf, _, hno, _⟩ := Peterson.exitNeglect_counterexample order turn i
  refine ⟨embed_valid hv, embed_completes.mpr hc, fun h => hf (embed_fair.mp h), ?_⟩
  rintro ⟨j, n, hn, he⟩
  exact hno ⟨j, n, hn, (embed_entry _ _ _).mp he⟩

end Peterson.Repeated
