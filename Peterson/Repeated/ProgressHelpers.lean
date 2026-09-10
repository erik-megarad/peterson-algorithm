import Peterson.Repeated.Safety

/-! Per-request control flow and fair reads, with restart and padding handled explicitly. -/
namespace Peterson.Repeated

theorem protocol_step {order : WaitOrder} {E : Execution} (h : Valid order E)
    {n : ℕ} {a : Action} (he : E.event n = some (.protocol a)) :
    Peterson.Step order (E.state n) a (E.state (n + 1)) := by
  have hs := (valid_iff.mp h).2.2 n _ he
  cases hs with
  | protocol hs => exact hs

theorem restart_pc_eq {s : State} {i j : Proc} (hr : s.pc j = .afterPassage)
    (hi : s.pc i ≠ .afterPassage) : (s.setPC j .beforeFlag).pc i = s.pc i := by
  have hne : i ≠ j := by intro he; subst j; exact hi hr
  simp [State.setPC, Function.update, hne]

theorem request_pending {order : WaitOrder} {E : Execution}
    (h : Valid order E) {i : Proc} {n : ℕ} (hr : Request E i n) :
    Pending i (E.state (n + 1)) := by
  have hs := protocol_step h hr
  generalize hdst : E.state (n + 1) = t at hs
  cases hs
  simp [Pending, State.setPC, Function.update]

theorem pending_succ_of_not_entry {order : WaitOrder} {E : Execution}
    (h : Valid order E) {i : Proc} {n : ℕ} (hp : Pending i (E.state n))
    (hn : ¬ Entry E i n) : Pending i (E.state (n + 1)) := by
  cases he : E.event n with
  | none => simpa [(valid_iff.mp h).2.1 n he] using hp
  | some a =>
    have hs := (valid_iff.mp h).2.2 n a he
    generalize hdst : E.state (n + 1) = t at hs
    cases hs with
    | protocol hs =>
      rw [← hdst] at hs ⊢
      rcases Peterson.step_pending_or_entry hs hp with hp' | hent
      · exact hp'
      · exact (hn ⟨_, he, hent⟩).elim
    | restart hr =>
      have hi : (E.state n).pc i ≠ .afterPassage := by
        rcases hp with hp | hp | hp <;> simp [hp]
      simpa only [Pending, restart_pc_eq hr hi] using hp

theorem pending_of_no_entry {order : WaitOrder} {E : Execution}
    (h : Valid order E) {i : Proc} {m n : ℕ} (hmn : m ≤ n)
    (hp : Pending i (E.state m))
    (hn : ∀ r, m ≤ r → r < n → ¬ Entry E i r) : Pending i (E.state n) := by
  induction n, hmn using Nat.le_induction with
  | base => exact hp
  | succ n hmn ih =>
    exact pending_succ_of_not_entry h
      (ih (fun r hmr hrn => hn r hmr (Nat.lt_trans hrn (Nat.lt_succ_self n))))
      (hn n hmn (Nat.lt_succ_self n))

theorem protocol_enabled (order : WaitOrder) (i : Proc) (s : State)
    (hp : Protocol i s) : Enabled order i s := Peterson.protocol_enabled order i s hp

theorem protocol_pc_succ_of_not_taken {order : WaitOrder} {E : Execution}
    (h : Valid order E) {i : Proc} {n : ℕ}
    (hp : Protocol i (E.state n)) (hn : ¬ Taken E i n) :
    (E.state (n + 1)).pc i = (E.state n).pc i := by
  cases he : E.event n with
  | none => rw [(valid_iff.mp h).2.1 n he]
  | some a =>
    have hs := (valid_iff.mp h).2.2 n a he
    generalize hdst : E.state (n + 1) = t at hs
    cases hs with
    | protocol hs =>
      rw [← hdst] at hs ⊢
      apply Peterson.step_pc_of_ne_actor hs
      intro hi
      exact hn ⟨hp, _, he, hi.symm⟩
    | restart hr =>
      apply restart_pc_eq hr
      rcases hp with (hp | hp | hp) | hp <;> simp [hp]

theorem next_protocol_step {order : WaitOrder} {E : Execution}
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

theorem first_protocol_step {order : WaitOrder} {E : Execution}
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

theorem flagFirst_next_read {E : Execution}
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
  rcases flagFirst_step_read (protocol_step h he) hi hpn with hc | hr
  · refine ⟨n, hn, Or.inl ⟨a, he, hi, ?_, hc⟩⟩
    rcases hpn with hp | hp <;> simp [hp]
  · exact ⟨n, hn, Or.inr (by simpa [hpc] using hr)⟩

theorem flagFirst_favorable_reader_entry {E : Execution}
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

theorem turnFirst_next_read {E : Execution}
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
  rcases turnFirst_step_read (protocol_step h he) hi hpn with hc | hr
  · refine ⟨n, hn, Or.inl ⟨a, he, hi, ?_, hc⟩⟩
    rcases hpn with hp | hp <;> simp [hp]
  · exact ⟨n, hn, Or.inr (by simpa [hpc] using hr)⟩

theorem turnFirst_favorable_reader_entry {E : Execution}
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

theorem favorable_reader_entry {order : WaitOrder} {E : Execution}
    (h : Valid order E) (hf : ProtocolFair order E) {i : Proc} {m : ℕ}
    (hp : (E.state m).pc i = .beforeFirstRead ∨ (E.state m).pc i = .betweenReads)
    (hs : (∀ n, m ≤ n → (E.state n).flag i.other = false) ∨
      (∀ n, m ≤ n → (E.state n).turn = i.other)) :
    ∃ n, m ≤ n ∧ Entry E i n := by
  cases order with
  | flagFirst => exact flagFirst_favorable_reader_entry h hf hp hs
  | turnFirst => exact turnFirst_favorable_reader_entry h hf hp hs

/-- Each request starts at the ready counter, never from a pending passage. -/
theorem request_source {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {n : ℕ} (hr : Request E i n) : (E.state n).pc i = .beforeFlag := by
  have hs := protocol_step h hr
  generalize hdst : E.state (n + 1) = t at hs
  cases hs
  assumption

theorem pending_not_request {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {n : ℕ} (hp : Pending i (E.state n)) : ¬ Request E i n := by
  intro hr
  have hs := request_source h hr
  simp [Pending, hs] at hp

/-- Reusing the actor's request label first requires entry of the pending passage. -/
theorem entry_before_next_request {order : WaitOrder} {E : Execution}
    (h : Valid order E) {i : Proc} {r q : ℕ}
    (hr : Request E i r) (hq : Request E i q) (hrq : r < q) :
    ∃ n, r < n ∧ n < q ∧ Entry E i n := by
  by_contra hno
  apply pending_not_request h (n := q) ?_ hq
  apply pending_of_no_entry h (by omega) (request_pending h hr)
  intro n hn hnq he
  exact hno ⟨n, by omega, hnq, he⟩

/-- Each exit boundary has exactly one possible label; interference/padding preserves it. -/
theorem boundary_pc_succ {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {n : ℕ} {p : PC} {b : RepeatedAction}
    (hb : (p = .critical ∧ b = .protocol (.finishCritical i)) ∨
      (p = .beforeExitWrite ∧ b = .protocol (.writeFlagFalse i)) ∨
      (p = .afterPassage ∧ b = .restart i))
    (hp : (E.state n).pc i = p) (hne : E.event n ≠ some b) :
    (E.state (n + 1)).pc i = p := by
  cases he : E.event n with
  | none => simpa [(valid_iff.mp h).2.1 n he] using hp
  | some a =>
    have hs := (valid_iff.mp h).2.2 n a he
    generalize hdst : E.state (n + 1) = t at hs ⊢
    cases hs with
    | protocol hs =>
      rename_i action
      by_cases hi : i = actor action
      · cases hs <;> rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp_all [actor, State.setPC]
      · exact (Peterson.step_pc_of_ne_actor hs hi).trans hp
    | restart hs =>
      rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp_all [State.setPC, Function.update]
      all_goals intro heq; subst i; simp_all

/-- If a boundary counter is left by a later observation, its event occurred beforehand. -/
theorem boundary_before {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {m q : ℕ} {p : PC} {b : RepeatedAction}
    (hb : (p = .critical ∧ b = .protocol (.finishCritical i)) ∨
      (p = .beforeExitWrite ∧ b = .protocol (.writeFlagFalse i)) ∨
      (p = .afterPassage ∧ b = .restart i))
    (hmq : m ≤ q) (hp : (E.state m).pc i = p) (hq : (E.state q).pc i ≠ p) :
    ∃ n, m ≤ n ∧ n < q ∧ E.event n = some b := by
  by_contra hno
  apply hq
  have persists : ∀ n, m ≤ n → n ≤ q → (E.state n).pc i = p := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; exact hp
    | succ n hn ih =>
      intro hnq
      apply boundary_pc_succ h hb (ih (by omega))
      intro he
      exact hno ⟨n, hn, by omega, he⟩
  exact persists q hmq le_rfl

/-- A later request by the same actor requires entry, finish, exit, and private restart in order. -/
theorem request_cycle_order {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {r q : ℕ} (hr : Request E i r) (hq : Request E i q) (hrq : r < q) :
    ∃ e f x z, r < e ∧ e < f ∧ f < x ∧ x < z ∧ z < q ∧
      Entry E i e ∧ Finish E i f ∧
      E.event x = some (.protocol (.writeFlagFalse i)) ∧ E.event z = some (.restart i) := by
  obtain ⟨e, hre, heq, he⟩ := entry_before_next_request h hr hq hrq
  have hready := request_source h hq
  obtain ⟨f, hef, hfq, hf⟩ := boundary_before h (q := q) (Or.inl ⟨rfl, rfl⟩)
    (by omega) he.choose_spec.2.2.2 (by simp [hready])
  have hs := protocol_step h hf
  have hpc : (E.state (f + 1)).pc i = .beforeExitWrite := by
    generalize hdst : E.state (f + 1) = t at hs ⊢
    cases hs
    simp [State.setPC]
  obtain ⟨x, hfx, hxq, hx⟩ := boundary_before h (q := q) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (by omega) hpc (by simp [hready])
  have hs := protocol_step h hx
  have hpc : (E.state (x + 1)).pc i = .afterPassage := by
    generalize hdst : E.state (x + 1) = t at hs ⊢
    cases hs
    simp [State.setPC]
  obtain ⟨z, hxz, hzq, hz⟩ := boundary_before h (q := q) (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (by omega) hpc (by simp [hready])
  exact ⟨e, f, x, z, hre, by omega, by omega, by omega, hzq, he, hf, hx, hz⟩

end Peterson.Repeated
