import Peterson.Repeated.ProgressHelpers

/-! Per-request lockout freedom. No global one-passage stabilization is used. -/
namespace Peterson.Repeated

def Reader (i : Proc) (s : State) : Prop :=
  s.pc i = .beforeFirstRead ∨ s.pc i = .betweenReads

theorem writeTurn_facts {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i v : Proc} {n : ℕ} (he : E.event n = some (.protocol (.writeTurn i v))) :
    (E.state n).pc i = .betweenWrites ∧
    (E.state (n + 1)).pc i = .beforeFirstRead ∧ (E.state (n + 1)).turn = i := by
  have hs := protocol_step h he
  generalize hdst : E.state (n + 1) = t at hs ⊢
  cases hs
  simp_all [State.setPC, State.setTurn]

theorem first_turn_write {order : WaitOrder} {E : Execution}
    (h : Valid order E) (hf : ProtocolFair order E) {i : Proc} {m : ℕ}
    (hp : (E.state m).pc i = .betweenWrites) :
    ∃ n, m ≤ n ∧ E.event n = some (.protocol (.writeTurn i i)) := by
  obtain ⟨n, hn, ⟨_, a, he, hi⟩, hpc⟩ := first_protocol_step h hf (Or.inl (Or.inl hp))
  refine ⟨n, hn, ?_⟩
  have hs := protocol_step h he
  have hb := hpc.trans hp
  generalize hdst : E.state (n + 1) = t at hs
  cases hs <;> simp_all [actor]

theorem reader_succ {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {n : ℕ} (hr : Reader i (E.state n))
    (hp : Pending i (E.state (n + 1))) : Reader i (E.state (n + 1)) := by
  cases he : E.event n with
  | none => simpa [(valid_iff.mp h).2.1 n he] using hr
  | some a =>
    have hs := (valid_iff.mp h).2.2 n a he
    generalize hdst : E.state (n + 1) = t at hs hp ⊢
    cases hs with
    | protocol hs =>
      have hmono := Peterson.step_passageStage hs i
      rcases hp with hp | hp
      · rcases hr with hr | hr <;> simp [hp, hr, passageStage] at hmono
      · exact hp
    | restart hs =>
      have hi : (E.state n).pc i ≠ .afterPassage := by
        rcases hr with hr | hr <;> simp [hr]
      simpa only [Reader, restart_pc_eq hs hi] using hr

theorem reader_forever {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {m : ℕ} (hr : Reader i (E.state m))
    (hne : ∀ n, m ≤ n → ¬ Entry E i n) :
    ∀ n, m ≤ n → Reader i (E.state n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hr
  | succ n hn ih =>
    exact reader_succ h ih (pending_succ_of_not_entry h (Or.inr ih) (hne n hn))

/-- A changed turn has an actual turn-write label; restart and padding cannot change it. -/
theorem turn_succ {order : WaitOrder} {E : Execution} (h : Valid order E) (n : ℕ) :
    (E.state (n + 1)).turn = (E.state n).turn ∨
    ∃ j, E.event n = some (.protocol (.writeTurn j j)) ∧ (E.state (n + 1)).turn = j := by
  cases he : E.event n with
  | none => exact Or.inl (congrArg State.turn ((valid_iff.mp h).2.1 n he))
  | some a =>
    have hs := (valid_iff.mp h).2.2 n a he
    generalize hdst : E.state (n + 1) = t at hs ⊢
    cases hs with
    | restart _ => exact Or.inl rfl
    | protocol hs =>
      cases hs <;> simp_all [State.setPC, State.setFlag, State.setTurn]

theorem reader_no_turn_write {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {n : ℕ} (hr : Reader i (E.state n)) :
    E.event n ≠ some (.protocol (.writeTurn i i)) := by
  intro he
  have hb := (writeTurn_facts h he).1
  rcases hr with hr | hr <;> simp [hr] at hb

/-- The waiting actor cannot undo a favorable peer turn, even across recurring peer writes. -/
theorem favorable_turn_forever {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {m : ℕ} (hr : ∀ n, m ≤ n → Reader i (E.state n))
    (ht : (E.state m).turn = i.other) :
    ∀ n, m ≤ n → (E.state n).turn = i.other := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ht
  | succ n hn ih =>
    rcases turn_succ h n with he | ⟨j, he, ht⟩
    · exact he.trans ih
    · have hji : j ≠ i := by intro hj; exact reader_no_turn_write h (hr n hn) (by simpa only [hj] using he)
      have hj : j = i.other := by cases i <;> cases j <;> simp_all [Proc.other]
      exact ht.trans hj

theorem no_turn_write_constant {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {m : ℕ} (hr : ∀ n, m ≤ n → Reader i (E.state n))
    (hw : ∀ n, m ≤ n → E.event n ≠ some (.protocol (.writeTurn i.other i.other))) :
    ∀ n, m ≤ n → (E.state n).turn = (E.state m).turn := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rcases turn_succ h n with he | ⟨j, he, _⟩
    · exact he.trans ih
    · have hj : j = i ∨ j = i.other := by cases i <;> cases j <;> simp [Proc.other]
      rcases hj with hj | hj
      · exact (reader_no_turn_write h (hr n hn) (by simpa only [hj] using he)).elim
      · exact (hw n hn (by simpa only [hj] using he)).elim

/-- With no later peer turn write, fairness excludes its between-writes position everywhere. -/
theorem no_turn_write_no_between {order : WaitOrder} {E : Execution}
    (h : Valid order E) (hf : ProtocolFair order E) {j : Proc} {m : ℕ}
    (hw : ∀ n, m ≤ n → E.event n ≠ some (.protocol (.writeTurn j j))) :
    ∀ n, m ≤ n → (E.state n).pc j ≠ .betweenWrites := by
  intro n hn hp
  obtain ⟨k, hk, he⟩ := first_turn_write h hf hp
  exact hw k (by omega) he

/-- After requests cease, a false flag stays false; private restart is harmless. -/
theorem flag_false_succ {order : WaitOrder} {E : Execution} (h : Valid order E)
    {i : Proc} {n : ℕ} (hf : (E.state n).flag i = false)
    (hr : ¬ Request E i n) : (E.state (n + 1)).flag i = false := by
  cases he : E.event n with
  | none => simpa [(valid_iff.mp h).2.1 n he] using hf
  | some a =>
    have hs := (valid_iff.mp h).2.2 n a he
    generalize hdst : E.state (n + 1) = t at hs ⊢
    cases hs with
    | restart _ => exact hf
    | protocol hs =>
      cases hs <;> simp_all [State.setPC, State.setFlag, State.setTurn, Function.update, Request]
      exact Ne.symm hr

theorem exit_eventually_false {order : WaitOrder} {E : Execution}
    (h : Valid order E) (hf : ProtocolFair order E) {i : Proc} {m : ℕ}
    (hp : (E.state m).pc i = .beforeExitWrite) :
    ∃ n, m ≤ n ∧ (E.state n).flag i = false := by
  obtain ⟨n, hn, ⟨_, a, he, hi⟩, hpc⟩ := first_protocol_step h hf (Or.inr hp)
  refine ⟨n + 1, by omega, ?_⟩
  have hs := protocol_step h he
  have hb := hpc.trans hp
  generalize hdst : E.state (n + 1) = t at hs ⊢
  cases hs <;> simp_all [actor, State.setPC, State.setFlag]

theorem critical_eventually_false {order : WaitOrder} {E : Execution}
    (h : Valid order E) (hf : ProtocolFair order E) (hc : CriticalCompletes E)
    {i : Proc} {m : ℕ} (hp : (E.state m).pc i = .critical) :
    ∃ n, m ≤ n ∧ (E.state n).flag i = false := by
  obtain ⟨k, hk, he⟩ := hc i m hp
  have hs := protocol_step h he
  have hexit : (E.state (k + 1)).pc i = .beforeExitWrite := by
    generalize hdst : E.state (k + 1) = t at hs ⊢
    cases hs
    simp [State.setPC]
  obtain ⟨n, hn, hf⟩ := exit_eventually_false h hf hexit
  exact ⟨n, by omega, hf⟩

/-- The non-writing peer eventually stays outside, even if private restart remains possible. -/
theorem peer_eventually_false {order : WaitOrder} {E : Execution}
    (h : Valid order E) (hf : ProtocolFair order E) (hc : CriticalCompletes E)
    {j : Proc} {m : ℕ}
    (hw : ∀ n, m ≤ n → E.event n ≠ some (.protocol (.writeTurn j j)))
    (ht : ∀ n, m ≤ n → (E.state n).turn = j.other) :
    ∃ k, m ≤ k ∧ ∀ n, k ≤ n → (E.state n).flag j = false := by
  have hb := no_turn_write_no_between h hf hw
  have hreq : ∀ n, m ≤ n → ¬ Request E j n := by
    intro n hn he
    have hs := protocol_step h he
    have hp : (E.state (n + 1)).pc j = .betweenWrites := by
      generalize hdst : E.state (n + 1) = t at hs ⊢
      cases hs
      simp [State.setPC]
    exact hb (n + 1) (by omega) hp
  have hex : ∃ k, m ≤ k ∧ (E.state k).flag j = false := by
    have hread (hr : Reader j (E.state m)) : ∃ k, m ≤ k ∧ (E.state k).flag j = false := by
      obtain ⟨n, hn, _, _, _, _, hcritical⟩ := favorable_reader_entry h hf hr (Or.inr ht)
      obtain ⟨k, hk, hflag⟩ := critical_eventually_false h hf hc hcritical
      exact ⟨k, by omega, hflag⟩
    cases hp : (E.state m).pc j with
    | beforeFlag | afterPassage =>
      refine ⟨m, le_rfl, ?_⟩
      have hi := flag_iff_interested_reachable (valid_reachable h m) j
      cases hv : (E.state m).flag j <;> simp_all [Interested]
    | betweenWrites => exact (hb m le_rfl hp).elim
    | beforeFirstRead => exact hread (Or.inl hp)
    | betweenReads => exact hread (Or.inr hp)
    | critical => exact critical_eventually_false h hf hc hp
    | beforeExitWrite => exact exit_eventually_false h hf hp
  obtain ⟨k, hk, hflag⟩ := hex
  refine ⟨k, hk, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hflag
  | succ n hn ih => exact flag_false_succ h ih (hreq n (by omega))

/-- A fixed pending request cannot wait forever under the exact two premises. -/
theorem pending_eventually_entry {order : WaitOrder} {E : Execution}
    (h : Valid order E) (hf : ProtocolFair order E) (hc : CriticalCompletes E)
    {i : Proc} {m : ℕ} (hp : Pending i (E.state m)) :
    ∃ n, m ≤ n ∧ Entry E i n := by
  by_contra hno
  have hne : ∀ n, m ≤ n → ¬ Entry E i n := by
    intro n hn he
    exact hno ⟨n, hn, he⟩
  have hex : ∃ k, m ≤ k ∧ Reader i (E.state k) := by
    rcases hp with hb | hr
    · obtain ⟨n, hn, he⟩ := first_turn_write h hf hb
      exact ⟨n + 1, by omega, Or.inl (writeTurn_facts h he).2.1⟩
    · exact ⟨m, le_rfl, hr⟩
  obtain ⟨k, hk, hr⟩ := hex
  have hrs := reader_forever h hr (fun n hn => hne n (by omega))
  have force {N : ℕ} (hN : k ≤ N)
      (fav : (∀ n, N ≤ n → (E.state n).flag i.other = false) ∨
        (∀ n, N ≤ n → (E.state n).turn = i.other)) : False := by
    obtain ⟨n, hn, he⟩ := favorable_reader_entry h hf (hrs N hN) fav
    exact hne n (by omega) he
  by_cases hw : ∃ n, k ≤ n ∧ E.event n = some (.protocol (.writeTurn i.other i.other))
  · obtain ⟨n, hn, he⟩ := hw
    exact force (N := n + 1) (by omega) (Or.inr
      (favorable_turn_forever h (fun r hr => hrs r (by omega)) (writeTurn_facts h he).2.2))
  · have hnw : ∀ n, k ≤ n → E.event n ≠ some (.protocol (.writeTurn i.other i.other)) := by
      intro n hn he
      exact hw ⟨n, hn, he⟩
    have hconst := no_turn_write_constant h hrs hnw
    by_cases ht : (E.state k).turn = i.other
    · exact force le_rfl (Or.inr (fun n hn => (hconst n hn).trans ht))
    · have hturn : (E.state k).turn = i.other.other := by
        cases i <;> cases hv : (E.state k).turn <;> simp_all [Proc.other]
      obtain ⟨N, hN, hflag⟩ := peer_eventually_false h hf hc hnw
        (fun n hn => (hconst n hn).trans hturn)
      exact force hN (Or.inl hflag)

/-- First entry pairs with this still-pending request, even if earlier requests existed. -/
theorem repeated_request_entry : RepeatedRequestEntry := by
  intro order E h hf hc i r hr
  classical
  have hex := pending_eventually_entry h hf hc (request_pending h hr)
  let n := Nat.find hex
  have hn : r + 1 ≤ n ∧ Entry E i n := Nat.find_spec hex
  refine ⟨n, by omega, hn.2, ?_⟩
  intro k hk
  apply pending_of_no_entry h (by omega) (request_pending h hr)
  intro t ht htk he
  have hmin := Nat.find_min' hex (show r + 1 ≤ t ∧ Entry E i t from ⟨ht, he⟩)
  change n ≤ t at hmin
  omega

end Peterson.Repeated
