import Peterson.Progress

/-!
# Positive and negative execution witnesses

Terminal-padding helpers prove the infinite temporal premises. The first
witness is the reviewed A0 execution, in which neither optional actor starts.
A1 completes a lone passage; A2 includes contention and both completed passages.
N1 keeps one actor reading forever while neglecting its enabled peer.
-/

namespace Peterson

/-- Eventual absence from the protocol defeats continuous enablement on every suffix. -/
theorem protocolFair_of_eventually_not_protocol {order : WaitOrder} {E : ProgressExecution}
    (h : ∀ i m, ∃ n, m ≤ n ∧ ¬ Protocol i (E.state n)) : ProtocolFair order E := by
  intro i m hen
  obtain ⟨n, hmn, hn⟩ := h i m
  exact (hn (hen n hmn).1).elim

/-- Leaving critical occupancy requires that actor's explicit completion event. -/
theorem critical_succ_of_not_finish {order : WaitOrder} {E : ProgressExecution}
    (h : Valid order E) {i : Proc} {n : ℕ}
    (hc : (E.state n).pc i = .critical) (hf : ¬ Finish E i n) :
    (E.state (n + 1)).pc i = .critical := by
  cases he : E.event n with
  | none => rw [(valid_iff.mp h).2.1 n he]; exact hc
  | some a =>
    have hs := (valid_iff.mp h).2.2 n a he
    by_cases hi : i = actor a
    · generalize hdst : E.state (n + 1) = t at hs ⊢
      cases hs <;> simp_all [Finish, actor]
    · rw [step_pc_of_ne_actor hs hi]
      exact hc

/-- If critical occupancy eventually ends, validity supplies the required finish label. -/
theorem criticalCompletes_of_eventually_not_critical {order : WaitOrder}
    {E : ProgressExecution} (h : Valid order E)
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

/-- A terminal nonparticipating/completed state makes padded finite traces admissible. -/
theorem terminal_padding_admissible {order : WaitOrder} {E : ProgressExecution}
    {t : State} {N : ℕ} (h : Valid order E)
    (ht : ∀ n, E.state (N + n) = t)
    (hp : ∀ i, ¬ Protocol i t) (hc : ∀ i, t.pc i ≠ .critical) :
    ProtocolFair order E ∧ CriticalCompletes E := by
  constructor
  · apply protocolFair_of_eventually_not_protocol
    intro i m
    exact ⟨N + m, Nat.le_add_left m N, by rw [ht m]; exact hp i⟩
  · apply criticalCompletes_of_eventually_not_critical h
    intro i m
    exact ⟨N + m, Nat.le_add_left m N, by rw [ht m]; exact hc i⟩

/-- Reviewed A0: neither process requests, for either permitted initial turn. -/
def noRequests (turn : Proc) : ProgressExecution where
  state _ := ⟨fun _ => false, turn, fun _ => .beforeFlag⟩
  event _ := none

/-- A0 is valid and satisfies both actual temporal premises for either guard order. -/
theorem noRequests_admissible (order : WaitOrder) (turn : Proc) :
    Valid order (noRequests turn) ∧ ProtocolFair order (noRequests turn) ∧
      CriticalCompletes (noRequests turn) := by
  have hv : Valid order (noRequests turn) := by
    refine ⟨⟨fun _ => rfl, fun _ => rfl⟩, ?_⟩
    intro n
    rfl
  refine ⟨hv, terminal_padding_admissible (N := 0) hv (fun _ => rfl) ?_ ?_⟩
  · intro i
    simp [Protocol, Pending]
  · intro i
    simp

/-- A0 never triggers a pending obligation and has no spurious padding entry. -/
theorem noRequests_no_pending_or_entry (turn : Proc) (i : Proc) (n : ℕ) :
    ¬ Pending i ((noRequests turn).state n) ∧ ¬ Entry (noRequests turn) i n := by
  simp [noRequests, Pending, Entry]

/-- A1 state observations; the turn-first order retains its extra first read. -/
def loneState (order : WaitOrder) (turn i : Proc) (n : ℕ) : State :=
  let s0 : State := ⟨fun _ => false, turn, fun _ => .beforeFlag⟩
  let s1 := (s0.setFlag i true).setPC i .betweenWrites
  let s2 := (s1.setTurn i).setPC i .beforeFirstRead
  let s3 := s2.setPC i .betweenReads
  let entered := (if order = .flagFirst then s2 else s3).setPC i .critical
  let finished := entered.setPC i .beforeExitWrite
  let terminal := (finished.setFlag i false).setPC i .afterPassage
  match n with
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => if order = .flagFirst then entered else s3
  | 4 => if order = .flagFirst then finished else entered
  | 5 => if order = .flagFirst then terminal else finished
  | _ => terminal

/-- A1's original atomic labels followed by whole-state padding. -/
def lonePassage (order : WaitOrder) (turn i : Proc) : ProgressExecution where
  state := loneState order turn i
  event n := match n with
    | 0 => some (.writeFlagTrue i)
    | 1 => some (.writeTurn i i)
    | 2 => some (if order = .flagFirst then .readFlag i i.other false else .readTurn i i)
    | 3 => some (if order = .flagFirst then .finishCritical i else .readFlag i i.other false)
    | 4 => some (if order = .flagFirst then .writeFlagFalse i else .finishCritical i)
    | 5 => if order = .flagFirst then none else some (.writeFlagFalse i)
    | _ => none

/-- Every A1 tick is an original step or terminal padding, for either initial turn. -/
theorem lonePassage_valid (order : WaitOrder) (turn i : Proc) :
    Valid order (lonePassage order turn i) := by
  constructor
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | n
    all_goals cases order <;> dsimp [lonePassage, loneState, observationLTS]
    all_goals first
      | exact Step.writeFlagTrue rfl
      | exact Step.writeTurn (by simp [State.setPC])
      | exact Step.flagFirstReadFlagFalse rfl (by simp [State.setPC])
          (by cases i <;> rfl)
      | exact Step.turnFirstReadTurnSelf rfl (by simp [State.setPC]) rfl
      | exact Step.turnFirstReadFlagFalse rfl (by simp [State.setPC])
          (by cases i <;> rfl)
      | exact Step.finishCritical (by simp [State.setPC])
      | exact Step.writeFlagFalse (by simp [State.setPC])
      | rfl

/-- The completed actor and its never-started peer satisfy the actual infinite premises. -/
theorem lonePassage_admissible (order : WaitOrder) (turn i : Proc) :
    Valid order (lonePassage order turn i) ∧
      ProtocolFair order (lonePassage order turn i) ∧
      CriticalCompletes (lonePassage order turn i) := by
  have hv := lonePassage_valid order turn i
  refine ⟨hv, terminal_padding_admissible (N := 6) hv (t := loneState order turn i 6) ?_ ?_ ?_⟩
  · intro n
    cases order <;> simp [lonePassage, loneState, Nat.add_comm 6 n]
  · intro j
    cases order <;> cases i <;> cases j <;>
      simp [Protocol, Pending, loneState, State.setPC, State.setFlag, State.setTurn]
  · intro j
    cases order <;> cases i <;> cases j <;> simp [loneState, State.setPC, State.setFlag, State.setTurn]

/-- A1 really requests, is pending afterward, and enters at the order-specific read tick. -/
theorem lonePassage_pending_entry (order : WaitOrder) (turn i : Proc) :
    Request (lonePassage order turn i) i 0 ∧
      Pending i ((lonePassage order turn i).state 1) ∧
      Entry (lonePassage order turn i) i (if order = .flagFirst then 2 else 3) := by
  exact ⟨rfl, Or.inl (by simp [lonePassage, loneState, State.setPC, State.setFlag]), by
    cases order <;> refine ⟨.readFlag i i.other false, rfl, rfl, ?_, ?_⟩ <;>
      simp [lonePassage, loneState, State.setPC, State.setFlag, State.setTurn]⟩

/-- Every pending observation in A1 has a later new entry by that same actor. -/
theorem lonePassage_pending_progress (order : WaitOrder) (turn i j : Proc) (m : ℕ)
    (hp : Pending j ((lonePassage order turn i).state m)) :
    ∃ n, m ≤ n ∧ Entry (lonePassage order turn i) j n := by
  have he := (lonePassage_pending_entry order turn i).2.2
  rcases m with _ | _ | _ | _ | _ | _ | m
  all_goals cases order <;> cases i <;> cases j <;>
    simp_all [Pending, lonePassage, loneState, State.setPC, State.setFlag, State.setTurn]
  all_goals first | exact ⟨2, by decide, he⟩ | exact ⟨3, by decide, he⟩

/-- Padding begins after five/six actions, with both flags clear and the peer unstarted. -/
theorem lonePassage_terminal (order : WaitOrder) (turn i : Proc) (n : ℕ) :
    let k := (if order = .flagFirst then 5 else 6) + n
    (lonePassage order turn i).event k = none ∧
      ((lonePassage order turn i).state k).pc i = .afterPassage ∧
      ((lonePassage order turn i).state k).pc i.other = .beforeFlag ∧
      (∀ j, ((lonePassage order turn i).state k).flag j = false) := by
  cases order <;> cases n <;> cases i <;>
    simp [lonePassage, loneState, State.setPC, State.setFlag, State.setTurn,
      Proc.other, Nat.add_comm, Function.update]

/-- A2 observations: both request, the loser retries, then both complete. -/
def contentionState (order : WaitOrder) (turn i : Proc) (n : ℕ) : State :=
  let j := i.other
  let s0 : State := ⟨fun _ => false, turn, fun _ => .beforeFlag⟩
  let s1 := (s0.setFlag i true).setPC i .betweenWrites
  let s2 := (s1.setFlag j true).setPC j .betweenWrites
  let s3 := (s2.setTurn i).setPC i .beforeFirstRead
  let s4 := (s3.setTurn j).setPC j .beforeFirstRead
  let s5 := s4.setPC j .betweenReads
  let s6 := s5.setPC j .beforeFirstRead
  let aRead := s6.setPC i .betweenReads
  let aEntry := (if order = .flagFirst then aRead else s6).setPC i .critical
  let aFinish := aEntry.setPC i .beforeExitWrite
  let aExit := (aFinish.setFlag i false).setPC i .afterPassage
  let bRead := aExit.setPC j .betweenReads
  let bEntry := (if order = .flagFirst then aExit else bRead).setPC j .critical
  let bFinish := bEntry.setPC j .beforeExitWrite
  let terminal := (bFinish.setFlag j false).setPC j .afterPassage
  match n with
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s4
  | 5 => s5
  | 6 => s6
  | 7 => if order = .flagFirst then aRead else aEntry
  | 8 => if order = .flagFirst then aEntry else aFinish
  | 9 => if order = .flagFirst then aFinish else aExit
  | 10 => if order = .flagFirst then aExit else bRead
  | 11 => bEntry
  | 12 => bFinish
  | _ => terminal

/-- A2 retains all thirteen individual actions and pads only after both exits. -/
def contention (order : WaitOrder) (turn i : Proc) : ProgressExecution where
  state := contentionState order turn i
  event n := match n with
    | 0 => some (.writeFlagTrue i)
    | 1 => some (.writeFlagTrue i.other)
    | 2 => some (.writeTurn i i)
    | 3 => some (.writeTurn i.other i.other)
    | 4 => some (if order = .flagFirst then .readFlag i.other i true
        else .readTurn i.other i.other)
    | 5 => some (if order = .flagFirst then .readTurn i.other i.other
        else .readFlag i.other i true)
    | 6 => some (if order = .flagFirst then .readFlag i i.other true
        else .readTurn i i.other)
    | 7 => some (if order = .flagFirst then .readTurn i i.other else .finishCritical i)
    | 8 => some (if order = .flagFirst then .finishCritical i else .writeFlagFalse i)
    | 9 => some (if order = .flagFirst then .writeFlagFalse i
        else .readTurn i.other i.other)
    | 10 => some (.readFlag i.other i false)
    | 11 => some (.finishCritical i.other)
    | 12 => some (.writeFlagFalse i.other)
    | _ => none

/-- A2's failed reads, successful reads and exits are original atomic steps. -/
theorem contention_valid (order : WaitOrder) (turn i : Proc) :
    Valid order (contention order turn i) := by
  constructor
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    all_goals cases order <;> cases i <;> dsimp [contention, contentionState, observationLTS]
    all_goals first
      | exact Step.writeFlagTrue rfl
      | exact Step.writeTurn rfl
      | exact Step.flagFirstReadFlagTrue rfl rfl rfl
      | exact Step.flagFirstReadFlagFalse rfl rfl rfl
      | exact Step.flagFirstReadTurnSelf rfl rfl rfl
      | exact Step.flagFirstReadTurnOther rfl rfl rfl
      | exact Step.turnFirstReadTurnSelf rfl rfl rfl
      | exact Step.turnFirstReadTurnOther rfl rfl rfl
      | exact Step.turnFirstReadFlagTrue rfl rfl rfl
      | exact Step.turnFirstReadFlagFalse rfl rfl rfl
      | exact Step.finishCritical rfl
      | exact Step.writeFlagFalse rfl
      | rfl

/-- Terminal padding proves actual infinite admissibility, including exit scheduling. -/
theorem contention_admissible (order : WaitOrder) (turn i : Proc) :
    Valid order (contention order turn i) ∧ ProtocolFair order (contention order turn i) ∧
      CriticalCompletes (contention order turn i) := by
  have hv := contention_valid order turn i
  refine ⟨hv, terminal_padding_admissible (N := 13) hv
    (t := contentionState order turn i 13) ?_ ?_ ?_⟩
  · intro n
    cases order <;> simp [contention, contentionState, Nat.add_comm 13 n]
  · intro j
    cases order <;> cases i <;> cases j <;>
      simp [Protocol, Pending, contentionState, State.setPC, State.setFlag, State.setTurn,
        Proc.other]
  · intro j
    cases order <;> cases i <;> cases j <;>
      simp [contentionState, State.setPC, State.setFlag, State.setTurn, Proc.other]

/-- Both requests really occur; both are pending before the loser's unsuccessful evaluation. -/
theorem contention_requests_pending (order : WaitOrder) (turn i : Proc) :
    Request (contention order turn i) i 0 ∧ Request (contention order turn i) i.other 1 ∧
      Pending i ((contention order turn i).state 4) ∧
      Pending i.other ((contention order turn i).state 4) := by
  cases order <;> cases i <;>
    simp [Request, Pending, contention, contentionState, State.setPC, State.setFlag,
      State.setTurn, Proc.other]

/-- A's entry index depends on read order; B's new entry is tick 10 in both. -/
theorem contention_entries (order : WaitOrder) (turn i : Proc) :
    Entry (contention order turn i) i (if order = .flagFirst then 7 else 6) ∧
      Entry (contention order turn i) i.other 10 := by
  cases order <;> cases i <;> constructor
  all_goals unfold Entry
  all_goals refine ⟨_, rfl, rfl, ?_, ?_⟩
  all_goals simp [contention, contentionState, State.setPC, State.setFlag, State.setTurn,
    Proc.other]

/-- Every A2 pending observation has a future new entry by that actor, even after A entered. -/
theorem contention_pending_progress (order : WaitOrder) (turn i j : Proc) (m : ℕ)
    (hp : Pending j ((contention order turn i).state m)) :
    ∃ n, m ≤ n ∧ Entry (contention order turn i) j n := by
  obtain ⟨ha, hb⟩ := contention_entries order turn i
  rcases m with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  all_goals cases order <;> cases i <;> cases j <;>
    simp [Pending, contention, contentionState, State.setPC, State.setFlag,
      State.setTurn, Proc.other] at hp
  all_goals first
    | exact ⟨7, by decide, ha⟩
    | exact ⟨6, by decide, ha⟩
    | exact ⟨10, by decide, hb⟩

/-- After thirteen actions both counters are finished and flags clear forever. -/
theorem contention_terminal (order : WaitOrder) (turn i : Proc) (n : ℕ) :
    (contention order turn i).event (13 + n) = none ∧
      (∀ j, ((contention order turn i).state (13 + n)).pc j = .afterPassage) ∧
      (∀ j, ((contention order turn i).state (13 + n)).flag j = false) := by
  cases order <;> cases i <;>
    simp [contention, contentionState, State.setPC, State.setFlag, State.setTurn,
      Proc.other, Nat.add_comm 13 n]
  all_goals constructor <;> intro j <;> cases j <;> rfl

/-- N1: the four initial writes, then only the losing actor's two-read retry forever. -/
def protocolNeglect (order : WaitOrder) (turn i : Proc) : ProgressExecution where
  state n := contentionState order turn i (if n < 4 then n else 4 + n % 2)
  event n := (contention order turn i).event (if n < 4 then n else 4 + n % 2)

/-- N1 repeats exactly the reviewed unsuccessful read pair, with unchanged shared fields. -/
theorem protocolNeglect_valid (order : WaitOrder) (turn i : Proc) :
    Valid order (protocolNeglect order turn i) := by
  constructor
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · intro n
    rcases n with _ | _ | _ | _ | n
    all_goals cases order <;> cases i
    all_goals try { dsimp [protocolNeglect, contention, contentionState, observationLTS]
                    first | exact Step.writeFlagTrue rfl | exact Step.writeTurn rfl }
    all_goals have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    all_goals rcases hm with hm | hm
    all_goals simp [protocolNeglect, contention, contentionState, observationLTS,
      Nat.add_mod, hm, show ¬ n + 1 + 1 + 1 + 1 < 4 by omega,
      show ¬ n + 1 + 1 + 1 + 1 + 1 < 4 by omega]
    all_goals solve
      | exact Step.flagFirstReadFlagTrue rfl rfl rfl
      | exact Step.flagFirstReadTurnSelf rfl rfl rfl
      | exact Step.turnFirstReadTurnSelf rfl rfl rfl
      | exact Step.turnFirstReadFlagTrue rfl rfl rfl
      | (convert Step.flagFirstReadTurnSelf (s := contentionState .flagFirst turn .p1 5)
            (i := .p2) rfl rfl rfl using 1 <;> simp [contentionState, State.setPC, State.setFlag, State.setTurn, Proc.other])
      | (convert Step.flagFirstReadTurnSelf (s := contentionState .flagFirst turn .p2 5)
            (i := .p1) rfl rfl rfl using 1 <;> simp [contentionState, State.setPC, State.setFlag, State.setTurn, Proc.other])
      | (convert Step.turnFirstReadFlagTrue (s := contentionState .turnFirst turn .p1 5)
            (i := .p2) rfl rfl rfl using 1 <;> simp [contentionState, State.setPC, State.setFlag, State.setTurn, Proc.other])
      | (convert Step.turnFirstReadFlagTrue (s := contentionState .turnFirst turn .p2 5)
            (i := .p1) rfl rfl rfl using 1 <;> simp [contentionState, State.setPC, State.setFlag, State.setTurn, Proc.other])

/-- Neither N1 actor ever occupies a critical section. -/
theorem protocolNeglect_not_critical (order : WaitOrder) (turn i j : Proc) (n : ℕ) :
    ((protocolNeglect order turn i).state n).pc j ≠ .critical := by
  have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
  by_cases hn : n < 4
  · have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hn' with rfl | rfl | rfl | rfl
    all_goals cases order <;> cases i <;> cases j <;> simp [protocolNeglect, contentionState, State.setPC, State.setFlag, State.setTurn, Proc.other]
  · rcases hm with hm | hm
    all_goals cases order <;> cases i <;> cases j <;>
      simp [protocolNeglect, hn, hm, contentionState, State.setPC, State.setFlag, State.setTurn,
        Proc.other]

/-- N1 satisfies critical completion vacuously and has no entry at any tick. -/
theorem protocolNeglect_completion_no_entry (order : WaitOrder) (turn i : Proc) :
    CriticalCompletes (protocolNeglect order turn i) ∧
      ∀ j n, ¬ Entry (protocolNeglect order turn i) j n := by
  constructor
  · intro j n hc
    exact (protocolNeglect_not_critical order turn i j n hc).elim
  · intro j n he
    exact protocolNeglect_not_critical order turn i j (n + 1) he.choose_spec.2.2.2

/-- The neglected winner remains pending and enabled on the entire suffix from state 4. -/
theorem protocolNeglect_enabled (order : WaitOrder) (turn i : Proc) {n : ℕ} (hn : 4 ≤ n) :
    Pending i ((protocolNeglect order turn i).state n) ∧
      Enabled order i ((protocolNeglect order turn i).state n) := by
  have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hn' : ¬ n < 4 := by omega
  rcases hm with hm | hm
  all_goals cases order <;> cases i <;>
    dsimp [protocolNeglect]
  all_goals simp only [ite_eq_right hn', hm]
  all_goals refine ⟨Or.inr (Or.inl rfl), Or.inl (Or.inr (Or.inl rfl)), ?_⟩
  all_goals solve
    | exact ⟨_, _, rfl, Step.flagFirstReadFlagTrue rfl rfl rfl⟩
    | exact ⟨_, _, rfl, Step.turnFirstReadTurnOther rfl rfl rfl⟩

/-- No suffix tick is taken by the neglected actor, so actual protocol fairness fails. -/
theorem protocolNeglect_not_fair (order : WaitOrder) (turn i : Proc) :
    ¬ ProtocolFair order (protocolNeglect order turn i) := by
  intro hf
  obtain ⟨n, hn, _, a, he, ha⟩ := hf i 4 (fun _ hn => (protocolNeglect_enabled order turn i hn).2)
  have hn' : ¬ n < 4 := by omega
  have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm
  all_goals cases order <;> cases i <;>
    simp [protocolNeglect, hn', hm, contention] at he
  all_goals subst a; contradiction

/-- The other actor really takes a protocol step at every suffix tick. -/
theorem protocolNeglect_peer_taken (order : WaitOrder) (turn i : Proc) {n : ℕ}
    (hn : 4 ≤ n) : Taken (protocolNeglect order turn i) i.other n := by
  have hn' : ¬ n < 4 := by omega
  have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with hm | hm
  all_goals cases order <;> cases i <;>
    simp [Taken, Protocol, Pending, protocolNeglect, hn', hm, contention,
      contentionState, State.setPC, State.setFlag, State.setTurn, actor, Proc.other]

/-- N1 refutes future entry without protocol fairness, even with ongoing peer steps. -/
theorem protocolNeglect_counterexample (order : WaitOrder) (turn i : Proc) :
    Valid order (protocolNeglect order turn i) ∧
      CriticalCompletes (protocolNeglect order turn i) ∧
      ¬ ProtocolFair order (protocolNeglect order turn i) ∧
      Pending i ((protocolNeglect order turn i).state 4) ∧
      (¬ ∃ j n, 4 ≤ n ∧ Entry (protocolNeglect order turn i) j n) ∧
      (∀ m, ∃ n, m ≤ n ∧ Taken (protocolNeglect order turn i) i.other n) := by
  refine ⟨protocolNeglect_valid order turn i,
    (protocolNeglect_completion_no_entry order turn i).1,
    protocolNeglect_not_fair order turn i,
    (protocolNeglect_enabled order turn i (Nat.le_refl 4)).1, ?_, ?_⟩
  · rintro ⟨j, n, _, he⟩
    exact (protocolNeglect_completion_no_entry order turn i).2 j n he
  · intro m
    exact ⟨4 + m, Nat.le_add_left m 4, protocolNeglect_peer_taken order turn i (by omega)⟩

/-- N2 keeps an old occupant in critical while its peer retries forever. -/
def criticalNeglectState (order : WaitOrder) (turn i : Proc) (n : ℕ) : State :=
  let k := if order = .flagFirst then 3 else 4
  let entered := loneState order turn i k
  let requested := (entered.setFlag i.other true).setPC i.other .betweenWrites
  let ready := (requested.setTurn i.other).setPC i.other .beforeFirstRead
  if n < k then loneState order turn i n
  else if n = k then entered
  else if n = k + 1 then requested
  else if (n - (k + 2)) % 2 = 0 then ready else ready.setPC i.other .betweenReads

/-- The finite lone-entry prefix precedes the peer's writes and unsuccessful read pairs. -/
def criticalNeglect (order : WaitOrder) (turn i : Proc) : ProgressExecution where
  state := criticalNeglectState order turn i
  event n :=
    let k := if order = .flagFirst then 3 else 4
    if n < k then (lonePassage order turn i).event n
    else if n = k then some (.writeFlagTrue i.other)
    else if n = k + 1 then some (.writeTurn i.other i.other)
    else some (if ((n - (k + 2)) % 2 = 0) = (order = .flagFirst)
      then .readFlag i.other i true else .readTurn i.other i.other)

/-- Every N2 observation edge is an original step. -/
theorem criticalNeglect_valid (order : WaitOrder) (turn i : Proc) :
    Valid order (criticalNeglect order turn i) := by
  constructor
  · cases order <;> exact ⟨fun _ => rfl, fun _ => rfl⟩
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | n
    all_goals cases order <;> cases i
    all_goals try { simp [criticalNeglect, criticalNeglectState, loneState, lonePassage, observationLTS]
                    first
                    | exact Step.writeFlagTrue rfl
                    | exact Step.writeTurn rfl
                    | exact Step.flagFirstReadFlagFalse rfl rfl rfl
                    | exact Step.turnFirstReadTurnSelf rfl rfl rfl
                    | exact Step.turnFirstReadFlagFalse rfl rfl rfl
                    | exact Step.flagFirstReadFlagTrue rfl rfl rfl }
    all_goals have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    all_goals rcases hm with hm | hm
    all_goals simp [criticalNeglect, criticalNeglectState, loneState, lonePassage,
      observationLTS, Nat.add_mod, hm,
      show ¬ n + 1 + 1 + 1 + 1 + 1 + 1 < 4 by omega,
      show ¬ n + 1 + 1 + 1 + 1 + 1 + 1 < 3 by omega,
      show ¬ n + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 4 by omega,
      show ¬ n + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 3 by omega]
    all_goals try { first
      | exact Step.flagFirstReadFlagTrue rfl rfl rfl
      | exact Step.turnFirstReadTurnSelf rfl rfl rfl }
    all_goals solve
      | (convert Step.flagFirstReadTurnSelf (s := criticalNeglectState .flagFirst turn .p1 6)
          (i := .p2) rfl rfl rfl using 1 <;>
          simp [criticalNeglectState, loneState, State.setPC, State.setFlag, State.setTurn, Proc.other])
      | (convert Step.flagFirstReadTurnSelf (s := criticalNeglectState .flagFirst turn .p2 6)
          (i := .p1) rfl rfl rfl using 1 <;>
          simp [criticalNeglectState, loneState, State.setPC, State.setFlag, State.setTurn, Proc.other])
      | (convert Step.turnFirstReadFlagTrue (s := criticalNeglectState .turnFirst turn .p1 7)
          (i := .p2) rfl rfl rfl using 1 <;>
          simp [criticalNeglectState, loneState, State.setPC, State.setFlag, State.setTurn, Proc.other])
      | (convert Step.turnFirstReadFlagTrue (s := criticalNeglectState .turnFirst turn .p2 7)
          (i := .p1) rfl rfl rfl using 1 <;>
          simp [criticalNeglectState, loneState, State.setPC, State.setFlag, State.setTurn, Proc.other])

/-- On N2's repeating suffix the old occupant stays critical and the peer takes steps. -/
theorem criticalNeglect_tail (order : WaitOrder) (turn i : Proc) (d : ℕ) :
    let n := (if order = .flagFirst then 5 else 6) + d
    ((criticalNeglect order turn i).state n).pc i = .critical ∧
      Pending i.other ((criticalNeglect order turn i).state n) ∧
      Taken (criticalNeglect order turn i) i.other n ∧
      (∀ j, ¬ Finish (criticalNeglect order turn i) j n) ∧
      (∀ j, ¬ Entry (criticalNeglect order turn i) j n) := by
  have hm : d % 2 = 0 ∨ d % 2 = 1 := by omega
  rcases hm with hm | hm
  all_goals cases order <;> cases i <;>
    simp (disch := omega) [criticalNeglect, criticalNeglectState, loneState, Taken, Protocol, Pending,
      Finish, Entry, actor, State.setPC, State.setFlag, State.setTurn, Proc.other,
      Nat.add_comm, Nat.add_left_comm, Nat.add_mod, hm,
      show ¬ d + 5 < 3 by omega, show ¬ d + 6 < 3 by omega,
      show ¬ d + 6 < 4 by omega, show ¬ d + 7 < 4 by omega]
  all_goals simp [Function.update]

/-- N2 satisfies the actual fairness premise: its only suffix protocol actor keeps reading. -/
theorem criticalNeglect_fair (order : WaitOrder) (turn i : Proc) :
    ProtocolFair order (criticalNeglect order turn i) := by
  intro j m hen
  let k := if order = .flagFirst then 5 else 6
  have hle : m ≤ k + m := Nat.le_add_left m k
  have ht := criticalNeglect_tail order turn i m
  by_cases hj : j = i
  · subst j
    have hp := (hen (k + m) hle).1
    dsimp [k, Protocol, Pending] at hp
    rw [ht.1] at hp
    simp at hp
  · have hj' : j = i.other := by cases i <;> cases j <;> simp_all [Proc.other]
    subst j
    exact ⟨k + m, hle, ht.2.2.1⟩

/-- The old entry is earlier than the pending suffix; its occupant never finishes. -/
theorem criticalNeglect_old_entry (order : WaitOrder) (turn i : Proc) :
    Entry (criticalNeglect order turn i) i (if order = .flagFirst then 2 else 3) := by
  cases order <;> cases i <;> refine ⟨_, rfl, rfl, ?_, ?_⟩ <;>
    simp [criticalNeglect, criticalNeglectState, loneState, State.setPC,
      State.setFlag, State.setTurn, Proc.other]

/-- N2 isolates critical completion: validity and fairness hold but future entry fails. -/
theorem criticalNeglect_counterexample (order : WaitOrder) (turn i : Proc) :
    let m := if order = .flagFirst then 5 else 6
    Valid order (criticalNeglect order turn i) ∧
      ProtocolFair order (criticalNeglect order turn i) ∧
      ¬ CriticalCompletes (criticalNeglect order turn i) ∧
      Pending i.other ((criticalNeglect order turn i).state m) ∧
      (¬ ∃ j n, m ≤ n ∧ Entry (criticalNeglect order turn i) j n) := by
  dsimp only
  let m := if order = .flagFirst then 5 else 6
  have ht := criticalNeglect_tail order turn i 0
  simp only [Nat.add_zero] at ht
  refine ⟨criticalNeglect_valid order turn i, criticalNeglect_fair order turn i, ?_, ht.2.1, ?_⟩
  · intro hc
    obtain ⟨n, hn, hf⟩ := hc i m ht.1
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (criticalNeglect_tail order turn i d).2.2.2.1 i hf
  · rintro ⟨j, n, hn, he⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (criticalNeglect_tail order turn i d).2.2.2.2 j he

/-- N3 finishes opaque critical work, then neglects the still-enabled exit write. -/
def exitNeglectState (order : WaitOrder) (turn i : Proc) (n : ℕ) : State :=
  let k := if order = .flagFirst then 3 else 4
  let entered := loneState order turn i k
  let requested := (entered.setFlag i.other true).setPC i.other .betweenWrites
  let ready := (requested.setTurn i.other).setPC i.other .beforeFirstRead
  let finished := ready.setPC i .beforeExitWrite
  if n < k then loneState order turn i n
  else if n = k then entered
  else if n = k + 1 then requested
  else if n = k + 2 then ready
  else if (n - (k + 3)) % 2 = 0 then finished
  else finished.setPC i.other .betweenReads

/-- N2's prefix, one completion action, then the same unsuccessful read pair forever. -/
def exitNeglect (order : WaitOrder) (turn i : Proc) : ProgressExecution where
  state := exitNeglectState order turn i
  event n :=
    let k := if order = .flagFirst then 3 else 4
    if n < k then (lonePassage order turn i).event n
    else if n = k then some (.writeFlagTrue i.other)
    else if n = k + 1 then some (.writeTurn i.other i.other)
    else if n = k + 2 then some (.finishCritical i)
    else some (if ((n - (k + 3)) % 2 = 0) = (order = .flagFirst)
      then .readFlag i.other i true else .readTurn i.other i.other)

/-- Example-only comparison: weak fairness restricted to pending entry protocol positions.
It deliberately omits exit scheduling and never replaces `ProtocolFair`. -/
def EntryProtocolFair (order : WaitOrder) (E : ProgressExecution) : Prop :=
  ∀ i m, (∀ k, m ≤ k → Pending i (E.state k) ∧
    ∃ a t, actor a = i ∧ Step order (E.state k) a t) →
    ∃ n, m ≤ n ∧ Pending i (E.state n) ∧
      ∃ a, E.event n = some a ∧ actor a = i

/-- Every N3 edge, including opaque completion and each separate retry read, is original. -/
theorem exitNeglect_valid (order : WaitOrder) (turn i : Proc) :
    Valid order (exitNeglect order turn i) := by
  constructor
  · cases order <;> exact ⟨fun _ => rfl, fun _ => rfl⟩
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | _ | n
    all_goals cases order <;> cases i
    all_goals try { simp [exitNeglect, exitNeglectState, loneState, lonePassage, observationLTS]
                    first
                    | exact Step.writeFlagTrue rfl
                    | exact Step.writeTurn rfl
                    | exact Step.flagFirstReadFlagFalse rfl rfl rfl
                    | exact Step.turnFirstReadTurnSelf rfl rfl rfl
                    | exact Step.turnFirstReadFlagFalse rfl rfl rfl
                    | exact Step.flagFirstReadFlagTrue rfl rfl rfl
                    | exact Step.finishCritical rfl }
    all_goals have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    all_goals rcases hm with hm | hm
    all_goals simp (disch := omega) [exitNeglect, exitNeglectState, loneState, lonePassage,
      observationLTS, Nat.add_mod, hm,
      show ¬ n + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 3 by omega,
      show ¬ n + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 4 by omega,
      show ¬ n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 3 by omega,
      show ¬ n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 4 by omega]
    all_goals try { first
      | exact Step.flagFirstReadFlagTrue rfl rfl rfl
      | exact Step.turnFirstReadTurnSelf rfl rfl rfl }
    all_goals solve
      | (convert Step.flagFirstReadTurnSelf (s := exitNeglectState .flagFirst turn .p1 7)
          (i := .p2) rfl rfl rfl using 1 <;>
          simp [exitNeglectState, loneState, State.setPC, State.setFlag, State.setTurn, Proc.other])
      | (convert Step.flagFirstReadTurnSelf (s := exitNeglectState .flagFirst turn .p2 7)
          (i := .p1) rfl rfl rfl using 1 <;>
          simp [exitNeglectState, loneState, State.setPC, State.setFlag, State.setTurn, Proc.other])
      | (convert Step.turnFirstReadFlagTrue (s := exitNeglectState .turnFirst turn .p1 8)
          (i := .p2) rfl rfl rfl using 1 <;>
          simp [exitNeglectState, loneState, State.setPC, State.setFlag, State.setTurn, Proc.other])
      | (convert Step.turnFirstReadFlagTrue (s := exitNeglectState .turnFirst turn .p2 8)
          (i := .p1) rfl rfl rfl using 1 <;>
          simp [exitNeglectState, loneState, State.setPC, State.setFlag, State.setTurn, Proc.other])

/-- The completed actor remains before exit while its pending peer keeps reading. -/
theorem exitNeglect_tail (order : WaitOrder) (turn i : Proc) (d : ℕ) :
    let n := (if order = .flagFirst then 6 else 7) + d
    ((exitNeglect order turn i).state n).pc i = .beforeExitWrite ∧
      Pending i.other ((exitNeglect order turn i).state n) ∧
      Taken (exitNeglect order turn i) i.other n ∧
      (∀ j, ¬ Entry (exitNeglect order turn i) j n) ∧
      (¬ ∃ a, (exitNeglect order turn i).event n = some a ∧ actor a = i) := by
  have hm : d % 2 = 0 ∨ d % 2 = 1 := by omega
  rcases hm with hm | hm
  all_goals cases order <;> cases i <;>
    simp (disch := omega) [exitNeglect, exitNeglectState, loneState, Taken, Protocol, Pending,
      Entry, actor, State.setPC, State.setFlag, State.setTurn, Proc.other,
      Nat.add_comm, Nat.add_left_comm, Nat.add_mod, hm,
      show ¬ d + 6 < 3 by omega, show ¬ d + 7 < 3 by omega,
      show ¬ d + 7 < 4 by omega, show ¬ d + 8 < 4 by omega]
  all_goals simp [Function.update]

/-- Fairness with exit positions omitted holds for N3, including every earlier suffix. -/
theorem exitNeglect_entryFair (order : WaitOrder) (turn i : Proc) :
    EntryProtocolFair order (exitNeglect order turn i) := by
  intro j m hen
  let k := if order = .flagFirst then 6 else 7
  have hle : m ≤ k + m := Nat.le_add_left m k
  have ht := exitNeglect_tail order turn i m
  by_cases hj : j = i
  · subst j
    have hp := (hen (k + m) hle).1
    dsimp [k, Pending] at hp
    rw [ht.1] at hp
    simp at hp
  · have hj' : j = i.other := by cases i <;> cases j <;> simp_all [Proc.other]
    subst j
    exact ⟨k + m, hle, ht.2.1, ht.2.2.1.2⟩

/-- Critical occupancy ends for both actors; validity supplies actual completion labels. -/
theorem exitNeglect_completes (order : WaitOrder) (turn i : Proc) :
    CriticalCompletes (exitNeglect order turn i) := by
  apply criticalCompletes_of_eventually_not_critical (exitNeglect_valid order turn i)
  intro j m
  let k := if order = .flagFirst then 6 else 7
  refine ⟨k + m, Nat.le_add_left m k, ?_⟩
  have ht := exitNeglect_tail order turn i m
  by_cases hj : j = i
  · subst j
    rw [ht.1]
    decide
  · have hj' : j = i.other := by cases i <;> cases j <;> simp_all [Proc.other]
    subst j
    rcases ht.2.1 with hp | hp | hp <;> rw [hp] <;> decide

/-- The full premise rejects N3 because the exit write is continuously enabled. -/
theorem exitNeglect_not_fair (order : WaitOrder) (turn i : Proc) :
    ¬ ProtocolFair order (exitNeglect order turn i) := by
  intro hf
  let k := if order = .flagFirst then 6 else 7
  have hen : ∀ n, k ≤ n → Enabled order i ((exitNeglect order turn i).state n) := by
    intro n hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    have ht := exitNeglect_tail order turn i d
    exact ⟨Or.inr ht.1, _, _, rfl, Step.writeFlagFalse ht.1⟩
  obtain ⟨n, hn, _, ha⟩ := hf i k hen
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact (exitNeglect_tail order turn i d).2.2.2.2 ha

/-- The old entry and subsequent opaque completion precede the blocked suffix. -/
theorem exitNeglect_entry_finish (order : WaitOrder) (turn i : Proc) :
    Entry (exitNeglect order turn i) i (if order = .flagFirst then 2 else 3) ∧
      Finish (exitNeglect order turn i) i (if order = .flagFirst then 5 else 6) := by
  constructor
  · cases order <;> cases i <;> refine ⟨_, rfl, rfl, ?_, ?_⟩ <;>
      simp [exitNeglect, exitNeglectState, loneState, State.setPC,
        State.setFlag, State.setTurn, Proc.other]
  · cases order <;> rfl

/-- N3 isolates the need to schedule exit after opaque critical completion. -/
theorem exitNeglect_counterexample (order : WaitOrder) (turn i : Proc) :
    let m := if order = .flagFirst then 6 else 7
    Valid order (exitNeglect order turn i) ∧
      CriticalCompletes (exitNeglect order turn i) ∧
      EntryProtocolFair order (exitNeglect order turn i) ∧
      ¬ ProtocolFair order (exitNeglect order turn i) ∧
      Pending i.other ((exitNeglect order turn i).state m) ∧
      (¬ ∃ j n, m ≤ n ∧ Entry (exitNeglect order turn i) j n) ∧
      (∀ d, Taken (exitNeglect order turn i) i.other (m + d)) := by
  dsimp only
  have ht := exitNeglect_tail order turn i 0
  simp only [Nat.add_zero] at ht
  refine ⟨exitNeglect_valid order turn i, exitNeglect_completes order turn i,
    exitNeglect_entryFair order turn i, exitNeglect_not_fair order turn i, ht.2.1, ?_, ?_⟩
  · rintro ⟨j, n, hn, he⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact (exitNeglect_tail order turn i d).2.2.2.1 j he
  · intro d
    exact (exitNeglect_tail order turn i d).2.2.1

end Peterson
