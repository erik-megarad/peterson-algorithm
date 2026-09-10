import Peterson.Repeated.Overtaking
import Peterson.Repeated.ProgressExamples
import Mathlib.Tactic.IntervalCases

/-! Explicit 11-event witnesses followed by idle padding. Both initial TURN
values and actor roles remain parameters. No execution search is trusted. -/
namespace Peterson.Repeated
namespace OvertakingExamples

open Peterson.TraceTests

def witnessState (order : WaitOrder) (initialTurn i : Proc) (n : ℕ) : State :=
  match order, n with
  | .flagFirst, 0 => root initialTurn
  | .flagFirst, 1 => ((root initialTurn).setFlag i true).setPC i .betweenWrites
  | .flagFirst, 2 => ((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites
  | .flagFirst, 3 => ((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead
  | .flagFirst, 4 => ((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead
  | .flagFirst, 5 => (((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .betweenReads
  | .flagFirst, 6 => ((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .betweenReads).setPC i.other .critical
  | .flagFirst, 7 => (((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .betweenReads).setPC i.other .critical).setPC i.other .beforeExitWrite
  | .flagFirst, 8 => (((((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .betweenReads).setPC i.other .critical).setPC i.other .beforeExitWrite).setFlag i.other false).setPC i.other .afterPassage
  | .flagFirst, 9 => ((((((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .betweenReads).setPC i.other .critical).setPC i.other .beforeExitWrite).setFlag i.other false).setPC i.other .afterPassage).setPC i .critical
  | .flagFirst, 10 => (((((((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .betweenReads).setPC i.other .critical).setPC i.other .beforeExitWrite).setFlag i.other false).setPC i.other .afterPassage).setPC i .critical).setPC i .beforeExitWrite
  | .flagFirst, _ => (((((((((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .betweenReads).setPC i.other .critical).setPC i.other .beforeExitWrite).setFlag i.other false).setPC i.other .afterPassage).setPC i .critical).setPC i .beforeExitWrite).setFlag i false).setPC i .afterPassage
  | .turnFirst, 0 => root initialTurn
  | .turnFirst, 1 => ((root initialTurn).setFlag i true).setPC i .betweenWrites
  | .turnFirst, 2 => ((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites
  | .turnFirst, 3 => ((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead
  | .turnFirst, 4 => ((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead
  | .turnFirst, 5 => (((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .critical
  | .turnFirst, 6 => ((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .critical).setPC i.other .beforeExitWrite
  | .turnFirst, 7 => ((((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .critical).setPC i.other .beforeExitWrite).setFlag i.other false).setPC i.other .afterPassage
  | .turnFirst, 8 => (((((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .critical).setPC i.other .beforeExitWrite).setFlag i.other false).setPC i.other .afterPassage).setPC i .betweenReads
  | .turnFirst, 9 => ((((((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .critical).setPC i.other .beforeExitWrite).setFlag i.other false).setPC i.other .afterPassage).setPC i .betweenReads).setPC i .critical
  | .turnFirst, 10 => (((((((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .critical).setPC i.other .beforeExitWrite).setFlag i.other false).setPC i.other .afterPassage).setPC i .betweenReads).setPC i .critical).setPC i .beforeExitWrite
  | .turnFirst, _ => (((((((((((((((((root initialTurn).setFlag i true).setPC i .betweenWrites).setFlag i.other true).setPC i.other .betweenWrites).setTurn i.other).setPC i.other .beforeFirstRead).setTurn i).setPC i .beforeFirstRead).setPC i.other .critical).setPC i.other .beforeExitWrite).setFlag i.other false).setPC i.other .afterPassage).setPC i .betweenReads).setPC i .critical).setPC i .beforeExitWrite).setFlag i false).setPC i .afterPassage

def witnessEvent (order : WaitOrder) (i : Proc) (n : ℕ) : Option RepeatedAction :=
  match order, n with
  | .flagFirst, 0 => some (.protocol (.writeFlagTrue i))
  | .flagFirst, 1 => some (.protocol (.writeFlagTrue i.other))
  | .flagFirst, 2 => some (.protocol (.writeTurn i.other i.other))
  | .flagFirst, 3 => some (.protocol (.writeTurn i i))
  | .flagFirst, 4 => some (.protocol (.readFlag i.other i true))
  | .flagFirst, 5 => some (.protocol (.readTurn i.other i))
  | .flagFirst, 6 => some (.protocol (.finishCritical i.other))
  | .flagFirst, 7 => some (.protocol (.writeFlagFalse i.other))
  | .flagFirst, 8 => some (.protocol (.readFlag i i.other false))
  | .flagFirst, 9 => some (.protocol (.finishCritical i))
  | .flagFirst, 10 => some (.protocol (.writeFlagFalse i))
  | .turnFirst, 0 => some (.protocol (.writeFlagTrue i))
  | .turnFirst, 1 => some (.protocol (.writeFlagTrue i.other))
  | .turnFirst, 2 => some (.protocol (.writeTurn i.other i.other))
  | .turnFirst, 3 => some (.protocol (.writeTurn i i))
  | .turnFirst, 4 => some (.protocol (.readTurn i.other i))
  | .turnFirst, 5 => some (.protocol (.finishCritical i.other))
  | .turnFirst, 6 => some (.protocol (.writeFlagFalse i.other))
  | .turnFirst, 7 => some (.protocol (.readTurn i i))
  | .turnFirst, 8 => some (.protocol (.readFlag i i.other false))
  | .turnFirst, 9 => some (.protocol (.finishCritical i))
  | .turnFirst, 10 => some (.protocol (.writeFlagFalse i))
  | _, _ => none

def witness (order : WaitOrder) (initialTurn i : Proc) : Execution :=
  ⟨witnessState order initialTurn i, witnessEvent order i⟩

theorem witness_valid (order : WaitOrder) (initialTurn i : Proc) :
    Valid order (witness order initialTurn i) := by
  constructor
  · cases order <;> exact root_initial initialTurn
  · intro n
    by_cases hn : n < 11
    · cases order <;> interval_cases n
      all_goals change Step _ _ _ _
      · exact .protocol (Peterson.Step.writeFlagTrue (by simp [witness, witnessState, root]))
      · exact .protocol (Peterson.Step.writeFlagTrue (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.writeTurn (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.writeTurn (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · cases i <;> exact .protocol (Peterson.Step.flagFirstReadFlagTrue rfl (by simp [witness, witnessState, State.setPC, Function.update, root]) (by simp [witness, witnessState, root, State.setFlag, Function.update, Proc.other]))
      · cases i <;> exact .protocol (Peterson.Step.flagFirstReadTurnOther rfl (by simp [witness, witnessState, State.setPC, Function.update, root]) (by simp [witness, witnessState, root, State.setFlag, Proc.other]))
      · exact .protocol (Peterson.Step.finishCritical (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.writeFlagFalse (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.flagFirstReadFlagFalse rfl (by simp [witness, witnessState, State.setPC, Function.update, root]) (by simp [witness, witnessState, root, State.setFlag, Function.update, Proc.other]))
      · exact .protocol (Peterson.Step.finishCritical (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.writeFlagFalse (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.writeFlagTrue (by simp [witness, witnessState, root]))
      · exact .protocol (Peterson.Step.writeFlagTrue (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.writeTurn (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.writeTurn (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · cases i <;> exact .protocol (Peterson.Step.turnFirstReadTurnOther rfl (by simp [witness, witnessState, State.setPC, Function.update, root]) (by simp [witness, witnessState, root, State.setFlag, Proc.other]))
      · exact .protocol (Peterson.Step.finishCritical (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.writeFlagFalse (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.turnFirstReadTurnSelf rfl (by simp [witness, witnessState, State.setPC, Function.update, root]) (by simp [witness, witnessState, root, State.setFlag, Proc.other]))
      · exact .protocol (Peterson.Step.turnFirstReadFlagFalse rfl (by simp [witness, witnessState, State.setPC, Function.update, root]) (by simp [witness, witnessState, root, State.setFlag, Function.update, Proc.other]))
      · exact .protocol (Peterson.Step.finishCritical (by simp [witness, witnessState, State.setPC, Function.update, root]))
      · exact .protocol (Peterson.Step.writeFlagFalse (by simp [witness, witnessState, State.setPC, Function.update, root]))
    · have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      have hn2 : n ≠ 2 := by omega
      have hn3 : n ≠ 3 := by omega
      have hn4 : n ≠ 4 := by omega
      have hn5 : n ≠ 5 := by omega
      have hn6 : n ≠ 6 := by omega
      have hn7 : n ≠ 7 := by omega
      have hn8 : n ≠ 8 := by omega
      have hn9 : n ≠ 9 := by omega
      have hn10 : n ≠ 10 := by omega
      cases order <;>
        simp [witness, witnessEvent, witnessState, observationLTS, hn0, hn1, hn2,
          hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10,

          show n + 1 ≠ 2 from by omega, show n + 1 ≠ 3 from by omega,
          show n + 1 ≠ 4 from by omega, show n + 1 ≠ 5 from by omega,
          show n + 1 ≠ 6 from by omega, show n + 1 ≠ 7 from by omega,
          show n + 1 ≠ 8 from by omega, show n + 1 ≠ 9 from by omega,
          show n + 1 ≠ 10 from by omega]

theorem witness_tail (order : WaitOrder) (initialTurn i : Proc) (n : ℕ) :
    (witness order initialTurn i).state (11 + n) = (witness order initialTurn i).state 11 := by
  cases order <;> simp [witness, witnessState, Nat.add_comm]

theorem witness_admissible (order : WaitOrder) (initialTurn i : Proc) :
    ProtocolFair order (witness order initialTurn i) ∧
      CriticalCompletes (witness order initialTurn i) := by
  apply terminal_padding_admissible (witness_valid order initialTurn i) (witness_tail order initialTurn i)
  · intro j
    cases order <;> cases i <;> cases j <;>
      simp [witness, witnessState, Protocol, Pending, State.setPC, Function.update, Proc.other]
  · intro j
    cases order <;> cases i <;> cases j <;>
      simp [witness, witnessState, State.setPC, Function.update, Proc.other]

theorem witness_request (order : WaitOrder) (initialTurn i : Proc) :
    Request (witness order initialTurn i) i 0 := by cases order <;> rfl

theorem witness_turn (order : WaitOrder) (initialTurn i : Proc) :
    TurnWrite (witness order initialTurn i) i 3 := by cases order <;> rfl

theorem witness_service (order : WaitOrder) (initialTurn i : Proc) :
    Serves (witness order initialTurn i) i 0 8 := by
  refine ⟨by omega, ?_, ?_⟩
  · refine ⟨.readFlag i i.other false, ?_, rfl, ?_, ?_⟩
    all_goals cases order <;> cases i <;>
      simp [witness, witnessEvent, witnessState, State.setPC, Function.update, Proc.other]
  · intro k hk
    obtain ⟨hlo, hhi⟩ := hk
    interval_cases k <;> cases order <;> cases i <;>
      simp [Pending, witness, witnessState, State.setPC, Function.update, Proc.other]

def peerEntryTick : WaitOrder → ℕ
  | .flagFirst => 5
  | .turnFirst => 4

theorem witness_peer_entry (order : WaitOrder) (initialTurn i : Proc) :
    Entry (witness order initialTurn i) i.other (peerEntryTick order) := by
  refine ⟨.readTurn i.other i, ?_, rfl, ?_, ?_⟩
  all_goals cases order <;> cases i <;>
    simp [peerEntryTick, witness, witnessEvent, witnessState, State.setPC, Function.update, Proc.other]

end OvertakingExamples

/-- Every order, actor and initial TURN has an admissible witness attaining both bounds. -/
theorem repeated_overtaking_sharp : RepeatedOvertakingSharp := by
  intro order i initialTurn
  let E := OvertakingExamples.witness order initialTurn i
  have hv := OvertakingExamples.witness_valid order initialTurn i
  have hadm := OvertakingExamples.witness_admissible order initialTurn i
  have hr := OvertakingExamples.witness_request order initialTurn i
  have ht := OvertakingExamples.witness_turn order initialTurn i
  have hs := OvertakingExamples.witness_service order initialTurn i
  have hp : PendingThrough E i 0 8 := ⟨hs.1, hs.2.2⟩
  have positive (a : ℕ) (ha : a ≤ 3) : 0 < PeerEntries E i a 8 := by
    apply Finset.card_pos.mpr
    refine ⟨OvertakingExamples.peerEntryTick order, mem_peerEntryIndices.mpr ⟨?_, ?_,
      OvertakingExamples.witness_peer_entry order initialTurn i⟩⟩
    · cases order <;> decide
    · cases order <;> simp only [OvertakingExamples.peerEntryTick] <;> omega
  refine ⟨E, hv, ?_, hadm.1, hadm.2, 0, 3, 8, hr, ht, hs, by omega, by omega, ?_, ?_⟩
  · cases order <;> rfl
  · have hbound := repeated_overtaking_bound order E hv i 0 8 hr hp
    have hpos := positive 0 (by omega)
    omega
  · have hbound := repeated_after_turn_bound order E hv i 0 3 8 hr hp (by omega) (by omega) ht
    have hpos := positive 3 le_rfl
    omega

end Peterson.Repeated
