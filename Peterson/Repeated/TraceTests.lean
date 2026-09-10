import Peterson.Repeated.Safety
import Peterson.TraceTests

/-! Kernel-checked repeated passages, optional peer participation, and forbidden restarts. -/
namespace Peterson.Repeated.TraceTests

open Peterson.TraceTests

def cycleActions (order : WaitOrder) (i : Proc) : List RepeatedAction :=
  [.protocol (.writeFlagTrue i), .protocol (.writeTurn i i)] ++
  (match order with
   | .flagFirst => [.protocol (.readFlag i i.other false)]
   | .turnFirst => [.protocol (.readTurn i i), .protocol (.readFlag i i.other false)]) ++
  [.protocol (.finishCritical i), .protocol (.writeFlagFalse i), .restart i]

/-- A whole passage and private restart; the peer never requests. -/
theorem solo_cycle (order : WaitOrder) (turn i : Proc) :
    (repeatedLTS order).MTr (root turn) (cycleActions order i) (root i) := by
  cases order <;> simp only [cycleActions, List.cons_append, List.nil_append]
  all_goals
    apply Cslib.LTS.MTr.stepL (Step.protocol (Peterson.Step.writeFlagTrue (by simp [root])))
    apply Cslib.LTS.MTr.stepL (Step.protocol (Peterson.Step.writeTurn (by simp)))
  · apply Cslib.LTS.MTr.stepL
      (Step.protocol (Peterson.Step.flagFirstReadFlagFalse rfl (by simp) (by simp [root])))
    apply Cslib.LTS.MTr.stepL (Step.protocol (Peterson.Step.finishCritical (by simp)))
    apply Cslib.LTS.MTr.stepL (Step.protocol (Peterson.Step.writeFlagFalse (by simp)))
    apply Cslib.LTS.MTr.stepL (Step.restart (by simp))
    convert (Cslib.LTS.MTr.refl (lts := repeatedLTS _) (s := root i)) using 1
    · cases i <;> simp [root, State.setPC, State.setFlag, State.setTurn]
  · apply Cslib.LTS.MTr.stepL
      (Step.protocol (Peterson.Step.turnFirstReadTurnSelf rfl (by simp) (by simp)))
    apply Cslib.LTS.MTr.stepL
      (Step.protocol (Peterson.Step.turnFirstReadFlagFalse rfl (by simp) (by simp [root])))
    apply Cslib.LTS.MTr.stepL (Step.protocol (Peterson.Step.finishCritical (by simp)))
    apply Cslib.LTS.MTr.stepL (Step.protocol (Peterson.Step.writeFlagFalse (by simp)))
    apply Cslib.LTS.MTr.stepL (Step.restart (by simp))
    convert (Cslib.LTS.MTr.refl (lts := repeatedLTS _) (s := root i)) using 1
    · cases i <;> simp [root, State.setPC, State.setFlag, State.setTurn]

/-- Any finite schedule of whole passages, including repeated occurrences of one actor. -/
theorem cycles (order : WaitOrder) (turn : Proc) (actors : List Proc) :
    ∃ finalTurn, (repeatedLTS order).MTr (root turn)
      (actors.flatMap (cycleActions order)) (root finalTurn) := by
  induction actors generalizing turn with
  | nil => exact ⟨turn, .refl⟩
  | cons i rest ih =>
    obtain ⟨finalTurn, ht⟩ := ih i
    exact ⟨finalTurn, (Cslib.LTS.MTr.append_iff (repeatedLTS order)).mpr ⟨root i, solo_cycle order turn i, ht⟩⟩

/-- Concrete two-request trace for the same actor, for either order/initial turn. -/
theorem two_passages (order : WaitOrder) (turn i : Proc) :
    (repeatedLTS order).MTr (root turn)
      (cycleActions order i ++ cycleActions order i) (root i) := by
  exact (Cslib.LTS.MTr.append_iff (repeatedLTS order)).mpr ⟨root i, solo_cycle order turn i, solo_cycle order i i⟩

/-- Restart is not an old-model edge or stutter: it changes the actor's counter. -/
theorem restart_changes_pc {s : State} {i : Proc} (h : s.pc i = .afterPassage) :
    s.setPC i .beforeFlag ≠ s := by
  intro heq
  have := congrArg (fun t : State => t.pc i) heq
  simp [h] at this

/-- A client cannot restart from a critical, pending, or pre-exit position. -/
theorem restart_requires_exit {order : WaitOrder} {s t : State} {i : Proc}
    (h : Step order s (.restart i) t) : s.pc i = .afterPassage := by
  cases h with
  | restart hpc => exact hpc

end Peterson.Repeated.TraceTests
