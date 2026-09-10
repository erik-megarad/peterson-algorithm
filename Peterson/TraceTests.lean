import Peterson.Specification

/-!
# Checked traces for Peterson's two-process specification

These finite `MTr` witnesses exercise the semantic cases F0--F5 from the
accepted target review.  They are examples checked by Lean's kernel, not a
proof that every reachable state is safe.  The executable exhaustive check is
kept separately as non-authoritative falsification evidence.
-/

namespace Peterson.TraceTests

open Peterson

/-- The concrete root with the selected source-permitted initial `turn`. -/
def root (turn : Proc) : State where
  flag := fun _ => false
  turn := turn
  pc := fun _ => .beforeFlag

theorem root_initial (turn : Proc) : Initial (root turn) := by
  simp [root, Initial]

/-- F0: either initial `turn` value is reachable through CSLib's empty trace. -/
theorem f0_initial_p1 (order : WaitOrder) : Reachable order (root .p1) := by
  exact ⟨root .p1, root_initial .p1, ⟨[], .refl⟩⟩

/-- F0: the second source-permitted initial `turn` is an independent root. -/
theorem f0_initial_p2 (order : WaitOrder) : Reachable order (root .p2) := by
  exact ⟨root .p2, root_initial .p2, ⟨[], .refl⟩⟩

/-- F1: the peer's flag write can occur between one process's two entry writes. -/
theorem f1_separate_entry_writes (order : WaitOrder) (turn actor : Proc) :
    let s0 := root turn
    let s1 := (s0.setFlag actor true).setPC actor .betweenWrites
    let s2 := (s1.setFlag actor.other true).setPC actor.other .betweenWrites
    (petersonLTS order).MTr (root turn)
      [.writeFlagTrue actor, .writeFlagTrue actor.other, .writeTurn actor actor]
      ((s2.setTurn actor).setPC actor .beforeFirstRead) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL
    (Step.writeFlagTrue (by cases actor <;> simp [root, State.setFlag, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL
    (Step.writeTurn (by cases actor <;> simp [State.setFlag, State.setPC, Proc.other]))
  exact Cslib.LTS.MTr.refl

/-- F2 (`flagFirst`): an unfavorable flag/turn pair causes a fresh attempt. -/
theorem f2_flagFirst_retry (turn actor : Proc) :
    let s0 := root turn
    let s1 := (s0.setFlag actor true).setPC actor .betweenWrites
    let s2 := (s1.setFlag actor.other true).setPC actor.other .betweenWrites
    let s3 := (s2.setTurn actor).setPC actor .beforeFirstRead
    (petersonLTS .flagFirst).MTr s0
      [.writeFlagTrue actor, .writeFlagTrue actor.other, .writeTurn actor actor,
       .readFlag actor actor.other true, .readTurn actor actor]
      ((s3.setPC actor .betweenReads).setPC actor .beforeFirstRead) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL
    (Step.writeFlagTrue (by cases actor <;> simp [root, State.setFlag, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL
    (Step.writeTurn (by cases actor <;> simp [State.setFlag, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadFlagTrue rfl (by simp [State.setPC])
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL
    (Step.flagFirstReadTurnSelf rfl (by simp [State.setPC])
      (by simp [State.setTurn, State.setPC]))
  exact Cslib.LTS.MTr.refl

/-- F2 (`turnFirst`): an unfavorable turn/flag pair causes a fresh attempt. -/
theorem f2_turnFirst_retry (turn actor : Proc) :
    let s0 := root turn
    let s1 := (s0.setFlag actor true).setPC actor .betweenWrites
    let s2 := (s1.setFlag actor.other true).setPC actor.other .betweenWrites
    let s3 := (s2.setTurn actor).setPC actor .beforeFirstRead
    (petersonLTS .turnFirst).MTr s0
      [.writeFlagTrue actor, .writeFlagTrue actor.other, .writeTurn actor actor,
       .readTurn actor actor, .readFlag actor actor.other true]
      ((s3.setPC actor .betweenReads).setPC actor .beforeFirstRead) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL
    (Step.writeFlagTrue (by cases actor <;> simp [root, State.setFlag, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL
    (Step.writeTurn (by cases actor <;> simp [State.setFlag, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL
    (Step.turnFirstReadTurnSelf rfl (by simp [State.setPC])
      (by simp [State.setTurn, State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadFlagTrue rfl (by simp [State.setPC])
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  exact Cslib.LTS.MTr.refl

/-- F3 (`flagFirst`): a false peer flag is a one-read short-circuit success. -/
theorem f3_flagFirst_flag_success (turn actor : Proc) :
    let s0 := root turn
    let s1 := (s0.setFlag actor true).setPC actor .betweenWrites
    let s2 := (s1.setTurn actor).setPC actor .beforeFirstRead
    (petersonLTS .flagFirst).MTr s0
      [.writeFlagTrue actor, .writeTurn actor actor, .readFlag actor actor.other false]
      (s2.setPC actor .critical) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn (by simp [State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadFlagFalse rfl (by simp [State.setPC])
    (by cases actor <;> simp [root, State.setFlag, State.setPC, State.setTurn, Proc.other]))
  exact Cslib.LTS.MTr.refl

/-- F3 (`turnFirst`): a false peer flag succeeds on the second read. -/
theorem f3_turnFirst_flag_success (turn actor : Proc) :
    let s0 := root turn
    let s1 := (s0.setFlag actor true).setPC actor .betweenWrites
    let s2 := (s1.setTurn actor).setPC actor .beforeFirstRead
    let s3 := s2.setPC actor .betweenReads
    (petersonLTS .turnFirst).MTr s0
      [.writeFlagTrue actor, .writeTurn actor actor, .readTurn actor actor,
       .readFlag actor actor.other false]
      (s3.setPC actor .critical) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn (by simp [State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadTurnSelf rfl (by simp [State.setPC])
    (by simp [State.setTurn, State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadFlagFalse rfl (by simp [State.setPC])
    (by cases actor <;> simp [root, State.setFlag, State.setPC, State.setTurn, Proc.other]))
  exact Cslib.LTS.MTr.refl

/-- F3 (`flagFirst`): the peer-valued `turn` succeeds on the second read. -/
theorem f3_flagFirst_turn_success (turn actor : Proc) :
    let s0 := root turn
    let s1 := (s0.setFlag actor true).setPC actor .betweenWrites
    let s2 := (s1.setTurn actor).setPC actor .beforeFirstRead
    let s3 := (s2.setFlag actor.other true).setPC actor.other .betweenWrites
    let s4 := (s3.setTurn actor.other).setPC actor.other .beforeFirstRead
    let s5 := s4.setPC actor .betweenReads
    (petersonLTS .flagFirst).MTr s0
      [.writeFlagTrue actor, .writeTurn actor actor, .writeFlagTrue actor.other,
       .writeTurn actor.other actor.other, .readFlag actor actor.other true,
       .readTurn actor actor.other]
      (s5.setPC actor .critical) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn (by simp [State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue
    (by cases actor <;> simp [root, State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn
    (by cases actor <;> simp [root, State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadFlagTrue rfl
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadTurnOther rfl (by simp [State.setPC])
    (by simp [State.setTurn, State.setPC]))
  exact Cslib.LTS.MTr.refl

/-- F3 (`turnFirst`): the peer-valued `turn` is a one-read short-circuit success. -/
theorem f3_turnFirst_turn_success (turn actor : Proc) :
    let s0 := root turn
    let s1 := (s0.setFlag actor true).setPC actor .betweenWrites
    let s2 := (s1.setTurn actor).setPC actor .beforeFirstRead
    let s3 := (s2.setFlag actor.other true).setPC actor.other .betweenWrites
    let s4 := (s3.setTurn actor.other).setPC actor.other .beforeFirstRead
    (petersonLTS .turnFirst).MTr s0
      [.writeFlagTrue actor, .writeTurn actor actor, .writeFlagTrue actor.other,
       .writeTurn actor.other actor.other, .readTurn actor actor.other]
      (s4.setPC actor .critical) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn (by simp [State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue
    (by cases actor <;> simp [root, State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn
    (by cases actor <;> simp [root, State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadTurnOther rfl
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by simp [State.setTurn, State.setPC]))
  exact Cslib.LTS.MTr.refl

/-- F4 (`flagFirst`): clearing a flag between reads does not revise the saved branch. -/
theorem f4_flagFirst_interference (turn actor : Proc) :
    let peer := actor.other
    let s0 := root turn
    let s1 := (s0.setFlag peer true).setPC peer .betweenWrites
    let s2 := (s1.setTurn peer).setPC peer .beforeFirstRead
    let s3 := s2.setPC peer .critical
    let s4 := s3.setPC peer .beforeExitWrite
    let s5 := (s4.setFlag actor true).setPC actor .betweenWrites
    let s6 := (s5.setTurn actor).setPC actor .beforeFirstRead
    let s7 := s6.setPC actor .betweenReads
    let s8 := (s7.setFlag peer false).setPC peer .afterPassage
    let s9 := s8.setPC actor .beforeFirstRead
    (petersonLTS .flagFirst).MTr s0
      [.writeFlagTrue peer, .writeTurn peer peer, .readFlag peer peer.other false,
       .finishCritical peer, .writeFlagTrue actor, .writeTurn actor actor,
       .readFlag actor peer true, .writeFlagFalse peer, .readTurn actor actor,
       .readFlag actor peer false]
      (s9.setPC actor .critical) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn (by simp [State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadFlagFalse rfl (by simp [State.setPC])
    (by cases actor <;> simp [root, State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.finishCritical (by simp [State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue
    (by cases actor <;> simp [root, State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn (by simp [State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadFlagTrue rfl (by simp [State.setPC])
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeFlagFalse
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadTurnSelf rfl
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by simp [State.setFlag, State.setTurn, State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadFlagFalse rfl (by simp [State.setPC])
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  exact Cslib.LTS.MTr.refl

/-- F4 (`turnFirst`): a peer turn write between reads does not revise the saved branch. -/
theorem f4_turnFirst_interference (turn actor : Proc) :
    let peer := actor.other
    let s0 := root turn
    let s1 := (s0.setFlag actor true).setPC actor .betweenWrites
    let s2 := (s1.setTurn actor).setPC actor .beforeFirstRead
    let s3 := (s2.setFlag peer true).setPC peer .betweenWrites
    let s4 := s3.setPC actor .betweenReads
    let s5 := (s4.setTurn peer).setPC peer .beforeFirstRead
    (petersonLTS .turnFirst).MTr s0
      [.writeFlagTrue actor, .writeTurn actor actor, .writeFlagTrue peer,
       .readTurn actor actor, .writeTurn peer peer, .readFlag actor peer true]
      (s5.setPC actor .beforeFirstRead) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn (by simp [State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue
    (by cases actor <;> simp [root, State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadTurnSelf rfl
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by cases actor <;> simp [State.setFlag, State.setTurn, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadFlagTrue rfl
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by cases actor <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  exact Cslib.LTS.MTr.refl

/--
F5 (`flagFirst`): under maximum contention, the process whose peer writes
`turn` last enters, the loser retries, and the loser enters only after the
winner finishes its critical section and clears its flag.  Quantifying over
`turn` and `winner` covers both roots and both asymmetric schedules.
-/
theorem f5_flagFirst_contention (turn winner : Proc) :
    let loser := winner.other
    let s0 := root turn
    let s1 := (s0.setFlag winner true).setPC winner .betweenWrites
    let s2 := (s1.setFlag loser true).setPC loser .betweenWrites
    let s3 := (s2.setTurn winner).setPC winner .beforeFirstRead
    let s4 := (s3.setTurn loser).setPC loser .beforeFirstRead
    let s5 := s4.setPC winner .betweenReads
    let s6 := s5.setPC winner .critical
    let s7 := s6.setPC loser .betweenReads
    let s8 := s7.setPC loser .beforeFirstRead
    let s9 := s8.setPC winner .beforeExitWrite
    let s10 := (s9.setFlag winner false).setPC winner .afterPassage
    (petersonLTS .flagFirst).MTr s0
      [.writeFlagTrue winner, .writeFlagTrue loser, .writeTurn winner winner,
       .writeTurn loser loser, .readFlag winner loser true, .readTurn winner loser,
       .readFlag loser loser.other true, .readTurn loser loser,
       .finishCritical winner, .writeFlagFalse winner,
       .readFlag loser loser.other false]
      (s10.setPC loser .critical) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue
    (by cases winner <;> simp [root, State.setFlag, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn
    (by cases winner <;> simp [State.setFlag, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadFlagTrue rfl
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadTurnOther rfl (by simp [State.setPC])
    (by simp [State.setTurn, State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadFlagTrue rfl
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadTurnSelf rfl (by simp [State.setPC])
    (by simp [State.setTurn, State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.finishCritical
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeFlagFalse
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.flagFirstReadFlagFalse rfl
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  exact Cslib.LTS.MTr.refl

/--
F5 (`turnFirst`): the analogous maximum-contention trace exposes the loser's
turn/flag retry and its later two-read entry after the winner's exit write.
-/
theorem f5_turnFirst_contention (turn winner : Proc) :
    let loser := winner.other
    let s0 := root turn
    let s1 := (s0.setFlag winner true).setPC winner .betweenWrites
    let s2 := (s1.setFlag loser true).setPC loser .betweenWrites
    let s3 := (s2.setTurn winner).setPC winner .beforeFirstRead
    let s4 := (s3.setTurn loser).setPC loser .beforeFirstRead
    let s5 := s4.setPC winner .critical
    let s6 := s5.setPC loser .betweenReads
    let s7 := s6.setPC loser .beforeFirstRead
    let s8 := s7.setPC winner .beforeExitWrite
    let s9 := (s8.setFlag winner false).setPC winner .afterPassage
    let s10 := s9.setPC loser .betweenReads
    (petersonLTS .turnFirst).MTr s0
      [.writeFlagTrue winner, .writeFlagTrue loser, .writeTurn winner winner,
       .writeTurn loser loser, .readTurn winner loser, .readTurn loser loser,
       .readFlag loser loser.other true, .finishCritical winner,
       .writeFlagFalse winner, .readTurn loser loser,
       .readFlag loser loser.other false]
      (s10.setPC loser .critical) := by
  dsimp
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue (by simp [root]))
  apply Cslib.LTS.MTr.stepL (Step.writeFlagTrue
    (by cases winner <;> simp [root, State.setFlag, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn
    (by cases winner <;> simp [State.setFlag, State.setPC, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeTurn
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadTurnOther rfl
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by simp [State.setTurn, State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadTurnSelf rfl
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by simp [State.setTurn, State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadFlagTrue rfl (by simp [State.setPC])
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.finishCritical
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.writeFlagFalse
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadTurnSelf rfl
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other])
    (by simp [State.setFlag, State.setTurn, State.setPC]))
  apply Cslib.LTS.MTr.stepL (Step.turnFirstReadFlagFalse rfl (by simp [State.setPC])
    (by cases winner <;> simp [State.setFlag, State.setPC, State.setTurn, Proc.other]))
  exact Cslib.LTS.MTr.refl

end Peterson.TraceTests
