import Peterson.NProcessHistory

namespace Peterson.NProcess.Examples

private def s1 : State 1 := ((initial 1).announce 0 0).setPC 0 (.writeTurn 0)
private def s2 : State 1 := (s1.writeTurn 0 0).setPC 0 (.scan 0 0)
private def s3 : State 1 := s2.setPC 0 (.scan 0 1)
private def s4 : State 1 := (s3.announce 1 0).setPC 1 (.writeTurn 0)
def staleScan : State 1 := s4.setPC 0 (passed 0)

/-- Source actors [1,1,1,2,1]: the first low read becomes stale before passage. -/
theorem stale_scan_trace : (lts 1).MTr (initial 1) [0,0,0,1,0] staleScan := by
  exact .stepL (.announce rfl) (.stepL (.writeTurn rfl)
    (.stepL (.scanLowNext rfl (by decide) (by decide))
      (.stepL (.announce rfl) (.stepL (.scanLowLast rfl (by decide) (by decide)) .refl))))

theorem stale_scan_not_snapshot : staleScan.pc 0 = .writeQ 1 ∧
    (staleScan.q 1).val = 1 ∧ Past 1 (staleScan.pc 0) := by
  exact ⟨rfl, rfl, by change 1 < 2; omega⟩

private def s6 : State 1 := (staleScan.announce 0 1).setPC 0 (.writeTurn 1)
private def s7 : State 1 := (s6.writeTurn 0 1).setPC 0 (.scan 1 0)
private def s8 : State 1 := s7.setPC 0 (.scan 1 1)
private def s9 : State 1 := s8.setPC 0 (passed 1)
private def s10 : State 1 := s9.setPC 0 .exit
def finished : State 1 := (s10.clear 0).setPC 0 .done

set_option maxHeartbeats 800000 in
theorem passage_completion_trace : (lts 1).MTr staleScan [0,0,0,0,0,0] finished := by
  exact .stepL (.announce rfl) (.stepL (.writeTurn rfl)
    (.stepL (.scanLowNext rfl (by decide) (by decide))
      (.stepL (.scanLowLast rfl (by decide) (by decide))
        (.stepL (.finish rfl) (.stepL (.clear rfl) .refl)))))

theorem finished_cleared : finished.pc 0 = .done ∧ (finished.q 0).val = 0 := by decide

private def w1 : State 0 := ((initial 0).announce 0 0).setPC 0 (.writeTurn 0)
private def w2 : State 0 := (w1.writeTurn 0 0).setPC 0 (.scan 0 0)
private def w3 : State 0 := (w2.announce 1 0).setPC 1 (.writeTurn 0)
private def w4 : State 0 := w3.setPC 0 (.readTurn 0)
private def w5 : State 0 := w4.setPC 0 (.scan 0 0)
private def w6 : State 0 := (w5.writeTurn 1 0).setPC 1 (.scan 0 0)
private def w7 : State 0 := w6.setPC 0 (.readTurn 0)
def turnEntry : State 0 := w7.setPC 0 (passed 0)

/-- A high Q read, unsuccessful TURN read, reset, and later successful TURN read. -/
theorem retry_then_turn_entry : (lts 0).MTr (initial 0) [0,0,1,0,0,1,0,0] turnEntry := by
  exact .stepL (.announce rfl) (.stepL (.writeTurn rfl)
    (.stepL (.announce rfl) (.stepL (.scanHigh rfl (by decide))
      (.stepL (.turnSelf rfl rfl) (.stepL (.writeTurn rfl)
        (.stepL (.scanHigh rfl (by decide)) (.stepL (.turnOther rfl (by decide)) .refl)))))))

theorem turn_entry_critical : turnEntry.pc 0 = .critical := by decide

end Peterson.NProcess.Examples
