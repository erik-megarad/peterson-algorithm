import Peterson.NProcessHistory

namespace Peterson.NProcess
variable {m : Nat} {s t u : State m} {i p q : Proc m} {j : Level m}
  {c : Cursor m} {xs : List (Proc m)}

/-- The cursor has not yet read a designated peer in this scan, or the
process is testing TURN after a failed scan. This is a derived predicate. -/
def BeforePeer (p : Proc m) (j : Level m) (c : Cursor m) (s : State m) : Prop :=
  (∃ d, s.pc p = .scan j d ∧ d.val ≤ c.val) ∨ s.pc p = .readTurn j

theorem beforePeer_initial_scan (h : s.pc p = .scan j 0) : BeforePeer p j c s :=
  Or.inl ⟨0, h, Nat.zero_le _⟩

theorem beforePeer_rank (h : BeforePeer p j c s) : rank (s.pc p) = 3 * j.val + 2 := by
  obtain ⟨d, hd, _⟩ | hd := h <;> simp [hd, rank]

/-- A persistently high designated peer prevents scan completion. The only
escape is an actual favorable TURN read, in a separate transition. -/
theorem beforePeer_step (h : Step s i t) (hb : BeforePeer p j c s)
    (hq : j.val + 1 ≤ (s.q (peer p c)).val) :
    BeforePeer p j c t ∨ (i = p ∧ s.pc p = .readTurn j ∧ s.turn j ≠ p) := by
  by_cases hi : p = i
  · subst i
    obtain ⟨d, hd, hdc⟩ | hd := hb
    · cases h <;> simp_all [State.setPC]
      · exact Or.inr (by simp)
      · have hcursor := congrArg Fin.val hd.2
        left
        refine ⟨⟨d.val + 1, by omega⟩, by simp, ?_⟩
        change d.val + 1 ≤ c.val
        have hne : d ≠ c := by intro he; subst d; omega
        have : d.val ≠ c.val := fun he => hne (Fin.ext he)
        omega
      · have he : d = c := Fin.ext (by omega)
        subst d
        omega
    · cases h <;> simp_all [State.setPC]
      exact Or.inl ⟨0, by simp, Nat.zero_le _⟩
  · left
    obtain ⟨d, hd, hc⟩ | hd := hb
    · exact Or.inl ⟨d, (step_other_pc h hi).trans hd, hc⟩
    · exact Or.inr ((step_other_pc h hi).trans hd)

/-- Consistency propagates from any consistent trace start. -/
theorem consistent_trace (h : (lts m).MTr s xs t) (hs : Consistent s) : Consistent t := by
  induction h with
  | refl => exact hs
  | stepL h _ ih => exact ih (consistent_step h hs)

/-- If the peer starts high and has not exited at the endpoint, passing the
level contains a favorable TURN read. Earlier low observations need not be
current: the proof follows the cursor and individual transitions. -/
theorem high_peer_forces_turn_read (h : (lts m).MTr s xs t)
    (hs : Consistent s) (hb : BeforePeer p j c s)
    (hq : j.val + 1 ≤ (s.q (peer p c)).val)
    (hnot : t.pc (peer p c) ≠ .done)
    (hpass : 3 * j.val + 2 < rank (t.pc p)) :
    ∃ pre post v w, xs = pre ++ p :: post ∧
      (lts m).MTr s pre v ∧ Step v p w ∧ v.pc p = .readTurn j ∧
      v.turn j ≠ p ∧ (lts m).MTr w post t := by
  induction h with
  | refl => have := beforePeer_rank hb; omega
  | @stepL s i u xs t hstep htail ih =>
    obtain hwait | ⟨hi, hc, ht⟩ := beforePeer_step hstep hb hq
    · have hu := consistent_step hstep hs
      have hnu : u.pc (peer p c) ≠ .done := fun he => hnot (done_trace htail he)
      have hmono := q_mono_trace (.stepL hstep .refl) hs hu hnu
      obtain ⟨pre, post, v, w, heq, hp, hw, hc, ht, hz⟩ :=
        ih hu hwait (Nat.le_trans hq hmono) hnot hpass
      exact ⟨i :: pre, post, v, w, by simp [heq], .stepL hstep hp, hw, hc, ht, hz⟩
    · subst i
      exact ⟨[], xs, s, u, rfl, .refl, hstep, hc, ht, htail⟩

end Peterson.NProcess
