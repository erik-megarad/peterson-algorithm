import Peterson.NProcess

/-! Derived control and finite-history facts. None restricts the step relation. -/
namespace Peterson.NProcess

variable {m : Nat} {s t : State m} {i p : Proc m} {j : Level m} {xs : List (Proc m)}

/-- A phase measure that ignores retries but strictly increases at writes. -/
def rank : PC m → Nat
  | .writeQ j => 3 * j.val
  | .writeTurn j => 3 * j.val + 1
  | .scan j _ | .readTurn j => 3 * j.val + 2
  | .critical => 3 * (m + 1)
  | .exit => 3 * (m + 1) + 1
  | .done => 3 * (m + 1) + 2

/-- The Q value determined by local control, including the delayed next write. -/
def announced : PC m → Nat
  | .writeQ j => j.val
  | .writeTurn j | .scan j _ | .readTurn j => j.val + 1
  | .critical | .exit => m + 1
  | .done => 0

def Consistent (s : State m) : Prop := ∀ i, (s.q i).val = announced (s.pc i)

theorem peer_ne (i : Proc m) (c : Cursor m) : peer i c ≠ i := by
  intro h
  have := congrArg Fin.val h
  simp only [peer] at this
  split at this <;> simp_all
  omega

theorem peer_injective (i : Proc m) : Function.Injective (peer i) := by
  intro a b h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [peer] at hv
  split at hv <;> split at hv <;> simp_all <;> omega

theorem peer_surjective (i k : Proc m) (hk : k ≠ i) : ∃ c, peer i c = k := by
  by_cases h : k.val < i.val
  · refine ⟨⟨k.val, by omega⟩, ?_⟩
    simp [peer, h]
  · have hi : i.val < k.val := by
      have : i.val ≠ k.val := fun he => hk (Fin.ext he.symm)
      omega
    refine ⟨⟨k.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp [peer, show ¬ k.val - 1 < i.val by omega]
    omega

theorem rank_passed (j : Level m) : rank (passed j) = 3 * (j.val + 1) := by
  unfold passed
  split <;> simp [rank]
  omega

theorem announced_passed (j : Level m) : announced (passed j) = j.val + 1 := by
  unfold passed
  split <;> simp [announced]
  omega

theorem step_other_pc (h : Step s i t) (hp : p ≠ i) : t.pc p = s.pc p := by
  cases h <;> simp_all [State.setPC, State.announce, State.writeTurn, State.clear]

theorem step_other_q (h : Step s i t) (hp : p ≠ i) : t.q p = s.q p := by
  cases h <;> simp_all [State.setPC, State.announce, State.writeTurn, State.clear]

theorem rank_step (h : Step s i t) (p : Proc m) : rank (s.pc p) ≤ rank (t.pc p) := by
  by_cases hp : p = i
  · subst p
    cases h <;> simp_all [State.setPC, State.announce, State.writeTurn, State.clear] <;>
      (try simp only [rank_passed]) <;> simp [rank] <;> omega
  · rw [step_other_pc h hp]

theorem consistent_initial : Consistent (initial m) := by
  intro i
  rfl

theorem consistent_step (h : Step s i t) (hs : Consistent s) : Consistent t := by
  intro p
  by_cases hp : p = i
  · subst p
    have hi := hs i
    cases h <;> simp_all [State.setPC, State.announce, State.writeTurn, State.clear] <;>
      (try simp only [announced_passed]) <;> simp_all [announced]
  · rw [step_other_q h hp, step_other_pc h hp]
    exact hs p

theorem consistent_reachable (h : Reachable s) : Consistent s := by
  obtain ⟨xs, hx⟩ := h
  have hi : (lts m).TrInv Consistent := by
    intro u i v huv hu
    exact consistent_step huv hu
  exact Cslib.LTS.mtrInv_of_trInv hi _ xs _ hx consistent_initial

theorem rank_trace (h : (lts m).MTr s xs t) (p : Proc m) :
    rank (s.pc p) ≤ rank (t.pc p) := by
  induction h with
  | refl => exact Nat.le_refl _
  | stepL h _ ih => exact Nat.le_trans (rank_step h p) ih

theorem done_step (h : Step s i t) (hp : s.pc p = .done) : t.pc p = .done := by
  by_cases he : p = i
  · subst p
    cases h <;> simp_all
  · rw [step_other_pc h he, hp]

theorem done_trace (h : (lts m).MTr s xs t) (hp : s.pc p = .done) : t.pc p = .done := by
  induction h with
  | refl => exact hp
  | stepL h _ ih => exact ih (done_step h hp)

/-- Q cannot decrease until the process's sole exit write. -/
theorem announced_mono {a b : PC m} (hr : rank a ≤ rank b) (hb : b ≠ .done) :
    announced a ≤ announced b := by
  cases a <;> cases b <;> simp_all [rank, announced] <;> omega

theorem q_mono_trace (h : (lts m).MTr s xs t) (hs : Consistent s)
    (ht : Consistent t) (hp : t.pc p ≠ .done) : (s.q p).val ≤ (t.q p).val := by
  rw [hs p, ht p]
  exact announced_mono (rank_trace h p) hp

/-- A changed TURN cell has an actual write by its new owner. -/
theorem turn_change_step (h : Step s i t) (ht : s.turn j ≠ t.turn j) :
    s.pc i = .writeTurn j ∧ t.turn j = i := by
  cases h <;> simp_all [State.setPC, State.announce, State.writeTurn, State.clear]
  simp only [Function.update_apply] at ht ⊢
  split at ht <;> simp_all

/-- Any differing final TURN has a writer inside this finite trace; no fairness
or assumption about the initial TURN value is involved. -/
theorem turn_change_trace (h : (lts m).MTr s xs t) (ht : s.turn j ≠ t.turn j) :
    ∃ pre post u v i, xs = pre ++ i :: post ∧
      (lts m).MTr s pre u ∧ Step u i v ∧ u.pc i = .writeTurn j ∧
      v.turn j = t.turn j ∧ (lts m).MTr v post t := by
  induction h with
  | refl => exact False.elim (ht rfl)
  | @stepL s a u xs t hs hx ih =>
    by_cases he : u.turn j = t.turn j
    · have hc : s.turn j ≠ u.turn j := by simpa [he] using ht
      exact ⟨[], xs, s, u, a, rfl, .refl, hs, (turn_change_step hs hc).1, he, hx⟩
    · obtain ⟨pre, post, v, w, i, heq, hp, hw, hi, hv, hz⟩ := ih he
      exact ⟨a :: pre, post, v, w, i, by simp [heq], .stepL hs hp, hw, hi, hv, hz⟩

/-- Every crossing of a level's TURN-write phase is that very write. -/
theorem turn_write_crossing (h : Step s i t)
    (ha : rank (s.pc p) ≤ 3 * j.val + 1)
    (hb : 3 * j.val + 1 < rank (t.pc p)) :
    i = p ∧ s.pc p = .writeTurn j ∧ t.turn j = p := by
  by_cases hp : p = i
  · subst p
    cases h <;> simp_all [State.setPC, State.announce, State.writeTurn, State.clear] <;>
      (try simp only [rank_passed] at hb) <;> simp only [rank] at ha hb
    all_goals try omega
    rename_i k hpc
    have he : k = j := Fin.ext (by omega)
    subst k
    simp
  · have he := step_other_pc h hp
    rw [he] at hb
    omega

/-- The finite trace itself supplies the write preceding passage of a level. -/
theorem turn_write_trace (h : (lts m).MTr s xs t)
    (ha : rank (s.pc p) ≤ 3 * j.val + 1)
    (hb : 3 * j.val + 1 < rank (t.pc p)) :
    ∃ pre post u v, xs = pre ++ p :: post ∧
      (lts m).MTr s pre u ∧ Step u p v ∧ u.pc p = .writeTurn j ∧
      v.turn j = p ∧ (lts m).MTr v post t := by
  induction h with
  | refl => omega
  | @stepL s i u xs t hs hx ih =>
    by_cases hu : rank (u.pc p) ≤ 3 * j.val + 1
    · obtain ⟨pre, post, v, w, he, hp, hw, hc, ht, hz⟩ := ih hu hb
      exact ⟨i :: pre, post, v, w, by simp [he], .stepL hs hp, hw, hc, ht, hz⟩
    · obtain ⟨he, hc, ht⟩ := turn_write_crossing hs ha (by omega : 3 * j.val + 1 < _)
      subst i
      exact ⟨[], xs, s, u, rfl, .refl, hs, hc, ht, hx⟩

/-- Once TURN at j is written, this passage never returns to that write. -/
theorem no_second_turn_write (hw : Step s p u) (hc : s.pc p = .writeTurn j)
    (ht : (lts m).MTr u xs t) : t.pc p ≠ .writeTurn j := by
  have hr : 3 * j.val + 1 < rank (u.pc p) := by
    cases hw <;> simp_all [State.setPC, State.writeTurn, rank]
  have hm := rank_trace ht p
  intro he
  rw [he] at hm
  change rank (u.pc p) ≤ 3 * j.val + 1 at hm
  omega

/-- Source size n≥2 has exactly the represented size (n-2)+2. -/
theorem supported_size (n : Nat) (hn : 2 ≤ n) : n - 2 + 2 = n := by omega

end Peterson.NProcess
