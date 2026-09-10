import Peterson.NProcessScan
import Mathlib.Data.Fintype.Card

namespace Peterson.NProcess
variable {m : Nat} {s t : State m} {p : Proc m} {j : Level m}
  {xs : List (Proc m)} {S : Finset (Proc m)}

theorem past_rank {a : PC m} (h : Past (j.val + 1) a) :
    3 * j.val + 2 < rank a ∧ a ≠ .done := by
  cases a <;> simp_all [Past, rank] <;> omega

theorem rank_high_q {a : PC m} (h : 3 * j.val + 1 < rank a) (hn : a ≠ .done) :
    j.val + 1 ≤ announced a := by
  cases a <;> simp_all [rank, announced] <;> omega

theorem rank_past_previous {a : PC m} (h : 3 * j.val + 1 < rank a) (hn : a ≠ .done) :
    Past j.val a := by
  cases a <;> simp_all [rank, Past] <;> omega

/-- First trace point where every member has crossed its TURN-write phase.
Its actor is the latest writer among this set; no time bound is imposed. -/
theorem latest_set_writer (h : (lts m).MTr s xs t)
    (hs : ¬ ∀ p ∈ S, 3 * j.val + 1 < rank (s.pc p))
    (ht : ∀ p ∈ S, 3 * j.val + 1 < rank (t.pc p)) :
    ∃ pre post u v p, xs = pre ++ p :: post ∧ p ∈ S ∧
      (lts m).MTr s pre u ∧ Step u p v ∧ u.pc p = .writeTurn j ∧
      v.turn j = p ∧ (∀ q ∈ S, 3 * j.val + 1 < rank (v.pc q)) ∧
      (lts m).MTr v post t := by
  classical
  induction h with
  | refl => exact False.elim (hs ht)
  | @stepL s i u xs t hstep htail ih =>
    by_cases hu : ∀ p ∈ S, 3 * j.val + 1 < rank (u.pc p)
    · push Not at hs
      obtain ⟨p, hp, hlow⟩ := hs
      obtain ⟨hi, hc, hv⟩ := turn_write_crossing hstep hlow (hu p hp)
      subst i
      exact ⟨[], xs, s, u, p, rfl, hp, .refl, hstep, hc, hv, hu, htail⟩
    · obtain ⟨pre, post, v, w, p, he, hp, hh, hw, hc, hv, hall, hz⟩ := ih hu ht
      exact ⟨i :: pre, post, v, w, p, by simp [he], hp, .stepL hstep hh,
        hw, hc, hv, hall, hz⟩

/-- A set of at least two processes past this level forces an extra process
at the preceding level in an earlier reachable state. This is the counting
step's historical witness, derived from individual reads and writes. -/
theorem predecessor_extra (ht : Reachable t) (hc : 1 < S.card)
    (hall : ∀ p ∈ S, Past (j.val + 1) (t.pc p)) :
    ∃ u r, Reachable u ∧ r ∉ S ∧ Past j.val (u.pc r) ∧
      ∀ q ∈ S, Past j.val (u.pc q) := by
  classical
  obtain ⟨xs, htrace⟩ := ht
  have hlast : ∀ p ∈ S, 3 * j.val + 1 < rank (t.pc p) := by
    intro p hp
    have := (past_rank (hall p hp)).1
    omega
  have hfirst : ¬ ∀ p ∈ S, 3 * j.val + 1 < rank ((initial m).pc p) := by
    obtain ⟨p, hp, q, hq, _⟩ := Finset.one_lt_card.mp hc
    intro ha
    have := ha p hp
    simp [initial, rank] at this
  obtain ⟨pre, post, a, b, p, _, hp, hpre, hw, hpc, hturn, hcross, hpost⟩ :=
    latest_set_writer htrace hfirst hlast
  have hb : Consistent b := consistent_step hw (consistent_trace hpre consistent_initial)
  have hscan : b.pc p = .scan j 0 := by
    cases hw <;> simp_all [State.setPC, State.writeTurn]
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ S, q ≠ p := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hc
    by_cases he : x = p
    · exact ⟨y, hy, by simpa [he] using hxy.symm⟩
    · exact ⟨x, hx, he⟩
  obtain ⟨c, hpeer⟩ := peer_surjective p q hqp
  have hnq : t.pc (peer p c) ≠ .done := by
    rw [hpeer]
    exact (past_rank (hall q hq)).2
  have hbn : b.pc q ≠ .done := fun he =>
    (past_rank (hall q hq)).2 (done_trace hpost he)
  have hbq : j.val + 1 ≤ (b.q (peer p c)).val := by
    rw [hpeer, hb q]
    exact rank_high_q (hcross q hq) hbn
  obtain ⟨front, back, v, w, _, hfront, hread, _, hdiff, hback⟩ :=
    high_peer_forces_turn_read hpost hb (beforePeer_initial_scan hscan) hbq hnq
      (past_rank (hall p hp)).1
  have hchange : b.turn j ≠ v.turn j := by rw [hturn]; exact Ne.symm hdiff
  obtain ⟨front', back', u, z, r, _, hfront', hwrite, hrpc, _, hback'⟩ :=
    turn_change_trace hfront hchange
  have hbefore : (lts m).MTr (initial m) ((pre ++ [p]) ++ front') u :=
    Cslib.LTS.MTr.comp (lts m) (Cslib.LTS.MTr.stepR (lts m) hpre hw) hfront'
  have hafter : (lts m).MTr u (r :: (back' ++ p :: back)) t :=
    .stepL hwrite (Cslib.LTS.MTr.comp (lts m) hback' (.stepL hread hback))
  have hrank : ∀ q ∈ S, 3 * j.val + 1 < rank (u.pc q) := by
    intro q hq
    exact Nat.lt_of_lt_of_le (hcross q hq) (rank_trace hfront' q)
  refine ⟨u, r, ⟨_, hbefore⟩, ?_, ?_, ?_⟩
  · intro hr
    have := hrank r hr
    rw [hrpc] at this
    simp [rank] at this
  · simp [hrpc, Past]
  · intro q hq
    exact rank_past_previous (hrank q hq)
      (fun he => (past_rank (hall q hq)).2 (done_trace hafter he))

/-- At most n-k processes have passed source level k without clearing Q.
The induction is uniform over every reachable state and finite subset. -/
theorem level_capacity (k : Nat) (hk : k ≤ m + 1) (ht : Reachable t)
    (hall : ∀ p ∈ S, Past k (t.pc p)) : S.card ≤ m + 2 - k := by
  classical
  induction k generalizing t S with
  | zero => simpa using S.card_le_univ
  | succ k ih =>
    by_cases hc : S.card ≤ 1
    · omega
    · let j : Level m := ⟨k, by omega⟩
      obtain ⟨u, r, hu, hr, hpr, hps⟩ := predecessor_extra (j := j) ht (by omega) hall
      have hinsert : ∀ p ∈ insert r S, Past k (u.pc p) := by
        intro p hp
        obtain he | hp := Finset.mem_insert.mp hp
        · subst p
          exact hpr
        · exact hps p hp
      have hbound := ih (by omega) hu hinsert
      rw [Finset.card_insert_of_notMem hr] at hbound
      omega

/-- The exact reviewed arbitrary-size safety target, with no fairness,
snapshot, bounded-run, or additional initial-state assumption. -/
theorem arbitrary_mutual_exclusion : ArbitraryMutualExclusion := by
  classical
  intro m s hs p q hpq hboth
  have hmembers : ∀ r ∈ ({p, q} : Finset (Proc m)), Past (m + 1) (s.pc r) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    obtain rfl | rfl := hr
    · simp [hboth.1, Past]
    · simp [hboth.2, Past]
  have hc := level_capacity (m + 1) (Nat.le_refl _) hs hmembers
  simp [hpq] at hc

end Peterson.NProcess
