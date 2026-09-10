import Peterson.Repeated.Specification
import Peterson.Safety
import Peterson.Progress

/-! Restart preservation and exact finite/observation correspondence. -/
namespace Peterson.Repeated

/-- Restart leaves all three invariant control ranges unchanged. -/
theorem restart_ranges {s : State} {i : Proc} (hpc : s.pc i = .afterPassage)
    (j : Proc) (range : Set PC) (hr : range .beforeFlag ↔ range .afterPassage) :
    range ((s.setPC i .beforeFlag).pc j) ↔ range (s.pc j) := by
  by_cases h : j = i
  · subst j
    simpa [hpc] using hr
  · simp [State.setPC, Function.update, h]

theorem invariant_restart {s : State} {i : Proc}
    (hpc : s.pc i = .afterPassage) (hinv : Invariant s) :
    Invariant (s.setPC i .beforeFlag) := by
  have hi := fun j => restart_ranges hpc j Interested (by rfl)
  have ht := fun j => restart_ranges hpc j TurnWritten (by rfl)
  have hp := fun j => restart_ranges hpc j PastWait (by rfl)
  intro j
  constructor
  · intro h
    exact (hinv j).1 ((hi j).mp h)
  · intro h
    exact (hinv j).2 ⟨(hp j).mp h.1, (ht j.other).mp h.2⟩

theorem invariant_step (order : WaitOrder) :
    (repeatedLTS order).TrInv Invariant := by
  intro s a t h hinv
  cases h with
  | protocol h => exact Peterson.invariant_step order s _ t h hinv
  | restart hpc => exact invariant_restart hpc hinv

theorem invariant_reachable {order : WaitOrder} {s : State}
    (h : Reachable order s) : Invariant s := by
  obtain ⟨s₀, hi, actions, ht⟩ := h
  exact Cslib.LTS.mtrInv_of_trInv (invariant_step order) s₀ actions s ht
    (Peterson.invariant_initial hi)

/-- No fairness is required, and the initial turn and fixed order are arbitrary. -/
theorem repeated_mutual_exclusion : RepeatedMutualExclusion := by
  intro order s h
  exact Peterson.invariant_mutuallyExclusive (invariant_reachable h)

theorem flag_iff_interested_step {order : WaitOrder} {s t : State}
    {a : RepeatedAction} (h : Step order s a t)
    (hf : ∀ i, s.flag i = true ↔ Interested (s.pc i)) :
    ∀ i, t.flag i = true ↔ Interested (t.pc i) := by
  cases h with
  | protocol h => exact Peterson.flag_iff_interested_step h hf
  | restart hpc =>
    intro j
    exact (hf j).trans (restart_ranges hpc j Interested (by rfl)).symm

theorem flag_iff_interested_reachable {order : WaitOrder} {s : State}
    (h : Reachable order s) (i : Proc) :
    s.flag i = true ↔ Interested (s.pc i) := by
  obtain ⟨s₀, hi, actions, ht⟩ := h
  have hp : (repeatedLTS order).TrInv
      (fun s => ∀ j, s.flag j = true ↔ Interested (s.pc j)) := by
    intro s a t hs hf
    exact flag_iff_interested_step hs hf
  exact Cslib.LTS.mtrInv_of_trInv hp s₀ actions s ht
    (Peterson.flag_iff_interested_initial hi) i

/-- All old traces embed with identical states and protocol-wrapped labels. -/
theorem mTr_protocol {order : WaitOrder} {s t : State} {actions : List Action}
    (h : (petersonLTS order).MTr s actions t) :
    (repeatedLTS order).MTr s (actions.map RepeatedAction.protocol) t := by
  induction h with
  | refl => exact .refl
  | stepL h _ ih => exact .stepL (.protocol h) ih

/-- A trace containing only protocol labels is exactly an old-model trace. -/
theorem mTr_protocol_iff {order : WaitOrder} {s t : State} {actions : List Action} :
    (repeatedLTS order).MTr s (actions.map RepeatedAction.protocol) t ↔
      (petersonLTS order).MTr s actions t := by
  constructor
  · intro h
    induction actions generalizing s with
    | nil => cases h; exact .refl
    | cons a actions ih =>
      cases h with
      | stepL hs ht =>
        cases hs with
        | protocol hs => exact .stepL hs (ih ht)
  · exact mTr_protocol

theorem old_reachable {order : WaitOrder} {s : State}
    (h : Peterson.Reachable order s) : Reachable order s := by
  obtain ⟨s₀, hi, actions, ht⟩ := h
  exact ⟨s₀, hi, _, mTr_protocol ht⟩

theorem valid_iff {order : WaitOrder} {E : Execution} :
    Valid order E ↔ Initial (E.state 0) ∧
      (∀ n, E.event n = none → E.state (n + 1) = E.state n) ∧
      (∀ n a, E.event n = some a → Step order (E.state n) a (E.state (n + 1))) := by
  constructor
  · rintro ⟨hi, ht⟩
    refine ⟨hi, ?_, ?_⟩
    · intro n hn
      simpa [observationLTS, hn] using ht n
    · intro n a ha
      simpa [observationLTS, ha] using ht n
  · rintro ⟨hi, hn, ha⟩
    refine ⟨hi, ?_⟩
    intro n
    cases h : E.event n with
    | none => simpa [observationLTS, h] using hn n h
    | some a => simpa [observationLTS, h] using ha n a h

theorem observation_mTr_erase {order : WaitOrder} {s t : State}
    {labels : List (Option RepeatedAction)} (h : (observationLTS order).MTr s labels t) :
    (repeatedLTS order).MTr s (labels.filterMap id) t := by
  induction h with
  | refl => exact .refl
  | @stepL s label u labels t hstep _ ih =>
    cases label with
    | none =>
      change u = s at hstep
      subst u
      simpa using ih
    | some a => exact .stepL hstep ih

theorem valid_prefix_mTr {order : WaitOrder} {E : Execution}
    (h : Valid order E) {m n : ℕ} (hmn : m ≤ n) :
    (repeatedLTS order).MTr (E.state m)
      (((Cslib.ωSequence.mk E.event).extract m n).filterMap id) (E.state n) := by
  exact observation_mTr_erase (h.2.extract_mTr hmn)

theorem valid_reachable {order : WaitOrder} {E : Execution}
    (h : Valid order E) (n : ℕ) : Reachable order (E.state n) := by
  exact ⟨E.state 0, h.1, _, valid_prefix_mTr h (Nat.zero_le n)⟩

theorem valid_mutuallyExclusive {order : WaitOrder} {E : Execution}
    (h : Valid order E) (n : ℕ) : MutuallyExclusive (E.state n) :=
  repeated_mutual_exclusion order _ (valid_reachable h n)

/-- An repeated finite trace embeds with one `some` label per atomic action. -/
theorem mTr_observation {order : WaitOrder} {s t : State} {actions : List RepeatedAction}
    (h : (repeatedLTS order).MTr s actions t) :
    (observationLTS order).MTr s (actions.map some) t := by
  induction h with
  | refl => exact .refl
  | stepL hstep _ ih => exact .stepL hstep ih

open Cslib.ωSequence in
/--
Every initialized finite repeated trace has a valid infinite extension that
pads its terminal state forever. Its repeated labels occur at exactly their
repeated indices. This establishes validity only, not fairness or completion.
-/
theorem mTr_exists_valid_padding {order : WaitOrder} {s t : State}
    {actions : List RepeatedAction} (hi : Initial s)
    (h : (repeatedLTS order).MTr s actions t) :
    ∃ E : Execution, Valid order E ∧ E.state 0 = s ∧
      (∀ n (hn : n < actions.length), E.event n = some actions[n]) ∧
      (∀ n, E.state (actions.length + n) = t ∧ E.event (actions.length + n) = none) := by
  let tailStates : Cslib.ωSequence State := ⟨fun _ => t⟩
  let tailEvents : Cslib.ωSequence (Option RepeatedAction) := ⟨fun _ => none⟩
  have htail : (observationLTS order).OmegaExecution tailStates tailEvents := by
    intro n
    rfl
  obtain ⟨ss, hs, hzero, _, hdrop⟩ :=
    Cslib.LTS.OmegaExecution.append (mTr_observation h) htail (show tailStates 0 = t from rfl)
  let events := actions.map some ++ω tailEvents
  refine ⟨⟨fun n => ss n, fun n => events n⟩, ⟨?_, hs⟩, hzero, ?_, ?_⟩
  · simpa [hzero] using hi
  · intro n hn
    change (actions.map some ++ω tailEvents) n = some actions[n]
    rw [get_append_left n (actions.map some) tailEvents (by simpa using hn)]
    simp
  · intro n
    constructor
    · have hd := congrArg (fun seq : Cslib.ωSequence State => seq n) hdrop
      simpa [get_drop, Nat.add_comm, tailStates] using hd
    · simpa [events, tailEvents] using get_append_right n (actions.map some) tailEvents


end Peterson.Repeated
