import Peterson.Repeated.Specification
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

/-! Protected transcription of the independently reviewed quantitative target.
The observer counts events, without changing algorithm state or request identity. -/
namespace Peterson.Repeated

def PendingThrough (E : Execution) (i : Proc) (r b : ℕ) : Prop :=
  r < b ∧ ∀ k, r < k ∧ k ≤ b → Pending i (E.state k)

def TurnWrite (E : Execution) (i : Proc) (t : ℕ) : Prop :=
  E.event t = some (.protocol (.writeTurn i i))

noncomputable def peerEntryIndices (E : Execution) (i : Proc) (a b : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun k => a < k ∧ Entry E i.other k) (Classical.decPred _)
    (Finset.range b)

noncomputable def PeerEntries (E : Execution) (i : Proc) (a b : ℕ) : ℕ :=
  (peerEntryIndices E i a b).card

def RepeatedOvertakingBound : Prop :=
  ∀ order E, Valid order E → ∀ i r b,
    Request E i r → PendingThrough E i r b → PeerEntries E i r b ≤ 1

def RepeatedPreTurnZero : Prop :=
  ∀ order E, Valid order E → ∀ i r b,
    Request E i r → PendingThrough E i r b →
    (∀ t, r < t ∧ t < b → ¬ TurnWrite E i t) → PeerEntries E i r b = 0

def RepeatedAfterTurnBound : Prop :=
  ∀ order E, Valid order E → ∀ i r t b,
    Request E i r → PendingThrough E i r b →
    r < t → t < b → TurnWrite E i t → PeerEntries E i t b ≤ 1

def RepeatedBoundedService : Prop :=
  ∀ order E, Valid order E → ProtocolFair order E → CriticalCompletes E →
    ∀ i r, Request E i r → ∃ n, Serves E i r n ∧ PeerEntries E i r n ≤ 1

def RepeatedOvertakingSharp : Prop :=
  ∀ order i initialTurn, ∃ E : Execution,
    Valid order E ∧ (E.state 0).turn = initialTurn ∧
    ProtocolFair order E ∧ CriticalCompletes E ∧
    ∃ r t n, Request E i r ∧ TurnWrite E i t ∧ Serves E i r n ∧
      r < t ∧ t < n ∧ PeerEntries E i r n = 1 ∧ PeerEntries E i t n = 1

end Peterson.Repeated
