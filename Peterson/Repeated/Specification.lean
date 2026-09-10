import Peterson.ProgressSpecification

/-! Protected transcription of the owner-accepted repeated-use target.
Protocol edges reuse the original relation literally; restart is private.
The request-entry proposition is a future proof target, not an assumption. -/
namespace Peterson.Repeated

inductive RepeatedAction where
  | protocol (action : Action)
  | restart (actor : Proc)
  deriving DecidableEq, Repr

inductive Step (order : WaitOrder) : State → RepeatedAction → State → Prop where
  | protocol (h : Peterson.Step order s a t) : Step order s (.protocol a) t
  | restart (hpc : s.pc i = .afterPassage) :
      Step order s (.restart i) (s.setPC i .beforeFlag)

def repeatedLTS (order : WaitOrder) : Cslib.LTS State RepeatedAction where
  Tr := Step order

def Reachable (order : WaitOrder) (s : State) : Prop :=
  ∃ s₀, Initial s₀ ∧ (repeatedLTS order).CanReach s₀ s

def observationLTS (order : WaitOrder) : Cslib.LTS State (Option RepeatedAction) where
  Tr s label t := match label with
    | none => t = s
    | some a => Step order s a t

structure Execution where
  state : ℕ → State
  event : ℕ → Option RepeatedAction

def Valid (order : WaitOrder) (E : Execution) : Prop :=
  Initial (E.state 0) ∧ (observationLTS order).OmegaExecution E.state E.event

def Request (E : Execution) (i : Proc) (r : ℕ) : Prop :=
  E.event r = some (.protocol (.writeFlagTrue i))

def Entry (E : Execution) (i : Proc) (n : ℕ) : Prop :=
  ∃ a, E.event n = some (.protocol a) ∧ Peterson.actor a = i ∧
    (E.state n).pc i ≠ .critical ∧ (E.state (n + 1)).pc i = .critical

def Finish (E : Execution) (i : Proc) (n : ℕ) : Prop :=
  E.event n = some (.protocol (.finishCritical i))

def Serves (E : Execution) (i : Proc) (r n : ℕ) : Prop :=
  r < n ∧ Entry E i n ∧ ∀ k, r < k ∧ k ≤ n → Pending i (E.state k)

def Enabled (order : WaitOrder) (i : Proc) (s : State) : Prop :=
  Protocol i s ∧ ∃ a t, Peterson.actor a = i ∧ Peterson.Step order s a t

def Taken (E : Execution) (i : Proc) (n : ℕ) : Prop :=
  Protocol i (E.state n) ∧ ∃ a, E.event n = some (.protocol a) ∧ Peterson.actor a = i

def ProtocolFair (order : WaitOrder) (E : Execution) : Prop :=
  ∀ i m, (∀ k, m ≤ k → Enabled order i (E.state k)) →
    ∃ n, m ≤ n ∧ Taken E i n

def CriticalCompletes (E : Execution) : Prop :=
  ∀ i m, (E.state m).pc i = .critical → ∃ n, m ≤ n ∧ Finish E i n

def RepeatedMutualExclusion : Prop :=
  ∀ order s, Reachable order s → Peterson.MutuallyExclusive s

def RepeatedRequestEntry : Prop :=
  ∀ order E, Valid order E → ProtocolFair order E → CriticalCompletes E →
    ∀ i r, Request E i r → ∃ n, Serves E i r n

end Peterson.Repeated
