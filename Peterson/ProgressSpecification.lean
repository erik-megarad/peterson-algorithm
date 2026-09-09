import Peterson.Specification
import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Protected one-passage progress contract

This module defines the one-passage temporal contract using CSLib infinite
executions over the source-specific observation adapter. It states validity,
participating-protocol fairness, critical completion, and the global future-entry
target. These are definitions, not a proof of progress. Correspondence and proofs
belong in separate modules.
-/

namespace Peterson

/-- Observation padding copies the whole state; an action is exactly `Step`. -/
def observationLTS (order : WaitOrder) : Cslib.LTS State (Option Action) where
  Tr s label t := match label with
    | none => t = s
    | some a => Step order s a t

/-- State and event observations, with no validity or fairness built into the type. -/
structure ProgressExecution where
  state : ℕ → State
  event : ℕ → Option Action

/-- Initiality allows either turn value; every tick is an observation transition. -/
def Valid (order : WaitOrder) (E : ProgressExecution) : Prop :=
  Initial (E.state 0) ∧ (observationLTS order).OmegaExecution E.state E.event

/-- Actor argument, independent of the observed process or the value written/read. -/
def actor : Action → Proc
  | .writeFlagTrue i | .writeTurn i _ | .readFlag i _ _
  | .readTurn i _ | .finishCritical i | .writeFlagFalse i => i

/-- A request at tick `n` takes effect in state `n + 1`. -/
def Request (E : ProgressExecution) (i : Proc) (n : ℕ) : Prop :=
  E.event n = some (.writeFlagTrue i)

/-- A started request that has not entered its critical section. -/
def Pending (i : Proc) (s : State) : Prop :=
  s.pc i = .betweenWrites ∨ s.pc i = .beforeFirstRead ∨ s.pc i = .betweenReads

/-- Participating protocol positions, including the exit flag write. -/
def Protocol (i : Proc) (s : State) : Prop :=
  Pending i s ∨ s.pc i = .beforeExitWrite

/-- A new entry edge, excluding old critical occupancy and padding. -/
def Entry (E : ProgressExecution) (i : Proc) (n : ℕ) : Prop :=
  ∃ a, E.event n = some a ∧ actor a = i ∧
    (E.state n).pc i ≠ .critical ∧ (E.state (n + 1)).pc i = .critical

/-- Opaque critical work finishes, separately from the following exit write. -/
def Finish (E : ProgressExecution) (i : Proc) (n : ℕ) : Prop :=
  E.event n = some (.finishCritical i)

/-- Some actor outcome is enabled at a participating protocol position. -/
def Enabled (order : WaitOrder) (i : Proc) (s : State) : Prop :=
  Protocol i s ∧ ∃ a t, actor a = i ∧ Step order s a t

/-- A participating actor step, with no requirement of a favorable read. -/
def Taken (E : ProgressExecution) (i : Proc) (n : ℕ) : Prop :=
  Protocol i (E.state n) ∧ ∃ a, E.event n = some a ∧ actor a = i

/-- Aggregate weak fairness on every suffix; optional initiation is excluded. -/
def ProtocolFair (order : WaitOrder) (E : ProgressExecution) : Prop :=
  ∀ i m, (∀ k, m ≤ k → Enabled order i (E.state k)) →
    ∃ n, m ≤ n ∧ Taken E i n

/-- Every critical occupant eventually finishes its opaque critical work. -/
def CriticalCompletes (E : ProgressExecution) : Prop :=
  ∀ i m, (E.state m).pc i = .critical → ∃ n, m ≤ n ∧ Finish E i n

/--
The accepted global future-entry target. The witness actor need not be the
pending actor. Tick `n = m` is future entry from observation `m`; an entry at
`m - 1` cannot discharge the obligation. No progress proof is declared here.
-/
def PetersonGlobalProgress : Prop :=
  ∀ order E, Valid order E → ProtocolFair order E → CriticalCompletes E →
    ∀ m, (∃ i, Pending i (E.state m)) → ∃ j n, m ≤ n ∧ Entry E j n

end Peterson
