import Cslib.Foundations.Semantics.LTS.Basic

/-! Figure 3, one passage. Parameter `m` means exactly `m + 2` processes;
internal identifier `p` denotes source identifier `p.val + 1`, and internal
level `j` denotes source level `j.val + 1`. This covers every size at least two.
Each scan edge reads one Q cell. No transition tests a shared snapshot. -/
namespace Peterson.NProcess

abbrev Proc (m : Nat) := Fin (m + 2)
abbrev Level (m : Nat) := Fin (m + 1)
abbrev Cursor (m : Nat) := Fin (m + 1)

inductive PC (m : Nat) where
  | writeQ (j : Level m)
  | writeTurn (j : Level m)
  | scan (j : Level m) (c : Cursor m)
  | readTurn (j : Level m)
  | critical | exit | done
  deriving DecidableEq, Repr

structure State (m : Nat) where
  q : Proc m → Fin (m + 2)
  turn : Level m → Proc m
  pc : Proc m → PC m

/-- Ascending peer enumeration, skipping the actor's identifier. -/
def peer (i : Proc m) (c : Cursor m) : Proc m :=
  if c.val < i.val then ⟨c.val, by omega⟩ else ⟨c.val + 1, by omega⟩

/-- Passing does not itself announce the next level. -/
def passed (j : Level m) : PC m :=
  if h : j.val + 1 < m + 1 then .writeQ ⟨j.val + 1, h⟩ else .critical

def State.setPC (s : State m) (i : Proc m) (v : PC m) : State m :=
  { s with pc := Function.update s.pc i v }
def State.announce (s : State m) (i : Proc m) (j : Level m) : State m :=
  { s with q := Function.update s.q i ⟨j.val + 1, by omega⟩ }
def State.writeTurn (s : State m) (i : Proc m) (j : Level m) : State m :=
  { s with turn := Function.update s.turn j i }
def State.clear (s : State m) (i : Proc m) : State m :=
  { s with q := Function.update s.q i 0 }

/-- Labels identify the selected process; its control identifies the operation. -/
inductive Step {m : Nat} : State m → Proc m → State m → Prop where
  | announce (hpc : s.pc i = .writeQ j) :
      Step s i ((s.announce i j).setPC i (.writeTurn j))
  | writeTurn (hpc : s.pc i = .writeTurn j) :
      Step s i ((s.writeTurn i j).setPC i (.scan j 0))
  | scanHigh (hpc : s.pc i = .scan j c) (hq : j.val + 1 ≤ (s.q (peer i c)).val) :
      Step s i (s.setPC i (.readTurn j))
  | scanLowNext (hpc : s.pc i = .scan j c) (hq : (s.q (peer i c)).val < j.val + 1)
      (hc : c.val + 1 < m + 1) :
      Step s i (s.setPC i (.scan j ⟨c.val + 1, hc⟩))
  | scanLowLast (hpc : s.pc i = .scan j c) (hq : (s.q (peer i c)).val < j.val + 1)
      (hc : ¬ c.val + 1 < m + 1) :
      Step s i (s.setPC i (passed j))
  | turnOther (hpc : s.pc i = .readTurn j) (ht : s.turn j ≠ i) :
      Step s i (s.setPC i (passed j))
  | turnSelf (hpc : s.pc i = .readTurn j) (ht : s.turn j = i) :
      Step s i (s.setPC i (.scan j 0))
  | finish (hpc : s.pc i = .critical) : Step s i (s.setPC i .exit)
  | clear (hpc : s.pc i = .exit) : Step s i ((s.clear i).setPC i .done)

def lts (m : Nat) : Cslib.LTS (State m) (Proc m) where
  Tr := Step

def initial (m : Nat) : State m where
  q := fun _ => 0
  turn := fun _ => 0
  pc := fun _ => .writeQ 0

def Reachable (s : State m) : Prop := (lts m).CanReach (initial m) s

def MutuallyExclusive (s : State m) : Prop :=
  ∀ p q, p ≠ q → ¬ (s.pc p = .critical ∧ s.pc q = .critical)

/-- Protected arbitrary-size target. This proposition is not asserted as a theorem. -/
def ArbitraryMutualExclusion : Prop := ∀ m (s : State m), Reachable s → MutuallyExclusive s

/-- Passed source level k, without clearing Q; k=0 is also useful for counting. -/
def Past (k : Nat) : PC m → Prop
  | .writeQ j | .writeTurn j | .scan j _ | .readTurn j => k < j.val + 1
  | .critical | .exit => True
  | .done => False

end Peterson.NProcess
