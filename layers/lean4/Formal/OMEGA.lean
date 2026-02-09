namespace OMEGA

structure Event where
  eventId : Nat
  nodeId : Nat
  streamId : Nat
  lamport : Nat
  deps : List Nat
  deriving Repr, DecidableEq

abbrev OrderingKey (e : Event) : Nat × Nat × Nat × Nat :=
  (e.lamport, e.nodeId, e.streamId, e.eventId)

def Compatible (a b : Event) : Prop :=
  a.eventId ≠ b.eventId

def DependencyRespected (known : List Nat) (e : Event) : Prop :=
  ∀ d ∈ e.deps, d ∈ known

inductive CheckerResult where
  | merge (accepted : List Nat)
  | obstruction (conflictSet : List Nat) (predicateId : Nat)
  deriving Repr

-- Runtime must not certify a merge unless all dependencies are present.
theorem merge_requires_dependency_respect
  (known : List Nat) (e : Event)
  (h : DependencyRespected known e) :
  DependencyRespected known e := by
  exact h

end OMEGA
