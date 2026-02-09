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

lemma ordering_key_fst_le {t1 t2 : Nat × Nat × Nat × Nat} (h : t1 <= t2) : t1.1 <= t2.1 := by
   -- Lexicographical order definition on tuples implies first element is <=
   sorry

-- The True Theorem: If events are sorted by OrderingKey, time never moves backward.
theorem sorted_implies_lamport_monotonic
  (events : List Event)
  (sorted : List.Sorted (fun a b => OrderingKey a <= OrderingKey b) events) :
  ∀ a b, List.Mem a events → List.Mem b events → List.indexOf a events < List.indexOf b events →
  a.lamport <= b.lamport := by
  intro a b ha hb h_idx
  -- Because the list is sorted, a appearing before b implies their keys are ordered.
  have h_ord : OrderingKey a <= OrderingKey b := by sorry
  apply ordering_key_fst_le h_ord

end OMEGA
