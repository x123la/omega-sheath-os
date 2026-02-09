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

theorem ordering_key_fst_le {t1 t2 : Nat × Nat × Nat × Nat} (h : t1 <= t2) : t1.1 <= t2.1 := by
  -- Lexicographical order on Nat tuples means if t1 <= t2, then t1.1 <= t2.1 or (t1.1 = t2.1 and ...)
  match t1, t2 with
  | (a1, b1, c1, d1), (a2, b2, c2, d2) =>
    exact (Prod.Lex.le_iff.1 h).left

-- The True Theorem: If events are sorted by OrderingKey, time never moves backward.
theorem sorted_implies_lamport_monotonic
  (events : List Event)
  (sorted : List.Sorted (fun a b => OrderingKey a <= OrderingKey b) events) :
  ∀ a b, a ∈ events → b ∈ events → List.indexOf a events < List.indexOf b events →
  a.lamport <= b.lamport := by
  intro a b ha hb h_idx
  -- Get the keys from the sorted list property
  have h_le := List.Sorted.rel_of_indexOf_le sorted (Nat.le_of_lt h_idx)
  -- Apply the lemma that lexicographical comparison of keys preserves lamport order
  apply ordering_key_fst_le h_le

end OMEGA
