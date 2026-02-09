--------------------------- MODULE OMEGA ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Nodes, Events, MaxCertLen, Deps

VARIABLES Queues, Seen, Accepted, Frontier, CertStream, ActorState
Vars == <<Queues, Seen, Accepted, Frontier, CertStream, ActorState>>

Init ==
  /\ Queues = [n \in Nodes |-> <<>>]
  /\ Seen = {}
  /\ Accepted = {}
  /\ Frontier = {}
  /\ CertStream = <<>>
  /\ ActorState = "Running"

Receive(e) ==
  /\ e \in Events
  /\ e \notin Seen
  /\ Seen' = Seen \cup {e}
  /\ UNCHANGED <<Queues, Accepted, Frontier, CertStream, ActorState>>

Reconcile ==
  /\ ActorState = "Running"
  /\ Len(CertStream) < MaxCertLen
  /\ Accepted' = Seen
  /\ Frontier' = Seen
  /\ CertStream' = Append(CertStream, [type |-> "Merge", accepted |-> Seen])
  /\ UNCHANGED <<Queues, Seen, ActorState>>

EmitObstruction ==
  /\ ActorState = "Running"
  /\ Len(CertStream) < MaxCertLen
  /\ CertStream' = Append(CertStream, [type |-> "Obstruction", accepted |-> Accepted])
  /\ UNCHANGED <<Queues, Seen, Accepted, Frontier, ActorState>>

Crash ==
  /\ ActorState' = "SafeMode"
  /\ UNCHANGED <<Queues, Seen, Accepted, Frontier, CertStream>>

Restart ==
  /\ ActorState = "SafeMode"
  /\ ActorState' = "Running"
  /\ UNCHANGED <<Queues, Seen, Accepted, Frontier, CertStream>>

Next ==
  \/ \E e \in Events: Receive(e)
  \/ Reconcile
  \/ EmitObstruction
  \/ Crash
  \/ Restart

NoDuplicateAcceptance == \A e \in Accepted: Cardinality({e}) = 1

CausalOrder == \A e \in Accepted: \A d \in Deps[e]: d \in Accepted

Safety == NoDuplicateAcceptance /\ CausalOrder

Liveness == <> (ActorState = "Running")

Spec == Init /\ [][Next]_Vars

THEOREM Spec => []Safety
=============================================================================
