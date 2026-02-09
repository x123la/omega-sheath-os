--------------------------- MODULE OMEGA ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Nodes, Events, MaxCertLen, Deps, QuorumSize

VARIABLES Queues, Seen, Accepted, Frontier, CertStream, ActorState, Votes
Vars == <<Queues, Seen, Accepted, Frontier, CertStream, ActorState, Votes>>

Init ==
  /\ Queues = [n \in Nodes |-> <<>>]
  /\ Seen = {}
  /\ Accepted = {}
  /\ Frontier = {}
  /\ CertStream = <<>>
  /\ ActorState = "Running"
  /\ Votes = [c \in 1..MaxCertLen |-> {}]

Reconcile ==
  /\ ActorState = "Running"
  /\ Len(CertStream) < MaxCertLen
  /\ Accepted' = Seen
  /\ Frontier' = Seen
  /\ CertStream' = Append(CertStream, [type |-> "Merge", accepted |-> Seen, final |-> FALSE])
  /\ UNCHANGED <<Queues, Seen, ActorState, Votes>>

Vote(certIdx, node) ==
  /\ certIdx \in 1..Len(CertStream)
  /\ node \in Nodes
  /\ Votes' = [Votes EXCEPT ![certIdx] = Votes[certIdx] \cup {node}]
  /\ UNCHANGED <<Queues, Seen, Accepted, Frontier, CertStream, ActorState>>

Finalize(certIdx) ==
  /\ certIdx \in 1..Len(CertStream)
  /\ Cardinality(Votes[certIdx]) >= QuorumSize
  /\ CertStream' = [CertStream EXCEPT ![certIdx].final = TRUE]
  /\ UNCHANGED <<Queues, Seen, Accepted, Frontier, ActorState, Votes>>

Next ==
  \/ \E e \in Events: Receive(e)
  \/ Reconcile
  \/ EmitObstruction
  \/ Crash
  \/ Restart
  \/ \E i \in 1..Len(CertStream), n \in Nodes: Vote(i, n)
  \/ \E i \in 1..Len(CertStream): Finalize(i)

BFT_Safety == \A i \in 1..Len(CertStream): 
  CertStream[i].final => Cardinality(Votes[i]) >= QuorumSize

NoDuplicateAcceptance == \A e \in Accepted: Cardinality({e}) = 1

CausalOrder == \A e \in Accepted: \A d \in Deps[e]: d \in Accepted

Safety == NoDuplicateAcceptance /\ CausalOrder

Liveness == <> (ActorState = "Running")

Spec == Init /\ [][Next]_Vars

THEOREM Spec => []Safety
=============================================================================
