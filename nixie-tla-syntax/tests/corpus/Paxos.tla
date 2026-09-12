----------------------------- MODULE Paxos -----------------------------
EXTENDS Integers, FiniteSets, TLC
CONSTANTS Acceptors, Values, Quorums, Ballots

ASSUME QuorumAssumption ==
  /\ \A Q \in Quorums : Q \subseteq Acceptors
  /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
        maxVal : Values \cup {None}, acc : Acceptors]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

VARIABLES maxBal, maxVBal, maxVal, msgs

vars == <<maxBal, maxVBal, maxVal, msgs>>

Send(m) == msgs' = msgs \cup {m}

Init == /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]
        /\ msgs = {}

Phase1a(b) == /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase1b(a) ==
  /\ \E m \in msgs :
       /\ m.type = "1a"
       /\ m.bal > maxBal[a]
       /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
       /\ Send([type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a],
                maxVal |-> maxVal[a], acc |-> a])
  /\ UNCHANGED <<maxVBal, maxVal>>

Next == \/ \E b \in Ballots : Phase1a(b)
        \/ \E a \in Acceptors : Phase1b(a)

Spec == Init /\ [][Next]_vars

Inv == \A a \in Acceptors : maxBal[a] >= maxVBal[a]
=============================================================================
