------------------------------- MODULE EWD998 -------------------------------
EXTENDS Integers, FiniteSets, Sequences, Naturals
CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1
Color == {"white", "black"}

VARIABLES active, color, counter, pending, token

vars == <<active, color, counter, pending, token>>

TokenPerm == [pos: Node, q: Int, color: Color]

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token \in TokenPerm

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color  \in [Node -> Color]
  /\ counter = [n \in Node |-> 0]
  /\ pending = [n \in Node |-> 0]
  /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

InitiateProbe ==
  /\ token.pos = 0
  /\ \/ token.color = "black"
     \/ color[0] = "black"
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [color EXCEPT ![0] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

PassToken(i) ==
  /\ ~ active[i]
  /\ token.pos = i
  /\ token' = [token EXCEPT !.pos = @ - 1,
                            !.q = @ + counter[i],
                            !.color = IF color[i] = "black" THEN "black" ELSE @]
  /\ color' = [color EXCEPT ![i] = "white"]
  /\ UNCHANGED <<active, counter, pending>>

SendMsg(i) ==
  /\ active[i]
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  /\ \E j \in Node \ {i} :
        pending' = [pending EXCEPT ![j] = @ + 1]
  /\ UNCHANGED <<active, color, token>>

System == \/ InitiateProbe
          \/ \E i \in Node \ {0} : PassToken(i)

Environment == \E i \in Node : SendMsg(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

Inv == terminationDetected => (\A i \in Node : ~ active[i])

THEOREM Spec => []TypeOK
=============================================================================
