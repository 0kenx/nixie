---- MODULE Torture ----
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS N, Proc, F(_), G(_, _)
VARIABLES s, t

\* @type: Set(Int) => Int;
Sum(S) == CHOOSE n \in Int : TRUE

Empty == <<>>
Cart == Proc \X Proc \X Int
Dom == DOMAIN s
Card == Cardinality(Proc) > 0
Pow == SUBSET Proc
Big == UNION {{1}, {2}}

Nested == [a |-> [b |-> [c |-> 1]], d |-> <<1, 2>>]

Deep == [s EXCEPT ![1].fld[2] = @ + 1]

HigherOrder == F(LAMBDA x : x + 1)

Cond ==
  /\ LET local == 1
         other == 2
     IN local + other > 0
  /\ IF s = 0
       THEN t' = 1
       ELSE t' = 2
  /\ CASE s = 1 -> t' = 1
       [] s = 2 -> t' = 2
       [] OTHER -> t' = 0

Quantified ==
  /\ \E i \in 1..N :
        /\ s' = i
        /\ t' = i
  /\ \A i, j \in Proc :
        i # j => s[i] # s[j]

Temporal == []<>(s = 0) /\ <>[](t = 1) /\ (s = 0 ~> t = 1)

Strings == "a\tb\"c\\d"

Seqs == Append(Tail(<<1,2,3>>), 4) \o <<5>>

FnSetOfRec == [Proc -> [x : Int, y : BOOLEAN]]

Mapped == {f[i] : i \in DOMAIN f}
Filtered == {x \in Proc : \E y \in Proc : y # x}

Parens == (1 + 2) * 3 - -4

Chained == (a \cup b \cup c) \cap d

Prime == /\ s' = s + 1  \* trailing comment
         /\ t' = t

Assoc == G(1, 2) + G(3, 4)

THEOREM Cond => Temporal
====
