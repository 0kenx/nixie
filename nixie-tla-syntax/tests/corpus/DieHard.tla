---------------------------- MODULE DieHard ----------------------------
EXTENDS Integers
VARIABLES big, small

TypeOK == /\ small \in 0..3
          /\ big   \in 0..5

Init == /\ big = 0
        /\ small = 0

FillSmall == /\ small' = 3
             /\ big' = big

FillBig == /\ big' = 5
           /\ small' = small

EmptySmall == /\ small' = 0
              /\ big' = big

SmallToBig == IF big + small =< 5
                THEN /\ big' = big + small
                     /\ small' = 0
                ELSE /\ big' = 5
                     /\ small' = small - (5 - big)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ SmallToBig

NotSolved == big # 4
=============================================================================
