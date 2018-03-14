------------------------------ MODULE DieHard ------------------------------
EXTENDS Naturals, Sequences, TLC

Min(m,n) == IF m < n THEN m ELSE n

(* --fair algorithm dlm
variables
    jugs = << 0, 0 >>;
    capacity_of = << 3, 5 >>;

begin
    while TRUE do
        with j \in 1..2 do
            assert jugs[j] # 4
        end with;
        either \* Empty Jug
            with j \in 1..2 do
                jugs[j] := 0;
            end with;
        or \* Fill Jug
            with j \in 1..2 do
                jugs[j] := capacity_of[j];
            end with;
        or \* Move water from jugs
            with j \in 1..2,
                 k \in 1..2 \ {j},
                 to_transfer = Min(jugs[j], capacity_of[k] - jugs[k])
            do
                jugs[j] := jugs[j] - to_transfer || jugs[k] := jugs[k] + to_transfer;
            end with;
        end either;
    end while;
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES jugs, capacity_of

vars == << jugs, capacity_of >>

Init == (* Global variables *)
        /\ jugs = << 0, 0 >>
        /\ capacity_of = << 3, 5 >>

Next == /\ \E j \in 1..2:
             Assert(jugs[j] # 4, 
                    "Failure of assertion at line 14, column 13.")
        /\ \/ /\ \E j \in 1..2:
                   jugs' = [jugs EXCEPT ![j] = 0]
           \/ /\ \E j \in 1..2:
                   jugs' = [jugs EXCEPT ![j] = capacity_of[j]]
           \/ /\ \E j \in 1..2:
                   \E k \in 1..2 \ {j}:
                     LET to_transfer == Min(jugs[j], capacity_of[k] - jugs[k]) IN
                       jugs' = [jugs EXCEPT ![j] = jugs[j] - to_transfer,
                                            ![k] = jugs[k] + to_transfer]
        /\ UNCHANGED capacity_of

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Mar 14 11:10:46 CET 2018 by gwagwa
\* Created Wed Mar 14 10:42:25 CET 2018 by gwagwa
