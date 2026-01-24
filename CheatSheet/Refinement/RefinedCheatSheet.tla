---- MODULE RefinedCheatSheet ----
\* Refined version of CheatSheet
\* Breaks down x into two internal variables (high and low nibbles)

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Users, Pages, MaxValue
VARIABLE xHigh, xLow, y, z, seq, rec

\* ============================================================================
\* REFINEMENT MAPPING
\* ============================================================================
\* x (in high-level) maps to xHigh * 2 + xLow (in low-level)

x == xHigh * 2 + xLow

\* Instance of the abstract specification
AbstractCheatSheet == INSTANCE CheatSheet

\* ============================================================================
\* TYPE INVARIANT (for refined spec)
\* ============================================================================

TypeOK ==
    /\ xHigh \in 0..(MaxValue \div 2)
    /\ xLow \in 0..1
    /\ y \in STRING
    /\ z \in SUBSET Pages
    /\ seq \in Seq(Nat)
    /\ rec \in [a: Nat, b: STRING]

\* ============================================================================
\* INITIALIZATION
\* ============================================================================

Init ==
    /\ xHigh = 0
    /\ xLow = 0
    /\ y = ""
    /\ z = {}
    /\ seq = <<>>
    /\ rec = [a |-> 0, b |-> "init"]

\* ============================================================================
\* ACTIONS (refined to match high-level behavior)
\* ============================================================================

IncrementX ==
    /\ x < MaxValue
    /\ IF xLow = 0
       THEN /\ xLow' = 1
            /\ UNCHANGED xHigh
       ELSE /\ xHigh' = xHigh + 1
            /\ xLow' = 0
    /\ UNCHANGED <<y, z, seq, rec>>

AppendToY ==
    /\ Len(y) < MaxValue
    /\ y' = y \o "a"
    /\ UNCHANGED <<xHigh, xLow, z, seq, rec>>

AddToZ ==
    /\ \E page \in Pages:
        /\ page \notin z
        /\ z' = z \union {page}
    /\ UNCHANGED <<xHigh, xLow, y, seq, rec>>

RemoveFromZ ==
    /\ z # {}
    /\ \E page \in z:
        z' = z \ {page}
    /\ UNCHANGED <<xHigh, xLow, y, seq, rec>>

AppendToSeq ==
    /\ Len(seq) < MaxValue
    /\ seq' = Append(seq, x)
    /\ UNCHANGED <<xHigh, xLow, y, z, rec>>

UpdateRecord ==
    /\ Len(y) > 0
    /\ rec' = [rec EXCEPT !.a = x, !.b = y]
    /\ UNCHANGED <<xHigh, xLow, y, z, seq>>

\* ============================================================================
\* NEXT STATE RELATION
\* ============================================================================

Next ==
    \/ IncrementX
    \/ AppendToY
    \/ AddToZ
    \/ RemoveFromZ
    \/ AppendToSeq
    \/ UpdateRecord

Spec == Init /\ [][Next]_<<xHigh, xLow, y, z, seq, rec>> /\ AbstractCheatSheet!Spec

====
