---- MODULE CheatSheet ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Users, Pages, MaxValue
VARIABLE x, y, z, seq, rec

\* ============================================================================
\* TYPE INVARIANT
\* ============================================================================

TypeOK ==
    /\ x \in 0..MaxValue
    /\ y \in STRING
    /\ z \in SUBSET Pages
    /\ seq \in Seq(Nat)
    /\ rec \in [a: Nat, b: STRING]

\* ============================================================================
\* EXAMPLE INVARIANTS
\* ============================================================================

\* Quantifier examples
AllPagesInZ == \A page \in Pages: page \in z
ExistsPagesInZ == \E page \in Pages: page \in z

\* Implication example
AllPageImpliesExists == (~AllPagesInZ) \/ ExistsPagesInZ

\* Record field constraints
RecordOK == rec.a <= MaxValue /\ (Len(rec.b) > 0 \/ rec.b = "init")

\* Sequence constraints
SeqNonEmpty == Len(seq) > 0
SeqOrdered == \A i \in 1..(Len(seq)-1): seq[i] <= seq[i+1]
SeqNonEmptyOrEmpty == SeqNonEmpty \/ Len(seq) = 0

\* ============================================================================
\* INITIALIZATION
\* ============================================================================

Init ==
    /\ x = 0
    /\ y = ""
    /\ z = {}
    /\ seq = <<>>
    /\ rec = [a |-> 0, b |-> "init"]

\* ============================================================================
\* ACTIONS
\* ============================================================================

IncrementX ==
    /\ x < MaxValue
    /\ x' = x + 1
    /\ UNCHANGED <<y, z, seq, rec>>

AppendToY ==
    /\ Len(y) < MaxValue
    /\ y' = y \o "a"
    /\ UNCHANGED <<x, z, seq, rec>>

AddToZ ==
    /\ \E page \in Pages:
        /\ page \notin z
        /\ z' = z \union {page}
    /\ UNCHANGED <<x, y, seq, rec>>

RemoveFromZ ==
    /\ z # {}
    /\ \E page \in z:
        z' = z \ {page}
    /\ UNCHANGED <<x, y, seq, rec>>

AppendToSeq ==
    /\ Len(seq) < MaxValue
    /\ seq' = Append(seq, x)
    /\ UNCHANGED <<x, y, z, rec>>

UpdateRecord ==
    /\ Len(y) > 0
    /\ rec' = [rec EXCEPT !.a = x, !.b = y]
    /\ UNCHANGED <<x, y, z, seq>>

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

Spec == Init /\ [][Next]_<<x, y, z, seq, rec>>

\* ============================================================================
\* PROPERTIES TO CHECK
\* ============================================================================

\* Liveness: x eventually reaches MaxValue (won't hold with finite depth)
EventuallyMaxX == <>(x = MaxValue)

\* Liveness: z eventually contains all pages (won't hold with finite depth)
EventuallyAllPages == <>(z = Pages)

\* ============================================================================
\* THEOREMS AND PROOFS
\* ============================================================================

THEOREM InitValid == Init => TypeOK
PROOF
  <1>1 ASSUME Init PROVE x \in 0..MaxValue BY DEF Init
  <1>2 ASSUME Init PROVE y \in STRING BY DEF Init
  <1>3 ASSUME Init PROVE z \in SUBSET Pages BY DEF Init
  <1>4 ASSUME Init PROVE seq \in Seq(Nat) BY DEF Init
  <1>5 ASSUME Init PROVE rec \in [a: Nat, b: STRING] BY DEF Init
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF TypeOK

THEOREM NextPreservesTypeOK == TypeOK /\ Next => TypeOK'
PROOF
  <1> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' BY DEF Next
  <1>1 CASE IncrementX
    <2>1 x' < MaxValue \/ x' = MaxValue BY <1>1 DEF IncrementX
    <2>2 x' \in 0..MaxValue BY <2>1 DEF IncrementX, TypeOK
    <2>3 y' \in STRING BY <1>1 DEF IncrementX
    <2>4 z' \in SUBSET Pages BY <1>1 DEF IncrementX
    <2>5 seq' \in Seq(Nat) BY <1>1 DEF IncrementX
    <2>6 rec' \in [a: Nat, b: STRING] BY <1>1 DEF IncrementX
    <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
  <1>2 CASE AppendToY
    <2>1 x' \in 0..MaxValue BY <1>2 DEF AppendToY
    <2>2 y' \in STRING BY <1>2 DEF AppendToY
    <2>3 z' \in SUBSET Pages BY <1>2 DEF AppendToY
    <2>4 seq' \in Seq(Nat) BY <1>2 DEF AppendToY
    <2>5 rec' \in [a: Nat, b: STRING] BY <1>2 DEF AppendToY
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
  <1>3 CASE AddToZ
    <2>1 x' \in 0..MaxValue BY <1>3 DEF AddToZ
    <2>2 y' \in STRING BY <1>3 DEF AddToZ
    <2>3 z' \in SUBSET Pages BY <1>3 DEF AddToZ
    <2>4 seq' \in Seq(Nat) BY <1>3 DEF AddToZ
    <2>5 rec' \in [a: Nat, b: STRING] BY <1>3 DEF AddToZ
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
  <1>4 CASE RemoveFromZ
    <2>1 x' \in 0..MaxValue BY <1>4 DEF RemoveFromZ
    <2>2 y' \in STRING BY <1>4 DEF RemoveFromZ
    <2>3 z' \in SUBSET Pages BY <1>4 DEF RemoveFromZ
    <2>4 seq' \in Seq(Nat) BY <1>4 DEF RemoveFromZ
    <2>5 rec' \in [a: Nat, b: STRING] BY <1>4 DEF RemoveFromZ
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
  <1>5 CASE AppendToSeq
    <2>1 x' \in 0..MaxValue BY <1>5 DEF AppendToSeq
    <2>2 y' \in STRING BY <1>5 DEF AppendToSeq
    <2>3 z' \in SUBSET Pages BY <1>5 DEF AppendToSeq
    <2>4 seq' \in Seq(Nat) BY <1>5 DEF AppendToSeq
    <2>5 rec' \in [a: Nat, b: STRING] BY <1>5 DEF AppendToSeq
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
  <1>6 CASE UpdateRecord
    <2>1 x' \in 0..MaxValue BY <1>6 DEF UpdateRecord
    <2>2 y' \in STRING BY <1>6 DEF UpdateRecord
    <2>3 z' \in SUBSET Pages BY <1>6 DEF UpdateRecord
    <2>4 seq' \in Seq(Nat) BY <1>6 DEF UpdateRecord
    <2>5 rec' \in [a: Nat, b: STRING] BY <1>6 DEF UpdateRecord
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF TypeOK
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

====
