Require Import Coq.FSets.FSetList.
Require Import Coq.FSets.FSetProperties.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Omega.
Module subset (M : FSetInterface.S).
  Module nestedSet := FSetList.Make(M).
  (* From what I understand the above defines nestedSets as being finite sets
     of any kind of FSet...*)
Module P :=
Definition I1 (I : nestedSet.t) := nestedSet.In M.empty I.
Definition I2 (I : nestedSet.t) := forall A B, M.Subset A B -> nestedSet.In B I -> nestedSet.In A I.
Definition I3 (I : nestedSet.t) := forall A B n m, nestedSet.In A I -> nestedSet.In B I -> M.cardinal A = n -> M.cardinal B = m -> m > n -> exists x : M.elt, M.In x (M.diff B A)  /\ nestedSet.In (M.add x A) I.

(* From the above you can sort of get a sense of how this works. The finite sets
 and nested sets have a whole different set of functions and properties, so you have to change scopes a lot. .t gives you a set of that type and .elt gives you the type of element that goes in that set. *)

Record Matroid : Type :=
  {I : nestedSet.t;
   M1 : I1 I;
   M2 : I2 I;
   M3 : I3 I;
  }.

Definition Maximal (I : nestedSet.t) (A : M.t) :=
  forall S, M.Subset A S -> ~M.Equal A S -> ~(nestedSet.In S I).

Definition I3' (I : nestedSet.t) :=
  forall A B n m, nestedSet.In A I -> nestedSet.In B I -> Maximal I A -> Maximal I B -> M.cardinal A = n -> M.cardinal B = m -> n = m.


Theorem I3_iff_I3' : forall I, I3 I <-> I3' I.
Proof.
  Admitted.
