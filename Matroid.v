Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Constructive_sets.
Require Export Coq.Sets.Finite_sets.
Require Export Coq.Sets.Finite_sets_facts.
Require Export Coq.Bool.Bool.

Parameter U : Type.
Parameter G : Ensemble U.
Parameter finite : Finite U G.

(* The following define the independence axioms. *)

Definition I1 (I : Ensemble (Ensemble U)) :=
  I (Empty_set U).

Definition I2 (I : Ensemble (Ensemble U)) :=
  forall A B, Included U A B -> I B -> I A.

Definition I3 (I : Ensemble (Ensemble U)) :=
  forall A B n m, I A -> I B -> cardinal U A n -> cardinal U B m -> m > n ->  exists x : U, Setminus U B A x /\ I (Add U A x).

Record Matroid : Type :=
  { I : Ensemble (Ensemble U);
    M1 : I1 I;
    M2 : I2 I;
    M3 : I3 I
  }.


(** Here I will define the notion of maximality for an independent set. A set is independent if the addition of any additional elements causes the set **
to cease being independent. *)
Definition Maximal (I : Ensemble (Ensemble U)) (A : Ensemble U) :=
  forall S, Strict_Included U A S -> ~(I S).

Definition I3' (I : Ensemble (Ensemble U)) :=
  forall A B n m, Maximal I A -> Maximal I B -> cardinal U A n -> cardinal U B m -> n = m.

Theorem I3_iff_I3' : forall I, I3 I <-> I3' I.
Proof.
  Admitted.

Definition Base (M : Matroid) (B : Ensemble U) :=
  Maximal (I M) B /\ (I M) B.

Theorem Bases_Same_Size : forall A B (M : Matroid) n m, Base M A -> Base M B -> cardinal U A n -> cardinal U B m -> n = m.
Proof.
  intros. unfold Base in H. unfold Base in H0. destruct H. destruct H0. destruct M. simpl in *. apply I3_iff_I3' in M6. unfold I3' in M6. eapply M6. apply H. apply H0. apply H1. apply H2.
  Qed.
