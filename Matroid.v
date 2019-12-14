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

Definition Circuits (M : Matroid) : Ensemble (Ensemble U) :=
(fun S : Ensemble U =>(~ I M S) /\(forall T : Ensemble U,
Strict_Included U T S -> I M T)).

(*The following are Circuit principles *)
Definition C1 : Ensemble (Ensemble U) -> Prop :=
(fun C => ~ C (Empty_set U)).

Definition C2 : Ensemble (Ensemble U) -> Prop :=
(fun C => forall (A B : Ensemble U),
(C A) /\ (C B) /\ Included U A B -> Same_set U A B).

Definition C3 : Ensemble (Ensemble U) -> Prop :=
(fun C => forall (A B : Ensemble U), forall (e : U),
(C A) /\ (C B) /\ (~ Same_set U A B) /\
(In U (Intersection U A B) e) ->
exists C3 : Ensemble U,
(C C3) /\
Included U C3 (Setminus U (Union U A B) (Singleton U e))).

Lemma Circuits_Satisfy_C1 : forall M : Matroid, C1 (Circuits M).
Proof.
  unfold C1.
  intros.
  intro.
  unfold Circuits in H.
  destruct H.
  contradict H.
  apply M1.
Qed.

Lemma Circuits_Satisfy_C2 : forall M : Matroid, C2 (Circuits M).
Proof.
  unfold C2.
  intros.
  destruct H as [C_A [C_B A_sub_B]].
  assert (G: A = B \/ A <> B). apply classic.
  destruct G.
  apply (Extension U); assumption.
  unfold Circuits in C_A.
  unfold Circuits in C_B.
  unfold Strict_Included in C_A.
  unfold Strict_Included in C_B.
  destruct C_A as [A_not_I A_prop_subs_I].
  destruct C_B as [B_not_I B_prop_subs_I].
  assert (G: Included U A B /\ A <> B -> I M A).
  apply B_prop_subs_I.
  contradict A_not_I.
  auto.
Qed.
