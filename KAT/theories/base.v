(*Require Import Plug.*)
Require Export List SetoidList Bool Setoid Program Recdef ZArith.
Require Export Sets SetProperties Generate SetConstructs.

Notation "[]" := (@nil _).

(* begin hide *)
Section ListExtra.
  
  Variable A : Type.
  
  Fixpoint list_pow (x:list A)(n:nat) := 
    match n with
      | O => nil
      | S n => app x (list_pow x n)
    end.

End ListExtra.
(** end hide *)

(** Usefull (and naive) tactics. *)

Ltac destruct2 G H :=
  destruct G;destruct H.

Ltac apply_comp G H I :=
  apply G in H ; apply H in I.

Ltac apply2 G H I :=
  apply G in H;apply G in I.

Ltac apply_mem G H :=
  let K := fresh in
    generalize H;intro K;
      apply G in H.

Ltac apply2_mem G H I :=
  apply_mem G H ; apply_mem G I.

Ltac inv H :=
  inversion H;subst;try congruence.

Ltac invc H :=
  inversion_clear H;try congruence.

(** * Definition of sets as characteristic predicates. *)
(** These definitions are verbatim copied from the library Ensembles. We copy the definitions here
in order to get rid of the annoying extraction warning about the axiom of set extensionality. *)

Section SetsProp.

  Variable U : Type.

  Definition Ensemble := U -> Prop.

  Definition In (A:Ensemble) (x:U) : Prop := A x.

  Definition Included (B C:Ensemble) : Prop := forall x:U, In B x -> In C x.

  Inductive Empty_set : Ensemble :=.

  Inductive Singleton (x:U) : Ensemble :=
    In_singleton : In (Singleton x) x.

  Inductive Union (B C:Ensemble) : Ensemble :=
    | Union_introl : forall x:U, In B x -> In (Union B C) x
    | Union_intror : forall x:U, In C x -> In (Union B C) x.

  Definition Same_set (B C:Ensemble) : Prop := Included B C /\ Included C B.

End SetsProp.

(** Some simplifications for Booleans. *)

Ltac simpl_bool :=
  match goal with
    | H: ?x || ?y = true  |- _ => apply orb_true_iff in H
    | H: ?x && ?y = true  |- _ => apply andb_true_iff in H
    | H: ?x || ?y = false |- _ => apply orb_false_iff in H
    | H: ?x && ?y = false |- _ => apply andb_false_iff in H
    | |- ?x || ?y = true  => apply orb_true_iff
    | |- ?x && ?y = true  => apply andb_true_iff
    | |- ?x || ?y = false => apply orb_false_iff
    | |- ?x && ?y = false =>apply andb_false_iff
  end.

Ltac simpl_bool_full := repeat simpl_bool.

Ltac autotc := auto with typeclass_instances.
      
