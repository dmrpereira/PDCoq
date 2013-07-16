Require Export language_proofs.

(*Generalizable All Variables.*)

(** * Proofs leading to the correctness of partial derivatives *)
(** The following proofs show that the properties of derivation match the one of left quotients. First we approach the [LQ] predicate. *)

Section LQPropertiesSimple.

  (** Left quotient of the empty language [\\0]. *)

  Lemma LQ_EmptyL : forall a, ∅ %Lq a ∼ ∅.
  Proof.
    split_eq;try (invc H);solve_empty.
  Qed.

  (** Left quotient of the epsilon language [\\1]. *)
  
  Lemma LQ_EpsL : forall a, {ε} %Lq a ∼ ∅.
  Proof.
    split_eq;[invc H;invc H0|solve_empty].
  Qed.

  (** Left quotient of the singleton language. These comprises two cases, one where the
   deriving symbol is the same as the one in the language, and also the contrary case.
 *)
    
  Lemma LQ_SyL_eq : forall a b:Z,  a === b -> {{a}} %Lq b ∼ {ε}.
  Proof.
    intros.
    rewrite H.
    split_eq;invc H0.
    inv H1;auto with lgs.
    econstructor;eauto with lgs.
  Qed.
  
  Lemma LQ_SyL_neq :  
    forall a b:Z, 
      a =/= b -> {{a}} %Lq b ∼ ∅.
  Proof.
    split_eq;invc H0.
    invc H1.
  Qed.
 
  (** Left quotient of the union of languages. *)
 
  Lemma LQ_union :
    forall l1 l2 a,
      (l1 ∪ l2) %Lq a ∼ (l1 %Lq a) ∪ (l2 %Lq a).
  Proof.
    split_eq;invc H;[
      invc H0;[left|right];constructor;auto |
        constructor;invc H0;left|constructor;invc H0;right];auto.
  Qed.

End LQPropertiesSimple.
        
Hint Resolve 
     @LQ_EmptyL 
     @LQ_EpsL 
     @LQ_SyL_eq 
     @LQ_SyL_neq
     @LQ_union : lgs.

Hint Rewrite
     @LQ_EmptyL 
     @LQ_EpsL 
     @LQ_SyL_eq 
     @LQ_SyL_neq
     @LQ_union : lgs.

Lemma LQ_star_l_plus_l_eq : 
  forall l a, 
    l∗ %Lq a ∼ l⁺ %Lq a.
Proof.
  split_eq;invc H;invc H0.
  induction n;simpl;intros;
    [inv H|constructor;constructor 1 with (n:=n);auto].
  induction n;econstructor;
  [(constructor 1 with (n:=1)) | constructor 1 with (n:=S (S n))];auto.
Qed.

Hint Resolve @LQ_star_l_plus_l_eq : lgs.

(** Extra properties about quotients involving concatenation. *)
Lemma LQ_conc_aux_1 :
  forall l1 l2 a,
    ~[] ∈ l1 -> (l1•l2) %Lq a ∼ (l1 %Lq a)•l2.
Proof.
  split_eq.
  inv H0;inv H1.
  pose proof (not_null_in_lconc _ _ _ _ _ _ H3 H4 H2 H) as H5;destruct H5 as [k H5].
  rewrite H5, <- app_comm_cons in H2;injection H2;intros;subst;constructor;auto with lgs.
  invc H0;inv H1;constructor;rewrite app_comm_cons;auto with lgs. 
Qed.

Lemma LQ_conc_aux_2 :
  forall l1 l2 a,
    [] ∈ l1 -> (l1•l2) %Lq a ∼ ((l1 %Lq a)•l2) ∪ (l2 %Lq a).
Proof.
  split_eq.
  inv H0;inv H1.
  destruct(eq_dec w1 []) as [H5|H5].
  inv H5;simpl in H2;right;constructor;rewrite <- H2;autotc.
  pose proof (not_null_in_lconc_2 _ _ _ _ _ _ H3 H4 H2 H5) as H6;destruct H6 as [k H6];subst.
  rewrite <- app_comm_cons in H2;injection H2;intros;subst;constructor;auto with lgs.
  destruct H0. 
  inversion H0;inversion H1;subst;constructor;rewrite app_comm_cons;constructor;auto with lgs.
  inv H0;constructor;change (a :: x) with ([]++(a :: x))%list;auto with lgs. 
Qed.

(** * Left-quotients of languages w.r.t. words *)

Section LQwProperties.

  Lemma LQw_nil : 
    forall l, 
      l %Lqw [] ∼ l.
  Proof.
    split_eq;[inv H|econstructor];auto.
  Qed.

  Lemma LQw_sy_LQ_eq : 
    forall l a, 
      l %Lqw [a] ∼ l %Lq a.
  Proof.
    split_eq;inv H;econstructor;auto.
  Qed.

  Instance In_L_m : Proper(leq ==> eq ==> iff) (In word).
  Proof.
    repeat red;intros;subst;split_eq;auto.
  Qed.

  Lemma LQw_LQ_cons : 
    forall l a w,
      l %Lqw (a::w) ∼ (l %Lq a) %Lqw w.
  Proof.
    induction w.
    rewrite LQw_nil;rewrite LQw_sy_LQ_eq;auto.

    inversion_clear IHw.
    do 2 econstructor;inv H1;auto with lgs.

    inv H1;inv H2;auto.
  Qed.

  Lemma LQw_split : 
    forall l w1 w2,
      l %Lqw (w1++w2)%list ∼ (l %Lqw w1) %Lqw w2.
  Proof.
    intro l;induction w1;simpl;intros.
    rewrite LQw_nil;auto.

    split_eq;inv H;repeat constructor.
    rewrite <- app_ass;auto.
    invc H0; rewrite <- app_ass in H1;auto.
  Qed.

  Lemma LQw_EmptyL : forall w, LQw ∅ w ∼ ∅.
  Proof.
    split_eq;[invc H;invc H0|inv H].
  Qed.

  Inductive SigmaPlus : language :=
  | in_sp_sy : forall a, [a] ∈ SigmaPlus
  | in_sp_sy_ins : forall w, w ∈ SigmaPlus -> forall a, (a::w) ∈ SigmaPlus.
    
  Notation "{Sig+}" := SigmaPlus.

  Local Hint Constructors SigmaPlus.

  Lemma LQw_EpsL : forall w, (w ∈ {Sig+}) -> {ε} %Lqw w ∼ ∅.
  Proof.
    intros w;induction 1;split_eq;invc H;inv H0;inv H.
  Qed.

  Lemma LQw_SyL_sy_eq : forall a , {{a}} %Lqw [a] ∼ {ε}.
  Proof.
    split_eq;invc H;[invc H0|constructor;simpl];auto with lgs.
  Qed.

  Lemma LQw_SyL_sy_neq : forall w a, w ∈ {Sig+} -> w <> [a] -> LQw {{a}} w ∼ ∅.
  Proof.
    intros w a.
    induction 1;intros;split_eq.
    invc H0;invc H1.
    inv H0.
    invc H1;inv H2. 
    symmetry in H4;apply app_eq_nil in H4;destruct H4;subst.
    invc H2.
    inv H1.
  Qed.

  Lemma LQw_union_l : 
    forall l1 l2 w,
      w ∈ {Sig+} -> (l1 ∪ l2) %Lqw w ∼ (l1 %Lqw w) ∪ (l2 %Lqw w).
  Proof.
    intros l1 l2 w;induction 1;split_eq.
    invc H;invc H0;[left|right];auto with lgs.
    constructor;invc H;inv H0;solve_trivial_union.
    invc H0;invc H1;[left|right];auto with lgs.
    constructor;invc H0;invc H1;solve_trivial_union.
  Qed.
  
End LQwProperties.

Hint Resolve
  LQw_SyL_sy_eq
  LQw_SyL_sy_neq
  LQw_EmptyL
  LQw_split 
  LQw_sy_LQ_eq : lgs.

(**  Words as members of partial derivatives w.r.t words *)

Lemma w_in_Lang_eq_nil_in_LQw : 
  forall w l,
    w ∈ l -> [] ∈ LQw l w.
Proof.
  intros;constructor;rewrite <- app_nil_end;auto.
Qed.

Lemma nil_in_LQw_eq_w_in_lang : 
  forall w l,
    [] ∈ LQw l w -> w ∈ l.
Proof.
  intros;invc H;rewrite app_nil_end;auto.
Qed.

  (** Language of the derivative w.r.t all words *)
  (*Inductive LQwAll : language -> language := *)
(*   | in_lqwall : forall w w' l, w' ∈ (l %Lqw w) -> w' ∈ (LQwAll l).*)

