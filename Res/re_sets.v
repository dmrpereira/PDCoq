Require Export reg_expr.

(** Some more tactics : to move to base.v *)
Ltac absinv H := abstract(inv H).
Ltac habsinv H x := abstract(inv H;auto with x).
Ltac absinvc H := abstract(invc H).
Ltac habsinvc H x := abstract(invc H;auto with x).

Inductive re_eq : re -> re -> Prop :=
  re_eq_re0 : 
    re_eq 0 0
| re_eq_re1 : 
    re_eq 1 1
| re_eq_re_sy : 
    forall x1 y1 : Z,
      x1 === y1 -> re_eq (\!x1) (\!y1)
| re_eq_re_union : 
    forall x1 y1 x2 y2 : re, 
      re_eq x1 y1 -> re_eq x2 y2 -> re_eq (x1 + x2) (y1 + y2)
| re_eq_re_conc : 
    forall x1 y1 x2 y2 : re,
      re_eq x1 y1 -> re_eq x2 y2 -> re_eq (x1 · x2) (y1 · y2)
| re_eq_re_star : 
    forall x1 y1 : re, 
      re_eq x1 y1 -> re_eq (x1 ⋆) (y1 ⋆).

Property re_leibniz : 
  forall r1 r2, re_eq r1 r2 -> r1 = r2.
Proof.
  induction 1;auto;subst;(absinv H||auto).
Qed.

Inductive re_lt : re -> re -> Prop :=
| re_lt_re0_re1 : 
    re_lt 0 1
| re_lt_re0_re_sy : 
    forall y1 : Z, re_lt 0 (\!y1)
| re_lt_re0_re_union : 
    forall y1 y2 : re, re_lt 0 (y1 + y2)
| re_lt_re0_re_conc : 
    forall y1 y2 : re, re_lt 0 (y1 · y2)
| re_lt_re0_re_star : 
    forall y1 : re, re_lt 0 (y1 ⋆)
| re_lt_re1_re_sy : 
    forall y1 : Z, re_lt 1 (\!y1)
| re_lt_re1_re_union : 
    forall y1 y2 : re, re_lt 1 (y1 + y2)
| re_lt_re1_re_conc : 
    forall y1 y2 : re, re_lt 1 (y1 · y2)
| re_lt_re1_re_star : 
    forall y1 : re, re_lt 1 (y1⋆)
| re_lt_re_sy_1 : 
    forall x1 y1 : Z, x1 <<< y1 -> re_lt (\!x1) (\!y1)
| re_lt_re_sy_re_union : 
    forall (x1 : Z) (y1 y2 : re), re_lt (\!x1) (y1 + y2)
| re_lt_re_sy_re_conc : 
    forall (x1 : Z) (y1 y2 : re), re_lt (\!x1) (y1 · y2)
| re_lt_re_sy_re_star : 
    forall (x1 : Z) (y1 : re), re_lt (\!x1) (y1⋆)
| re_lt_re_union_1 : 
    forall x1 y1 x2 y2 : re, 
      re_lt x1 y1 -> re_lt (x1+x2) (y1+y2)
| re_lt_re_union_2 : 
    forall x1 y1 x2 y2 : re, 
      re_eq x1 y1 ->  re_lt x2 y2 -> re_lt (x1+x2) (y1+y2)
| re_lt_re_union_re_conc : 
    forall x1 x2 y1 y2 : re, re_lt (x1+x2) (y1·y2)
| re_lt_re_union_re_star :
    forall x1 x2 y1 : re, re_lt (x1+x2) (y1⋆)
| re_lt_re_conc_1 : 
    forall x1 y1 x2 y2 : re, 
      re_lt x1 y1 -> re_lt (x1·x2) (y1·y2)
| re_lt_re_conc_2 : 
    forall x1 y1 x2 y2 : re, 
      re_eq x1 y1 -> re_lt x2 y2 -> re_lt (x1 · x2) (y1 · y2)
  | re_lt_re_conc_re_star : 
    forall x1 x2 y1 : re, re_lt (x1·x2) (y1⋆)
  | re_lt_re_star_1 : 
    forall x1 y1:re, re_lt x1 y1 -> re_lt (x1⋆) (y1⋆).

Hint Constructors re_lt re_eq : res.

Definition re_cmp := fix re_cmp (x y : re) : comparison :=
match x with
  | 0 =>
      match y with
      | re0 => Eq
      | _ => Lt
      end
  | re1 =>
      match y with
      | re0 => Gt
      | re1 => Eq
      | _ => Lt
      end
  | \!x1 =>
      match y with
      | re0 => Gt
      | re1 => Gt
      | \!y1 => compare x1 y1
      | _ => Lt
      end
  | x1 + x2 =>
      match y with
      | re0 => Gt
      | re1 => Gt
      | \!_ => Gt
      | y1 + y2 =>
          match re_cmp x1 y1 with
          | Eq => re_cmp x2 y2
          | Lt => Lt
          | Gt => Gt
          end
      | _ => Lt
      end
  | x1 · x2 =>
      match y with
      | y1 · y2 =>
          match re_cmp x1 y1 with
          | Eq => re_cmp x2 y2
          | Lt => Lt
          | Gt => Gt
          end
      | _ ⋆ => Lt
      | _ => Gt
      end
  | x1 ⋆ =>
      match y with
      | y1 ⋆ => re_cmp x1 y1
      | _ => Gt
      end
end.

Functional Scheme re_cmp_ind := Induction for re_cmp Sort Prop.

Global Instance re_eq_sym : Symmetric re_eq.
Proof.
  repeat red;induction 1;constructor;try (symmetry;auto);try assumption.
Qed.

Global Instance re_eq_trans : Transitive re_eq.
Proof.
  repeat red.
  induction x;intros;try absinv H;
  try now(abstract(inv H;inv H0;constructor;[apply IHx1 with y1|apply IHx2 with y2];auto)).
  abstract(inv H;inv H0;constructor;eapply IHx with y1;auto).
Qed.

Global Instance re_eq_equiv : Equivalence re_eq.
Proof.
  econstructor;auto with typeclass_instances.
  red;induction x;constructor;auto.
Qed.

Property re_cmp_eq_re_eq : forall r1 r2, re_cmp r1 r2 = Eq -> re_eq r1 r2.
Proof.
  intros.
  functional induction (re_cmp r1 r2);try congruence;auto with res.
  constructor. apply compare_2 in H. auto.
Qed.

Property re_cmp_lt_re_lt : forall r1 r2, re_cmp r1 r2 = Lt -> re_lt r1 r2.
Proof.
  intros.
  functional induction (re_cmp r1 r2);try congruence;auto with res.
  apply re_lt_re_union_2;auto. apply re_cmp_eq_re_eq  in e1. auto.
  apply re_lt_re_conc_2;auto. apply re_cmp_eq_re_eq  in e1. auto.
Qed.

Property re_cmp_gt_re_gt : forall r1 r2, re_cmp r1 r2 = Gt -> re_lt r2 r1.
Proof.
  intros.
  functional induction (re_cmp r1 r2);try congruence;auto with res.
  apply re_lt_re_sy_1. apply compare_3 in H. auto.
  apply re_lt_re_union_2;auto. apply re_cmp_eq_re_eq  in e1. symmetry. auto.
  apply re_lt_re_conc_2;auto. apply re_cmp_eq_re_eq  in e1. symmetry. auto.
Qed.

Property re_eq_re_cmp_eq : forall r1 r2, re_eq r1 r2 -> re_cmp r1 r2 = Eq.
Proof.
  induction 1;simpl;auto.
  rewrite H. apply elim_compare_eq;order.
  rewrite IHre_eq1,IHre_eq2;auto.
  rewrite IHre_eq1,IHre_eq2;auto.
Qed.

Property re_eq_symm :
  forall r1 r2, re_cmp r1 r2 = Eq -> re_cmp r2 r1 = Eq.
Proof.
  intros.
  functional induction (re_cmp r1 r2);try congruence;auto with res.
  apply compare_2 in H. apply re_eq_re_cmp_eq. rewrite H. constructor. reflexivity.
  apply re_cmp_eq_re_eq in e1. apply re_cmp_eq_re_eq in H. apply re_eq_re_cmp_eq .
  constructor; symmetry; auto.
  apply re_cmp_eq_re_eq in e1. apply re_cmp_eq_re_eq in H. apply re_eq_re_cmp_eq .
  constructor; symmetry; auto.
Qed.

Global Instance re_lt_trans : Transitive re_lt.
Proof.
  repeat red;intros x y z; revert z y x;induction z ; intros;
  repeat  match goal with 
            | H : re_lt _ 0 |- _ => inv H
            | H : re_lt _ 1 |- _ => inv H;auto with res
            | H : re_lt _ (\!_) |- _ => inv H;first [constructor;order||auto with res]
            | _ => idtac
          end.

  inv H0;[absinv H|habsinv H res|]. inv H;auto with res. constructor;order.

  inv H0;try (absinv H);try (habsinv H res). inv H;auto with res. constructor.
  apply IHz1 with x1;auto. apply re_lt_re_union_1. apply re_leibniz in H5;subst;auto.
  inv H;auto with res. constructor. apply re_leibniz in H4;subst;auto.
  apply re_leibniz in H4;subst;auto. apply re_lt_re_union_2;auto.
  apply IHz2 with x2;auto. 
  
  inv H0;try (absinv H);try (habsinv H res). inv H;auto with res. constructor.
  apply IHz1 with x1;auto. apply re_lt_re_conc_1. apply re_leibniz in H5;subst;auto.
  inv H;auto with res. constructor. apply re_leibniz in H4;subst;auto.
  apply re_leibniz in H4;subst;auto. apply re_lt_re_conc_2;auto.
  apply IHz2 with x2;auto.

  inv H0;try (absinv H);try (habsinv H res). inv H;auto with res. inv H;auto with res. 
  constructor. apply IHz with x1;auto.
Qed.

Global Program Instance re_ord: OrderedType re := 
  { _eq := re_eq ; _lt := re_lt ; _cmp := re_cmp }.
Next Obligation.
  constructor;auto with typeclass_instances.
  intros;intro.
  induction H;inv H0.
  order.
  normalize_notations.
  elim (IHre_lt H4).
  normalize_notations.
  elim (IHre_lt H7).
  elim (IHre_lt H4).
  elim (IHre_lt H7).
  elim (IHre_lt H3).
Qed.
Next Obligation.
  functional induction (re_cmp x y);try now(constructor);auto with res.
  case_eq(compare x1 y1);intros;constructor.
  apply compare_2 in H;auto with res.
  apply compare_1 in H;auto with res.
  apply compare_3 in H;auto with res.
  inv IHc0.
  apply re_cmp_eq_re_eq in e1.
  constructor.
  apply re_lt_re_union_2;auto.
  apply re_cmp_eq_re_eq in e1.  constructor.
  constructor;auto.
  symmetry in H. constructor. apply re_cmp_eq_re_eq in e1. apply re_cmp_gt_re_gt in H. 
  apply re_lt_re_union_2;auto. symmetry. auto.
  constructor. constructor. apply re_cmp_lt_re_lt in e1. assumption.
  constructor. apply re_cmp_gt_re_gt in e1. apply re_lt_re_union_1;auto. 
  inv IHc0.
  symmetry in H. apply re_cmp_lt_re_lt in H. apply re_cmp_eq_re_eq in e1. constructor.
  apply re_lt_re_conc_2;auto.
  symmetry in H.  apply re_cmp_eq_re_eq in e1. constructor. constructor;auto. 
  symmetry in H. apply re_cmp_eq_re_eq in e1. apply re_cmp_gt_re_gt in H. constructor.
  apply re_lt_re_conc_2;auto. symmetry;auto.
  constructor. constructor. apply re_cmp_lt_re_lt in e1. assumption.
  apply re_cmp_gt_re_gt in e1. constructor. constructor;auto.
  invc IHc.
  constructor. constructor. assumption.
  constructor. constructor. assumption.
  constructor. constructor. assumption.
Qed.

Typeclasses Opaque re_ord.

Global Program Instance re_UsualOT : UsualOrderedType re := 
         { SOT_lt := re_lt  ;
           SOT_cmp := re_cmp }.
Next Obligation.
  constructor.
  red;apply re_lt_trans.
  intros.
  red.
  intro.
  inversion H0.
  normalize_notations.
  rewrite H1 in H.
  generalize(@lt_antirefl re _ _ _ _ y);intro.
  contradiction.
Qed.
Next Obligation.
  reverse.
  induction x;destruct y;simpl;
    (try (now (constructor 1;auto;constructor)));
    (try (now (constructor 2;constructor)));
    (try (now (constructor 3;constructor))).
  case_eq(compare z z0);intro.
  apply compare_2 in H.
  constructor;auto.
  inversion_clear H.
  reflexivity.
  apply compare_1 in H;constructor;
    normalize_notations;constructor;auto.
  apply compare_3 in H.
  constructor;normalize_notations.
  constructor;auto.
  destruct(IHx1 y1).
  constructor.
  normalize_notations.
  constructor;auto.
  destruct(IHx2 y2).
  rewrite H.
  constructor.
  apply re_lt_re_union_2;auto.
  normalize_notations.
  reflexivity.
  rewrite H,H0;constructor;auto.
  constructor.
  apply re_lt_re_union_2;auto.
  normalize_notations.
  rewrite H;auto.
  constructor 3.
  constructor;auto.
  
  destruct(IHx1 y1).
  constructor.
  normalize_notations.
  constructor;auto.
  destruct(IHx2 y2).
  constructor.
  rewrite H.
  apply re_lt_re_conc_2;
    normalize_notations;auto.
  repeat constructor;subst;auto.
  constructor 3.
  apply re_lt_re_conc_2;subst;auto.
  normalize_notations;auto.
  constructor.
  constructor;auto.
  
  destruct(IHx y);constructor.
  constructor;auto.
  rewrite H;auto.
  constructor;auto.
Qed.

Typeclasses Opaque re_UsualOT.

Hint Resolve re_leibniz : res.
  
Lemma compat_bool_true : forall f:re->bool, compat_bool Logic.eq f.
Proof.
  intros;repeat red;intros;subst;auto.
Qed.

(** * Some useful, but simple, set properties not existing in the
     FSets Coq library *)
Open Scope set_scope.

Lemma reset_union_empty : forall s:set re, union s empty === s.
Proof.
  split_eq.
  apply union_1 in H;destruct H;auto.
  inversion H.
  apply union_2;assumption.
Qed.

(** Filter empty *)
Close Scope list_scope.
Lemma reset_filter_empty : forall f:re->bool, filter f empty === empty.
Proof.
  intros.
  split_eq.
  apply filter_1 in H.
  inversion H.
  vm_compute in H.
  inversion H.
  inversion H.
Qed.

Hint Rewrite 
  reset_union_empty
  reset_filter_empty : res.

Program Instance filter_bool_proper : forall f:re->bool, Proper (_eq ==> eq) f.
Next Obligation.
  red.
  intros.
  apply f_equal.
  revert x y H.
  induction x;destruct y;try reflexivity;intros;
    try solve [inversion H].
  inversion_clear H.
  rewrite H0;reflexivity.
  inversion_clear H.
  apply IHx1 in H0;apply IHx2 in H1.
  rewrite H0,H1.
  reflexivity.
  inversion_clear H.
  apply IHx1 in H0;apply IHx2 in H1.
  rewrite H0,H1.
  reflexivity.
  inversion_clear H.
  apply IHx in H0.
  rewrite H0;reflexivity.
Qed.

(** Filter singleton *)
Lemma reset_filter_subset : forall (f:re->bool) s, filter f s [<=] s.
Proof.
  intros.
  red;intros.
  apply filter_1 in H;auto with typeclass_instances;intros.
Qed.

(** Filter add *)
Lemma reset_filter_add : forall s x (f:re->bool), 
  filter f {x;s} === if f x then {x}%set ++ (filter f s) else filter f s.
Proof.
  intros.
  split_eq.
  apply filter_iff in H;auto with typeclass_instances.
  destruct H.
  apply add_iff in H.
  destruct H.
  rewrite <- H in H0.
  rewrite H0.
  rewrite H.
  apply union_2.
  apply singleton_2.
  reflexivity.
  eapply (filter_3 H) in H0.
  case_eq (f x);intros.
  apply union_3;auto.
  assumption.
  
  case_eq(f x);intros;rewrite H0 in H.
  apply union_1 in H.
  destruct H.
  apply singleton_1 in H;subst.
  apply filter_3;auto with typeclass_instances.
  rewrite H.
  apply add_iff.
  left;reflexivity.
  rewrite H in H0;assumption.
  
  generalize H;intros.
  apply filter_1 in H1;auto with typeclass_instances.
  apply filter_2 in H;auto with typeclass_instances.
  apply filter_3;auto with typeclass_instances.
  apply add_iff;auto.
  apply filter_iff in H;auto with typeclass_instances.
  destruct H.
  apply filter_iff;auto with typeclass_instances.
  split;auto.
  apply add_iff;auto.
Qed.

Lemma reset_filter_non_empty_ex : forall s1 s2:set re, ~((inter s1 s2)==={}) -> 
  exists z, z \In s1 /\ z \In s2.
Proof.
  induction s1 using set_induction;intros.
  apply empty_inter_1 with (s':=s2) in H.
  apply empty_is_empty_1 in H.
  rewrite H in H0.
  elim H0;reflexivity.
  
  apply Add_Equal in H0.
  rewrite H0 in H1.
  destruct(In_dec x s2).
  
  exists x.
  split;auto.
  rewrite H0.
  apply add_1.
  reflexivity.
  
  rewrite inter_add_2 in H1;auto.
  apply IHs1_1 in H1.
  do 2 destruct H1.
  exists x0.
  split.
  rewrite H0.
  apply add_2.
  assumption.
  assumption.
Qed.

Lemma reset_filter_ex_non_empty : forall s1 s2:set re, 
  (exists z, z \In s1 /\ z \In s2) -> ~(inter s1 s2 === {}).
Proof.
  induction s1 using set_induction;simpl;intros.
  destruct H0.
  destruct H0.
  elim (H x).
  assumption.
  
  apply Add_Equal in H0.
  destruct(In_dec x s2).
  rewrite H0.
  rewrite inter_add_1;auto.
  intro.
  destruct (H2 x).
  assert(x \In {x;(inter s1_1 s2)}).
  apply add_1.
  reflexivity.
  apply H3 in H5.
  inversion H5.
  
  rewrite H0.
  rewrite inter_add_2;auto.
  apply IHs1_1.
  do 2 destruct H1.
  exists x0.
  rewrite H0 in H1.
  apply add_iff in H1.
  destruct H1.
  rewrite<- H1 in H2.
  contradiction.
  split;auto.
Qed.

Inductive SreL : set re -> language :=
| in_sre_lang : forall s w r, r \In s -> w ∈ (re2rel r) -> w ∈ (SreL s).

Notation "L[ s ]" := (SreL s)(at level 0).

Definition SreLf (x:set re) : language :=
  fold (fun a => union_l (re2rel a)) x 0.

Notation "L'[ s ]" := (SreLf s)(at level 0).

Instance re2rel_m_eq : Proper (_eq ==> leq) (fun a => re2rel a).
Proof.
  repeat red.
  intros.
  apply re2rel_m.
  red in H;simpl in H.
  induction H;auto.
  rewrite H.
  reflexivity.
  rewrite IHre_eq1,IHre_eq2.
  reflexivity.
  rewrite IHre_eq1,IHre_eq2.
  reflexivity.
  rewrite IHre_eq;reflexivity.
Defined.

Instance union_l_f_proper : 
  Proper (_eq ==> leq ==> leq) (fun a : re => union_l a).
Proof.
  repeat red;intros.
  apply re2rel_m_eq in H;
    split;red;intros x1 H1;
      destruct H1;
        (apply H in H1||apply H0 in H1);
        solve [left;auto|right;auto].
Qed.

Lemma union_l_f_transpose : transpose leq (fun a : re => union_l a).
Proof.
  repeat red;intros;
    unfold Included;split;intros;auto. 
  inversion_clear H.
  constructor 2;left;auto.
  destruct H0.
  left;auto.
  right;right;auto.
  destruct H.
  right;left;auto.
  destruct H.
  left;auto.
  right;right;auto.
Qed.

Add Morphism SreLf : SreLf_m.
Proof.
  induction x using set_induction;intros;
    split;red;intros.
  unfold SreLf in H1.
  rewrite fold_1b in H1;auto.
  inversion H1.
  assert(Empty y).
  rewrite <- H0;assumption.
  
  unfold SreLf in H1.
  rewrite fold_1b in H1;auto.
  inversion_clear H1.
  unfold SreLf in H2 |- *.
  assert(x2==={x3;x1}).
  apply Add_Equal in H0.
  assumption.
  rewrite H3 in H1.
  symmetry in H1.
  generalize(@fold_2 re _ _ _ x1 x2 x3 _ _ leq_equiv 0 _
    union_l_f_proper union_l_f_transpose H H0).
  intro.
  apply H4 in H2.
  clear H4.
  assert(Add x3 x1 y).
  apply Add_Equal.
  assumption.
  generalize(@fold_2 re _ _ _ x1 y x3 _ _ leq_equiv 0 _
    union_l_f_proper union_l_f_transpose H H4);intro.
  apply H5.
  clear H5.
  clear H4.
  destruct H2.
  left;auto.
  right;auto.
  
  unfold SreLf in H2 |- *.
  assert(x2==={x3;x1}).
  apply Add_Equal in H0.
  assumption.
  assert(Add x3 x1 y).
  apply Add_Equal.
  rewrite <- H1;auto.
  generalize H4;intro.
  apply Add_Equal in H5.
  generalize (@fold_2 re _ _ _ x1 x2 x3 _ _ leq_equiv 0 _
    union_l_f_proper union_l_f_transpose H H0).
  intro.
  apply H6;clear H6.
  generalize (@fold_2 re _ _ _ x1 y x3 _ _ leq_equiv 0 _
    union_l_f_proper union_l_f_transpose H H4).
  intro.
  apply H6;clear H6.
  assumption.
Qed.

Lemma SreL_SreLf_equiv : forall x,
  forall a, a ∈ SreL x <-> a ∈ SreLf x.
Proof.
  induction x using set_induction.
  split;intros.
  inversion_clear H0.
  apply empty_is_empty_1 in H.
  rewrite H in H1.
  inversion H1.
  unfold SreLf in H0.
  rewrite fold_1b in H0;auto.
  inversion H0.
  split;intros.
  inversion_clear H1.
  unfold SreLf.
  generalize (@fold_2 re _ _ _ x1 x2 x3 _ _ leq_equiv 0 _
    union_l_f_proper union_l_f_transpose H H0).
  intro.
  apply H1.
  clear H1.
  apply H0 in H2.
  destruct H2.
  apply re2rel_m_eq in H1.
  left.
  apply H1;auto.
  right.
  apply IHx1.
  econstructor 1 with r;auto.
  generalize (@fold_2 re _ _ _ x1 x2 x3 _ _ leq_equiv 0 _
    union_l_f_proper union_l_f_transpose H H0).
  intro.
  unfold SreLf in H1.
  apply H2 in H1;clear H2.
  destruct H1.
  econstructor 1 with x3.
  apply Add_Equal in H0.
  rewrite H0.
  apply add_1;auto.
  assumption.
  apply IHx1 in H1.
  inversion_clear H1.
  apply Add_Equal in H0.
  constructor 1 with r.
  rewrite H0.
  apply add_2;auto.
  assumption.
Qed.
   
Lemma SreL_SreLf_eq : forall x,
  L[x] ∼ L'[x].
Proof.
  intro;split;red;apply SreL_SreLf_equiv.
Qed.

Hint Constructors SreL : lgs.

Global Instance SreL_m : Proper(_eq ==> leq) SreL.
Proof.
  repeat red;split_eq;invc H0;econstructor;eauto;eapply H;auto.
Qed.

Lemma SreL_empty : 0 ∼ L[{}].
Proof.
  split_eq;invc H. inv H0.
Qed.

Lemma SreL_singleton : forall x:re,
  L[{x}%set] ∼ x.
Proof.
  split_eq ;[inv H|econstructor];eauto.
  apply singleton_1 in H0;apply re2rel_m_eq in H0;eauto.
  eapply singleton_2;auto. 
Qed.

Lemma SreL_union : forall x y:set re, 
  L[x ++ y] ∼ L[x] ∪ L[y].
Proof.
  split_eq.
  invc H;apply union_iff in H0;destruct H0;[left|right];econstructor;eauto.
  destruct H as [w H1| w H2];[invc H1|invc H2];econstructor 1 with r;eauto;
    [eapply union_2|apply union_3];eauto.
Qed.

Lemma SreL_add : forall a x,
  L[{a;x}] ∼ L[{a}%set] ∪ L[x].
Proof.
  split_eq.
  invc H.
  apply add_iff in H0;destruct H0;
    [left;econstructor 1 with r;auto;apply singleton_2|
      right;econstructor 1 with r];auto.
  destruct H as [w H1 | w H1];invc H1;constructor 1 with r;auto;
    [apply add_1;apply singleton_1 in H|apply add_2];auto with sets.
Qed.

Hint Resolve 
  SreL_empty 
  SreL_add
  SreL_union
  SreL_singleton : lgs.
Hint Rewrite
  SreL_empty 
  SreL_add
  SreL_union
  SreL_singleton : lgs.

Ltac dup_empty :=
  match goal with
    | [H:Empty ?x, H':?x===?y|-_] =>
      assert(Empty y);try (rewrite <- H';auto)
  end.

(** Constant language of a set o regular expressions.*)
Definition c_of_re_set (s:set re) := 
  fold (fun x => orb (ε(x))) s false.
Definition c_c_of_re_set (s:set re) :=
  if c_of_re_set s then 1 else 0.
  
Notation "εs( x )" := (c_of_re_set x)(at level 45).
Notation "εs'( x )" := (c_c_of_re_set x)(at level 45).

Instance c_of_re_set_m : Proper (_eq ==> eq ==> eq) (fun y : re => orb (ε(y))). 
Proof.
  repeat red;intros;subst;rewrite H;auto.
Qed.

Lemma c_of_re_set_transp : transpose eq (fun y : re => orb (ε(y))).
Proof.
  repeat red;intros;
  do 2 rewrite orb_assoc ; rewrite (orb_comm (ε(x)) (ε(y)));auto. 
Qed.
  
Hint Resolve c_of_re_set_transp : typeclass_instances.

Instance c_of_re_set_proper : Proper(_eq ==> _eq) c_of_re_set.
Proof.
  repeat red;intros;unfold c_of_re_set;
  apply fold_equal;autotc. 
Qed.

Instance c_of_re_set_m1 : 
  Proper (_eq ==> _eq ==> _eq) (fun y : re => orb (ε(y))). 
Proof.
  repeat red;intros;rewrite H,H0;auto.
Qed.
  
Instance c_c_of_re_set_m : Proper(_eq ==> _eq) (fun x => if εs(x) then 1 else 0).
Proof.
  repeat red;intros;rewrite H;auto;reflexivity.
Qed.
  
Instance c_c_of_re_set_proper : Proper(_eq ==> _eq) c_c_of_re_set.
Proof.
  repeat red;intros. 
  Typeclasses Transparent re_ord.
  rewrite H;reflexivity.
  Typeclasses Opaque re_ord.
Qed.
  
Lemma c_of_re_set_false : forall s,
  εs(s) = false -> forall x, x \In s -> ε(x) = false.
Proof.
  induction s using set_induction;intros.
  elim (H x);auto.
  unfold c_of_re_set in H1.
  rewrite (@fold_2 re _ _ _ s1 s2 x _ (@eq bool) eq_equivalence
      false (fun y : re => orb (ε(y)))
      c_of_re_set_m c_of_re_set_transp H H0) in H1.
  apply orb_false_elim in H1;destruct H1;auto.
  apply H0 in H2;destruct H2. rewrite H2 in H1;auto.
  apply IHs1 in H2;auto.
Qed.

Lemma true_c_of_re_set : 
  forall s x, 
    x \In s -> ε(x) = true -> εs(s) = true.
Proof.
  induction s using set_induction;intros.
  apply empty_is_empty_1 in H;rewrite H in H0;inv H0.
  
  unfold c_of_re_set;apply H0 in H1;destruct H1.
  rewrite (@fold_2 re _ _ _ s1 s2 x _ (@eq bool) eq_equivalence
      false (fun y : re => orb (ε(y)))
      c_of_re_set_m c_of_re_set_transp H H0).
  simpl_bool;rewrite H1;auto.
  
  rewrite (@fold_2 re _ _ _ s1 s2 x _ (@eq bool) eq_equivalence
      false (fun y : re => orb (ε(y)))
      c_of_re_set_m c_of_re_set_transp H H0).
  apply (IHs1 _ H1) in H2;simpl_bool;auto.
Qed.

Hint Resolve 
  c_of_re_set_false
  true_c_of_re_set : res.

Lemma c_of_re_set_true : forall s, 
  εs(s) = true -> exists x,( x \In s /\ ε(x) = true).
Proof.
  induction s using set_induction;intros.
  unfold c_of_re_set in H0;rewrite fold_1b in H0;auto;inv H0.
  
  unfold c_of_re_set in H1.
  rewrite (@fold_2 re _ _ _ s1 s2 x _ (@eq bool) eq_equivalence
      false (fun y : re => orb (ε(y)))
      c_of_re_set_m c_of_re_set_transp H H0) in H1.
  simpl_bool;destruct H1.
  exists x;split;eauto;eapply H0;eauto.
  apply IHs1 in H1.
  destruct H1 as [x' [H2 H3]];exists x';split;eauto.
  apply H0;eauto.
Qed.
  
Lemma c_c_of_re_set_c_of_re_1 : forall r,
  ε(r) = true -> εs'({r}%set) = 1.
Proof.
  unfold c_c_of_re_set.
  intros.
  case_eq(c_of_re_set {r});intros;auto.
  eapply (c_of_re_set_false {r}) with r in H0;
    [congruence|apply singleton_2;auto].
Qed.

Lemma c_c_of_re_set_c_of_re_0 : forall r,
  ε(r) = false -> εs'({r}%set) = 0.
Proof.
  unfold c_c_of_re_set;intros;case_eq(c_of_re_set {r});intros;autotc.
  apply c_of_re_set_true in H0;destruct H0 as [x' [H0 H1]].
  apply singleton_1 in H0;rewrite H0 in H;congruence.
Qed.

Hint Resolve
   c_c_of_re_set_c_of_re_0
   c_c_of_re_set_c_of_re_1 : res.

Lemma false_c_of_re_set : forall s, 
  (forall x, x \In s -> ε(x) = false) -> εs(s) = false.
Proof.
  induction s using set_induction;intros;unfold c_of_re_set.
  rewrite fold_1b;auto.
  
  rewrite (@fold_2 re _ _ _ s1 s2 x _ (@eq bool) eq_equivalence
    false (fun y : re => orb (ε(y)))
    c_of_re_set_m c_of_re_set_transp H H0). 
  simpl_bool.
  assert(x \In s2) by (apply H0;autotc).
  split. 
  apply H1;auto.
  apply IHs1.
  intros.
  apply H1.
  apply H0;auto.
Qed.

Lemma c_of_re_set_dec : forall s, {εs(s) = true}+{εs(s) = false}.
Proof.
  induction s using set_induction;simpl;intros;unfold c_of_re_set.
  right;rewrite fold_1b;auto.

  rewrite (@fold_2 re _ _ _ s1 s2 x _ (@eq bool) eq_equivalence
    false (fun y : re => orb (ε(y)))
      c_of_re_set_m c_of_re_set_transp H H0);destruct IHs1 as [e1|e1];
  fold (εs(s1));rewrite e1;rewrite orb_comm;auto.
  destruct(c_of_re_dec x) as [e2|e2];rewrite e2;auto. 
Qed.

Lemma c_of_re_set_has_nil :
  forall s, εs(s) = true -> [] ∈ L[s].
Proof.
  intros s H;apply c_of_re_set_true in H;destruct H as [x [H1 H2]].
  constructor 1 with x;auto with res.
Qed.

Lemma c_of_re_set_has_not_nil :
  forall s, εs(s) = false -> ~[] ∈ L[s].
Proof.
  intros s H;intro H1;invc H1.
  pose proof c_of_re_set_false s H r H0.
  apply not_eps_not_in_l in H1;contradiction.
Qed.

(* ESTE TEM QUE SAIR DAQUI E IR PARA O dsr_dsl.v *)
Lemma c_of_re_set_singleton : 
  forall s, εs({s}%set) = ε(s).
Proof.
  intros;case_eq(c_of_re_set {s});intro.
  apply c_of_re_set_true in H.
  do 2 destruct H;apply singleton_1 in H.
  rewrite H;congruence.
  assert(s \In {s}%set) by (apply singleton_2;auto).
  generalize(c_of_re_set_false _ H _ H0);congruence.
Qed.

Hint Rewrite
  c_of_re_set_singleton : res.

Hint Resolve
  c_of_re_set_false
  true_c_of_re_set
  c_of_re_set_true
  c_c_of_re_set_c_of_re_1
  c_c_of_re_set_c_of_re_0
  false_c_of_re_set
  c_of_re_set_has_nil
  c_of_re_set_has_not_nil : res.
  
Global Instance re2rel_m_m : Proper(_eq ==> leq) re2rel.
Proof.
  repeat red;split_eq;apply re_leibniz in H;subst;auto.
Qed.

Lemma has_nil_c_of_re_set :
  forall s, [] ∈ L[s] -> εs(s) = true.
Proof.
  intros s H;inv H;apply eps_in_l_null in H1;eapply true_c_of_re_set;eauto.
Qed.

Lemma has_not_nil_c_of_re_set :
  forall s, ~[] ∈ L[s] -> εs(s) = false.
Proof.
  intros s H;apply not_true_is_false;intro;apply c_of_re_set_has_nil in H0;contradiction. 
Qed.

Hint Resolve 
  has_nil_c_of_re_set
  has_not_nil_c_of_re_set : res.
