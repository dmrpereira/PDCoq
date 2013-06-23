Add LoadPath "." as PDCoq.
Require Export base pdrvs decide Utf8 Relations ZArith BinNums Plug.

Section RelInterp.
  
  Variable B:Type.
  Hypothesis BOrd : UsualOrderedType B.
  Hypothesis v : Z -> relation B. 
  
  Definition EmpRel : relation B := fun _ _:B => False.
  Definition IdRel : relation B := fun x y :B => x = y.
  Definition UnionRel (x y:relation B) : relation B := union _ x y.
  Definition CompRel (R S: relation B): relation B := 
    fun i k => exists j, R i j /\ S j k.
    (*Inductive CompRel : relation B -> relation B -> relation B :=
    | mkComp : forall R S:relation B, 
               forall a c, R a c -> forall b, R c b -> CompRel R S a b.*)
  Inductive trans_refl (R:relation B) : relation B :=
  | trr : forall x, trans_refl R x x
  | trt : forall x y, R x y -> forall z, trans_refl R y z -> trans_refl R x z.

  Lemma trans_refl_trans :
    forall R x y, 
      trans_refl R x y -> forall z,
                            trans_refl R y z -> trans_refl R x z.
  Proof.
    induction 1;intros.
    assumption.
    inversion_clear H0.
    constructor 2 with y;auto.
    constructor 2 with y;auto.
  Qed.
  

  Fixpoint nRel(r:relation B)(n:nat):relation B :=
    match n with
      | O => IdRel
      | S m => CompRel r (nRel r m)
    end.

  Lemma nRel_in_trans_refl :
    forall n R a b,
      nRel R n a b -> trans_refl R a b.
  Proof.
    induction n;simpl;intros.
    red in H;subst.
    constructor 1.
    do 2 destruct H.
    constructor 2 with x;auto.
  Qed.

  Lemma in_trans_refl_nRel :
    forall R a b,
      trans_refl R a b -> exists n, nRel R n a b.
  Proof.
    induction 1;intros.
    exists O;simpl;red;auto.
    
    destruct IHtrans_refl.
    destruct H0.
    exists (S x0).
    simpl.
    esplit;eauto.
    exists (S x0).
    esplit;eauto.
  Qed.

  Fixpoint reRel(v:Z -> relation B)(r:re) : relation B :=
    match r with
      | re0 => EmpRel
      | re1 => IdRel
      | re_sy a => v a
      | re_union x y => UnionRel (reRel v x) (reRel v y)
      | re_conc x y => CompRel (reRel v x) (reRel v y)
      | re_star x => trans_refl (reRel v x)
    end.

  Fixpoint reRelW (v:Z -> relation B)(w:word) : relation B :=
    match w with
      | nil => IdRel
      | x::xs => CompRel (v x) (reRelW v xs)
    end.

  Definition rel_eq (R1 R2:relation B) : Prop :=
    same_relation B R1 R2.

  Global Instance rel_eq_equiv : Equivalence rel_eq.
  Proof.
    constructor;red;unfold inclusion;intros;repeat red;unfold inclusion;
    split;intros;eauto.
    apply H in H0.
    assumption.
    apply H in H0.
    auto.
    apply H in H1.
    apply H0 in H1.
    assumption.
    apply H0 in H1.
    apply H in H1.
    assumption.
  Qed.

  (*Definition v (r:A):= IdRel.*)

  Lemma reRelW_append :
    forall  w1 w2,
      rel_eq (CompRel (reRelW v w1) (reRelW v w2)) (reRelW v (w1++w2)%list).
  Proof.
    split;unfold inclusion;intros.
    
    revert w1 w2 x y H.
    induction w1;simpl;intros.

    inversion_clear H.
    destruct H0.
    red in H;subst.
    assumption.
    do 4 destruct H.
    constructor 1 with x1.
    split;auto.
    apply IHw1.
    constructor 1 with x0;auto.
    
    revert w1 w2 x y H.
    induction w1;simpl;intros.
    destruct w2.
    simpl in *.
    unfold IdRel in *;simpl in *;subst.
    econstructor 1 with y;eauto.
    simpl in *.
    do 2 destruct H.
    split with x.
    split.
    red;auto.
    exists x0.
    split;auto.
    do 2 destruct H.
    apply IHw1 in H0.
    do 2 destruct H0.
    exists x1;split.
    exists x0;split;auto.
    assumption.
  Qed.

  Inductive ReL : re -> relation B :=
  |mkRel : forall x:re, 
           forall w1, 
             w1 ∈ re2rel x -> forall a b, 
                                   (reRelW v w1) a b -> ReL x a b.

  Lemma Main :
    forall r:re, rel_eq (reRel v r) (ReL r).
  Proof.
    induction r;unfold rel_eq, same_relation, inclusion;simpl.

    simpl;split;intros.
    inversion H.
    inversion_clear H.
    inversion H0.

    split;intros.
    red in H;subst.
    econstructor 1 with (@nil Z).
    constructor.
    simpl;red;auto.
    inversion_clear H.
    inversion H0.
    symmetry in H;subst.
    simpl in H1;subst;red;auto.

    split;intros.
    econstructor 1 with (z::nil).
    constructor.
    simpl.
    reflexivity.
    constructor 1 with y.
    split;auto.
    red;auto.
    red;auto.
    inversion_clear H.
    inversion H0.
    symmetry in H;subst.
    simpl in H1.
    inversion_clear H1.
    destruct H2.
    rewrite H.
    red in H2.
    subst;auto.

    split;intros.
    destruct H.
    red in IHr1.
    apply IHr1 in H.
    inversion H;subst.
    econstructor 1 with w1.
    left;auto.
    assumption.
    red in IHr2.
    apply IHr2 in H.
    inversion H;subst.
    econstructor 1 with w1.
    right;auto.
    assumption.

    inversion_clear H.
    simpl in H0.
    inversion_clear H0.
    left.
    apply IHr1.
    econstructor 1 with w1;auto.
    constructor 2.
    apply IHr2.
    econstructor 1 with w1;auto.

    split;intros.
    do 2 destruct H.
    apply IHr1 in H.
    apply IHr2 in H0.
    inversion_clear H.
    inversion_clear H0.
    econstructor 1 with (w1++w0)%list.
    simpl.
    constructor;auto.
    apply reRelW_append.
    split with x0.
    split;auto.
    simpl.
    inversion H.
    subst.
    simpl in H0.
    inversion H0;subst.
    apply reRelW_append in H1.
    destruct H1.
    destruct H1.
    split with x0.
    split.
    apply IHr1.
    econstructor;eauto.
    apply IHr2.
    econstructor;eauto.

    split;intros.
    apply in_trans_refl_nRel in H.
    destruct H.
    revert x0 x y H.
    induction x0;simpl;intros.
    red in H;subst.
    econstructor 1 with (@nil Z).
    constructor 1 with O;simpl;auto.
    constructor.
    simpl.
    do 2 destruct H.
    pose proof IHx0 _ _ H0.
    generalize H;intro.
    apply IHr in H2.
    inversion H2.
    subst.
    pose proof H0.
    apply IHx0 in H5.
    inversion_clear H5.
    econstructor 1 with (w1++w0)%list.
    apply lang_in_star_to_n in H6.
    destruct H6.
    constructor 1 with (S x2).
    simpl.
    constructor.
    assumption.
    apply H5.
    apply reRelW_append.
    split with x1.
    split;auto.

    inversion H;subst.
    clear H.
    simpl in H0.
    apply lang_in_star_to_n in H0.
    destruct H0.
    revert x0 x w1 H H1.
    induction x0;simpl;intros.
    assert(w1 ∈ {ε} -> w1 = (@nil Z)).
    induction w1;intros;auto.
    inversion H0.
    apply H0 in H.
    subst.
    simpl in H1.
    red in H1;subst.
    constructor.

    inversion H;subst.
    clear H.
    apply reRelW_append in H1.
    destruct H1.
    destruct H.
    revert x0 IHx0 H2.
    induction x0;intros.
    simpl in *.
    constructor 2 with x1.
    apply IHr.
    econstructor 1;eauto.
    
    eapply IHx0.
    apply H2.
    assumption.
    constructor 2 with x1.
    apply IHr.
    econstructor;eauto.
    apply IHx1 with w2.
    assumption.
    assumption.
  Qed.

  Theorem Rel_red_Leq :
    forall r1 r2:re,
      r1 ∼ r2 -> rel_eq (ReL r1) (ReL r2).
  Proof.
    split;unfold inclusion;intros;
    inversion H0;subst;
    constructor 1 with w1;auto;apply H;auto.
  Qed.

  Theorem Rel_red_Leq_final :
    forall r1 r2:re,
      r1 ∼ r2 -> rel_eq (reRel v r1) (reRel v r2).
  Proof.
    intros.
    rewrite (Main r1).
    rewrite (Main r2).
    apply Rel_red_Leq.
    assumption.
  Qed.
  
End RelInterp.

Require Export Maps.

(** Default type to be used. *)
Definition STD(T:Type) : relation T := IdRel T.
  
(** The empty map for reification. *)
Definition emp_m(T:Type) : Map[Z,relation T] := 
  @empty Z _ _ (relation T).
  
(** Adding an element to the reification map. *)
Definition add_mm(T:Type)(x:Z)(r:relation T)(m:Map[Z,relation T]) :=
  @add Z _ _ (relation T) x r m.
  
(** Find the map from [nat] to a relation, or return the default relation *)
Definition find_mm(T:Type)(x:Z)(m:Map[Z,relation T]) :=
  match @find Z _ _ (relation T) x m with
    | None => STD T
    | Some y => y
  end.
  
Definition f(T:Type)(v:Map[Z,relation T])(x:Z) :=
  find_mm T x v.

Ltac solve_rel :=
  intros;rel2re_eq;apply Rel_red_Leq_final;dec_re.

Goal forall T:Type,forall R1 R2 R3:relation T,
  rel_eq T (UnionRel T R1 (UnionRel T R2 R3)) (UnionRel T (UnionRel T R1 R2) R3).
Proof.
  solve_rel.
Qed.
 

