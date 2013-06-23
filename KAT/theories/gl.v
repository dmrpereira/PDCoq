Require Export kat_alph atoms gs.

(** * Languages of Guarded Strings *)
(** Like words, guarded strings can be gathered into possibly infinite
sets to form languages. We call these languages Languages of Guarded Strings. *)


Module GL(X:KAT_Alph).

  Module Export gS := GS(X).

  Definition gl := Ensemble gstring.

  (** The empty guarded language. *)

  Definition gl_emp := Empty_set gstring.

  (** The empty word guarded language. *)

  Inductive gl_eps : gl :=
  | mk_gl_eps : forall α, In _ (gl_eps) (gs_end α).

  (** Guarded language of a single symbol [s]. *)
  
  Inductive gl_sy (p:Z) : gl :=
  | mk_gl_sy : forall α β:atom, In _ (gl_sy p) (gs_conc α p (gs_end β)).

  (** Guarded language of a test [t]. *)

  Inductive gl_atom (t:test) : gl :=
  | mk_gl_atom : forall α, evalT α t = true -> In _ (gl_atom t) (gs_end α).
  
  (** The singleton language containing only the atom [α] *)

  Inductive gl_at_only (α:atom) : gl :=
  | mk_gl_atom_only : In _ (gl_at_only α) (gs_end α).
  
  (** Union of two guarded languages. *)

  Definition gl_union(l₁ l₂:gl) := Union _ l₁ l₂.

  (** Concatenation of two guarded languages. *)

  Inductive gl_conc(l₁ l₂:gl) : gl :=
  |mkg_gl_conc : 
   forall x y (T:compatible x y),
     In _ l₁ x -> 
     In _ l₂ y -> In _ (gl_conc l₁ l₂) (fusion_prod x  y T).

  (** [n]th power of a guarded language. *)

  Fixpoint conc_gln (L:gl)(n:nat) : gl :=
    match n with
      | 0     => gl_eps
      | S m => gl_conc L (conc_gln L m)
    end.
  
  (** Kleene closure of a guarded languages. *)
  
  Inductive gl_star(l:gl) : gl :=
  |mk_gl_star : 
   forall n gw,
     In _ (conc_gln l n) gw -> In _ (gl_star l) gw.

  (** Guarded language equality. *)
  
  Definition gl_eq (L1 L2:gl) := Same_set _ L1 L2.
  Notation "x == y" := (gl_eq x y).

  (** Morphisms for rewriting with [leq]. *)

  Global Instance gl_eq_equiv : Equivalence gl_eq.
  Proof.
    constructor;unfold gl_eq;
    [unfold Reflexive|unfold Symmetric|unfold Transitive].
    (* reflexivity *)
    repeat red;split;red;auto.
    (* symmetry *)
    split;apply H.
    (* transitivity *)
    unfold Same_set,Included;split;intros;
    inversion H;
    inversion H0;
    intuition.
  Qed.

  Global Instance gl_sy_m : Proper(_eq ==> gl_eq) gl_sy.
  Proof.
    split;red;intros;
    destruct H;auto.
  Qed.

  (** Guarded strings and tests are equal module Coq's convertibility. *)

  Lemma gs_leibniz :
    forall x y:gstring,
      _eq x y -> x = y.
  Proof.
    induction 1;intros;auto.
  Qed.

  Lemma test_leibniz :
    forall x y:test,
      _eq x y -> x = y.
  Proof.
    induction 1;auto;subst;auto.
  Qed.

  Global Instance gl_atom_m : Proper(_eq ==> gl_eq) gl_atom.
  Proof.
    repeat red.
    intros.
    apply test_leibniz in H.
    rewrite H;split;red;auto.
  Qed.

  Global Instance gl_union_m : Proper(gl_eq ==> gl_eq ==> gl_eq) gl_union.
  Proof.
    repeat red.
    intros.
    destruct H.
    destruct H0.
    split;red;intros.
    destruct H3.
    apply H in H3.
    constructor 1;auto.
    apply H0 in H3.
    constructor 2;auto.

    destruct H3.
    apply H1 in H3.
    constructor;auto.
    apply H2 in H3.
    constructor 2;auto.
  Qed.

  Global Instance gl_conc_m : Proper(gl_eq ==> gl_eq ==> gl_eq) gl_conc.
  Proof.
    intros.
    split;unfold Included;intros;
    destruct H1;
    constructor;
    first [apply H|apply H0];auto.
  Qed.

  Global Instance conc_gln_m : Proper (gl_eq ==> _eq ==> gl_eq) conc_gln.
  Proof.
    repeat red.
    intros.
    destruct H0.
    revert x0 x y H.
    induction x0;simpl;intros.
    split;red;intros;auto.
    split;
    apply gl_conc_m;auto.
    symmetry.
    assumption.
    apply IHx0 in H.
    destruct H.
    split;auto.
    apply IHx0 in H.
    destruct H.
    split;auto.
  Qed.

  Global Instance gl_star_m : Proper(gl_eq ==> gl_eq) gl_star.
  Proof.
    repeat red.
    intros.
    split;red;intros;
    inversion_clear H0.
    revert n x y x0 H H1;
    induction n;simpl;intros.
    inversion_clear H1.
    econstructor 1 with 0.
    simpl.
    constructor.
    inversion_clear H1.
    constructor 1 with (S n).
    simpl.
    constructor.
    apply H.
    assumption.
    eapply conc_gln_m.
    Focus 3.
    apply H2.
    symmetry;assumption.
    reflexivity.
    revert n x y x0 H H1;
    induction n;simpl;intros.
    inversion_clear H1.
    econstructor 1 with 0.
    simpl.
    constructor.
    inversion_clear H1.
    constructor 1 with (S n).
    simpl.
    constructor.
    apply H.
    assumption.
    eapply conc_gln_m.
    apply H.
    reflexivity.
    assumption.
  Qed.

  (** Properties of guarded languages. *)

  Lemma gl_emp_eq_gl_atom_ba0 :
    gl_emp == gl_atom ba0.
  Proof.
    split;red;intros.
    inversion H.
    inversion H. 
    subst.
    simpl in H0.
    discriminate.
  Qed.

  Hint Rewrite gl_emp_eq_gl_atom_ba0 : gl_rw.

  Lemma gl_eps_eq_gl_atom_ba1 :
    gl_eps == gl_atom ba1.
  Proof.
    split;red;intros.
    inversion H.
    econstructor.
    simpl.
    reflexivity.
    inversion H.
    constructor.
  Qed.

  Hint Rewrite gl_eps_eq_gl_atom_ba1 : gl_rw.

  Lemma union_left_zero :
    forall l,
      gl_union gl_emp l == l.
  Proof.
    split;red;intros.
    inversion_clear H.
    inversion H0.
    assumption.

    right;auto.
  Qed.

  Lemma fusion_prod_idemp :
    forall x,exists H,
      x = fusion_prod x (gs_end (last x)) H.
  Proof.
    intros.
    exists (refl_equal (last x)).
    revert x.
    induction x.
    simpl.
    reflexivity.
    rewrite IHx at 1.
    simpl.
    reflexivity.
  Qed.

  Lemma conc_unit_left :
    forall l x,
      In _ (gl_conc gl_eps l) x -> In _ l x.
  Proof.
    intros.
    inversion H.
    inversion H0.
    symmetry in H3.
    subst.
    simpl.
    assumption.
  Qed.

  Lemma conc_unit_right :
    forall l x,
      In _ (gl_conc l gl_eps) x -> In _ l x.
  Proof.
    intros.
    inversion H.
    inversion H1.
    symmetry in H3.
    subst.
    
    simpl.
    rewrite fusion_prod_end.
    assumption.
  Qed.


  (** Properties for guarded languages formed only by atoms. *)

  Section AtomLanguages.
    
    Lemma conc_gl_atom_false_left :
      forall b,
        gl_conc (gl_atom ba0) b == (gl_atom ba0).
    Proof.
      split;red;intros.
      inversion H.
      inversion H0.
      simpl in H3.
      discriminate.

      inversion H.
      simpl in H0.
      discriminate.
    Qed.

    Lemma conc_gl_atom_false_right :
      forall b,
        gl_conc b (gl_atom ba0) == (gl_atom ba0).
    Proof.
      split;red;intros.
      inversion H.
      inversion H1.
      simpl in H3.
      discriminate.

      inversion H.
      simpl in H0.
      discriminate.
    Qed.

    Lemma gl_atom_double_neg :
      forall b,
        gl_atom (baN (baN b)) == gl_atom b.
    Proof.
      split;red;intros.
      inversion H;subst.
      simpl in H0.
      constructor.
      symmetry.
      rewrite <- Bool.negb_involutive.
      symmetry;auto.

      inversion H.
      constructor.
      simpl.
      rewrite Bool.negb_involutive.
      assumption.
    Qed.

    (** b.T = b *)

    Lemma conc_gl_atom_true_left :
      forall b, 
        gl_conc b (gl_atom ba1) == b.
    Proof.
      split;red;intros.
      inversion H.
      apply gl_eps_eq_gl_atom_ba1 in H1.
      inversion H1.
      revert T H2.
      rewrite <- H3.
      intros.
      rewrite H2.
      rewrite (fusion_prod_end x0 α) in H2.
      subst.
      assumption.

      assert(exists t, x = fusion_prod x (gs_end (last x)) t).
      unfold compatible.
      simpl.
      exists (refl_equal (last x)).
      assert(forall y, y = fusion_prod y (gs_end (last y)) (eq_refl (last y))).
      induction y;simpl;intros.
      reflexivity.
      generalize(eq_refl (last y)).
      generalize(eq_refl (gs_conc o z y)).
      intros e e0.
      generalize((compatible_rewrite (gs_conc o z y) (gs_end (last y)) e0 o z y e)).
      intro.
      f_equal.
      rewrite <- fusion_prod_same_last.
      reflexivity.
      rewrite <- fusion_prod_same_last.
      reflexivity.
      destruct H0.
      rewrite H0.
      constructor.
      assumption.
      constructor.
      simpl.
      reflexivity.
    Qed.

    Lemma conc_gl_atom_true_right :
      forall b, 
        gl_conc (gl_atom ba1) b == b.
    Proof.
      split;red;intros.
      inversion H.
      apply gl_eps_eq_gl_atom_ba1 in H0.
      inversion H0.
      revert T H2.
      rewrite <- H3.
      intros.
      rewrite H2.
      simpl in H2.
      rewrite <- H2.
      assumption.

      assert(exists t, x = fusion_prod (gs_end (first x)) x t).
      unfold compatible.
      simpl.
      exists (refl_equal (first x)).
      reflexivity.
      destruct H0.
      rewrite H0.
      constructor;auto.
      constructor.
      simpl.
      reflexivity.
    Qed.

    Lemma union_gl_atom :
      forall b1 b2,
        gl_atom (baOr b1 b2) == gl_union (gl_atom b1) (gl_atom b2).
    Proof.
      split;red;intros.
      inversion_clear H.
      simpl in H0.
      apply Bool.orb_true_iff in H0.
      destruct H0;
        [left|right];constructor;assumption.
      
      inversion_clear H;inversion_clear H0;
      econstructor;simpl;apply Bool.orb_true_iff ;
      [left|right];assumption.
    Qed.

    Lemma conj_gl_atom :
      forall b1 b2,
        gl_atom (baAnd b1 b2) == gl_conc (gl_atom b1) (gl_atom b2).
    Proof.
      split;red;intros.
      inversion_clear H.
      simpl in H0.
      apply Bool.andb_true_iff in H0.
      destruct H0.
      assert(exists x, gs_end α = fusion_prod (gs_end α) (gs_end α) x).
      simpl.
      exists (refl_equal α).
      reflexivity.
      destruct H1.
      rewrite H1.
      constructor;constructor;auto.
      
      inversion_clear H.
      inversion H0.
      revert T.
      inversion H1.
      rewrite <- H2.
      simpl.
      intros.
      constructor.
      simpl.
      apply Bool.andb_true_iff.
      split;auto.
      red in T.
      simpl in T.
      rewrite <- T.
      assumption.
    Qed.

    Lemma gl_atom_neg_and :
      forall b1 b2,
        gl_atom (baN (baAnd b1 b2)) == gl_union (gl_atom (baN b1)) (gl_atom (baN b2)).
    Proof.
      split;red;intros.
      inversion H.
      simpl in H0.
      rewrite Bool.negb_andb in H0.
      apply Bool.orb_prop in H0.
      destruct H0.
      left.
      constructor.
      simpl.
      assumption.
      right;constructor;simpl.
      assumption.
      
      inversion H.
      inversion H0.
      simpl in *.
      constructor.
      simpl.
      rewrite Bool.negb_andb.
      eapply Bool.orb_true_iff.
      left;auto.

      inversion H0.
      simpl in *.
      constructor.
      simpl.
      rewrite Bool.negb_andb.
      eapply Bool.orb_true_iff.
      right;auto.
    Qed.

    Lemma gl_atom_false_conj :
      forall b,
        gl_atom (baAnd (baN b) b) == gl_emp.
    Proof.
      split;red;intros.
      inversion H.
      simpl in H0.
      rewrite Bool.andb_comm in H0.
      rewrite Bool.andb_negb_r in H0.
      discriminate.

      inversion H.
    Qed.

  End AtomLanguages.

  (** Semiring lemmas for guarded languages *)

  Lemma gl_conc_unit_left :
    forall l,
      gl_conc gl_eps l == l.
  Proof.
    intros.
    split;red;intros.
    inversion H.
    eapply conc_gl_atom_true_right.
    constructor;auto.
    inversion H0.
    econstructor.
    simpl.
    reflexivity.
    eapply conc_gl_atom_true_right in H.
    inversion H.
    constructor.
    apply gl_eps_eq_gl_atom_ba1.
    assumption.
    assumption.
  Qed.

  Hint Rewrite gl_conc_unit_left : gl_rw.

  Lemma gl_conc_unit_right :
    forall l,
      gl_conc l gl_eps == l.
  Proof.
    intros.
    split;red;intros.
    inversion H.
    eapply conc_gl_atom_true_left.
    constructor;auto.
    inversion H1.
    econstructor.
    simpl;auto.
    eapply conc_gl_atom_true_left in H.
    inversion H.
    constructor;auto.
    apply gl_eps_eq_gl_atom_ba1.
    assumption.
  Qed.

  Hint Rewrite gl_conc_unit_right : gl_rw.

  Lemma gl_conc_unit :
    forall l,
      gl_conc l gl_eps == gl_conc gl_eps l.
  Proof.
    intros.
    autorewrite with gl_rw.
    reflexivity.
  Qed.
    
  Lemma union_right_zero :
     forall l,
       gl_union l gl_emp == l.
  Proof.
    split;red;intros.
    inversion_clear H;auto.
    inversion H0.

    left;auto.
  Qed.

  Hint Rewrite union_left_zero union_right_zero : gl_rw.

  Corollary union_zero :
     forall l,
       gl_union l gl_emp == gl_union gl_emp l.
  Proof.
    intro.
    autorewrite with gl_rw;reflexivity.
  Qed.    

  Lemma conc_absorvent_left :
    forall l,
      gl_conc gl_emp l == gl_emp.
  Proof.
    split;red;intros.
    inversion H;subst.
    inversion H0.
    inversion H.
  Qed.

  Lemma conc_absorvent_right :
    forall l,
      gl_conc l gl_emp == gl_emp.
  Proof.
    split;red;intros.
    inversion_clear H.
    inversion H1.
    inversion H.
  Qed.

  Hint Rewrite conc_absorvent_left conc_absorvent_right : gl_rw.

  Corollary conc_absorvent :
    forall l,
      gl_conc l gl_emp == gl_conc gl_emp l.
  Proof.
    intro.
    autorewrite with gl_rw;reflexivity.
  Qed.
  
  Lemma union_assoc_gl :
    forall l1 l2 l3:gl,
      gl_union l1 (gl_union l2 l3) == gl_union (gl_union l1 l2) l3.
  Proof.
    intros.
    split;red;intros.
    inversion_clear H.
    constructor.
    left.
    assumption.
    inversion_clear H0.
    constructor;right;auto.
    constructor 2;auto.

    inversion_clear H.
    inversion_clear H0.
    constructor 1;auto.
    constructor 2;left;auto.
    do 2 constructor 2;auto.
  Qed.

  Lemma conc_assoc_gl :
    forall l1 l2 l3:gl,
      gl_conc l1 (gl_conc l2 l3) == gl_conc (gl_conc l1 l2) l3.
  Proof.
    intros.
    split;red;intros.
    inversion H;subst.
    inversion H1;subst.
    pose proof fusion_product_assoc_left x x0 y0 T0 T.
    destruct H4.
    destruct H4.
    rewrite H4.
    constructor;auto.
    constructor;auto.

    inversion H;subst.
    inversion H0;subst.
    pose proof fusion_product_assoc_right y0 x y T0 T.
    destruct H4.
    destruct H4.
    rewrite H4.
    constructor;auto.
    constructor;auto.
  Qed.

  Lemma conc_distr_left :
    forall l1 l2 l3,
      gl_conc (gl_union l1 l2) l3 == gl_union (gl_conc l1 l3) (gl_conc l2 l3).
  Proof.
    intros.
    split;red;intros.
    inv H.
    inv H0.
    subst.
    left.
    constructor;auto.
    subst.
    right.
    constructor;auto.
    inv H.
    inv H0.
    subst.
    constructor.
    left.
    assumption.
    assumption.
    inv H0.
    constructor.
    right;auto.
    assumption.
  Qed.

  Lemma conc_distr_right :
    forall l1 l2 l3,
      gl_conc l1 (gl_union l2 l3) == gl_union (gl_conc l1 l2) (gl_conc l1 l3).
  Proof.
    intros.
    split;red;intros.
    inv H.
    inv H1.
    constructor.
    constructor;auto.
    subst.
    constructor 2.
    constructor;auto.

    inv H.
    inv H0.
    constructor;auto.
    left;auto.
    inv H0.
    constructor.
    assumption.
    right;auto.
  Qed.

  Lemma union_idemp :
    forall l,
      gl_union l l == l.
  Proof.
    split;red;intros.
    inv H;auto.
    left;auto.
  Qed.

  Lemma union_comm :
    forall l1 l2,
      gl_union l1 l2 == gl_union l2 l1.
  Proof.
    split;red;intros;
    now(inv H;[right|left];auto).
  Qed.  

  (* These axioms' proofs are the same as the ones of regular
  languages. Must be realized in the future!!! *)
  (* Axiom gl_star_eq_left : *)
  (*   forall l, *)
  (*     gl_union gl_eps (gl_conc (gl_star l) l) == gl_star l. *)

  (* Axiom gl_star_eq_right : *)
  (*   forall l, *)
  (*     gl_union gl_eps (gl_conc l (gl_star l)) == gl_star l. *)

  (** * Natural partial relation on guarded languages *)

  Definition gl_leq l1 l2 := gl_union l1 l2 == l2.
  Notation "x ≤ y" := (gl_leq x y)(at level 45).

  (* Axiom gl_leq_left : *)
  (*   forall l1 l2 l3, *)
  (*     gl_union l1 (gl_conc l2 l3) <<= l3 -> gl_conc (gl_star l2)  l1 <<= l3. *)

  (* Axiom gl_leq_right : *)
  (*   forall l1 l2 l3, *)
  (*     gl_union l1 (gl_conc l3 l2) <<= l3 -> gl_conc l1 (gl_star l2) <<= l3. *)

  (** * Regular Guarded Languages *)

  Inductive rgl : gl -> Prop :=
  | rgl0 : rgl gl_emp
  | rl1 : rgl gl_eps
  | rglsy : forall p, rgl (gl_sy p) 
  | rglb : forall t, rgl (gl_atom t)
  | rglp : forall l₁ l₂, rgl l₁ -> rgl l₂ -> rgl (gl_union l₁ l₂)
  | rglc : forall l1 l2, rgl l1 -> rgl l2 -> rgl (gl_conc l1 l2)
  | rglst : forall l, rgl l -> rgl (gl_star l).

  Hint Constructors rgl : gl_hints.

  (** *  Left quotients of guarded languages. *)


  Inductive LQ (l:gl) : atom -> Z -> gl :=
  | in_quo : forall a x y, In _ l (gs_conc a x y) -> In _ (LQ l a x) y.

  Inductive LQw (l:gl) : gstring -> gl :=
  | in_quow : forall x w T, 
                In _ l (fusion_prod w x T) -> In _ (LQw l w) x.

  (** * Left quotient of guarded languages wrt. words (guardeds string
  without the last atom, or just lists of pairs [(atom*Z)] *)


  Inductive LQw_alt (l:gl) : seq -> gl :=
  | in_quow_alt : forall x w, 
                In _ l (to_gstring x w) -> In _ (LQw_alt l x) w.

  Hint Constructors LQ LQw LQw_alt : gl_hints.

  (** Bureocratic morphisms for rewriting with the previously defined language quotients. *)

  Instance LQ_m : Proper( gl_eq ==> _eq ==> _eq ==> gl_eq) LQ.
  Proof.
    repeat red.
    intros.
    normalize_notations.
    inv H0;subst.
    inv H1.
    subst.
    split;red;intros;
    inversion_clear H2;constructor;apply H;
    assumption.
  Qed.

  Instance LQw_m : Proper(gl_eq ==> _eq ==> gl_eq) LQw.
  Proof.
    repeat red.
    intros.
    apply gs_leibniz in H0.
    subst.
    split;red;intros;inversion_clear H0;
    econstructor;apply H;eauto.
  Qed.

  Instance LQw_alt_m : Proper(gl_eq ==> _eq ==> gl_eq) LQw_alt.
  Proof.
    repeat red.
    intros.
    pose proof list_leibniz x0 y0.
    apply H1 in H0.
    subst.
    gl_goal.
    inv H0.
    constructor.
    subst.
    apply H in H2.
    assumption.
    inv H0.
    subst.
    constructor.
    apply H;auto.
  Qed.

  Definition o0 : atom.
  Proof.
    refine(@Ord (pow2 ntests) 0 _).
    abstract(pose proof pow2_geq_1 ntests;
             inv H;simpl;reflexivity).
  Defined.

  Corollary empty_not_nil : ~(gl_eps == gl_emp).
  Proof.
    intro H;repeat red in H;
      destruct H as [H0 H1].
    repeat red in H0,H1.
    pose proof H0 (gs_end o0).
    assert(In gstring gl_eps (gs_end o0)).
    constructor.
    apply H in H2.
    inv H2.
  Qed.

  (** * Properties of the defined quotients *) 
  
  Section LQProperties.

    Lemma LQ_Empty : forall a s, LQ gl_emp a s == gl_emp.
    Proof.
      split;red;intros.
      inv H.
      inv H0.
      inv H.
    Qed.

    Lemma LQ_EpsL : 
      forall a s, LQ gl_eps a s == gl_emp.
    Proof.
      split;red;intros.
      inv H.
      inv H0.
      inv H.
    Qed.

    Lemma LQ_SyL_eq : 
      forall a s1 s2,
        s1 = s2 -> LQ (gl_sy s1) a s2 == gl_eps.
    Proof.
      split;red;intros.
      inv H0.
      inv H1.
      subst.
      econstructor.

      inv H0.
      subst.
      constructor.
      constructor.
    Qed.

    Lemma LQ_SyL_neq : 
      forall a s1 s2, 
        s1 <> s2 -> LQ (gl_sy s1) a s2 == gl_emp.
    Proof.
      split;red;intros.
      inv H0.
      subst.
      inv H1.
      inv H0.
    Qed.

    Lemma LQ_Test :
      forall b a s,
        LQ (gl_atom b) a s == gl_emp.
    Proof.
      split;red;intros.
      inv H.
      inv H0.
      inv H.
    Qed.

    Lemma LQ_union : 
      forall l1 l2 a s, 
        LQ (gl_union l1 l2) a s == gl_union (LQ l1 a s) (LQ l2 a s).
    Proof.
      split;red;intros.
      inv H.
      inv H0.
      subst.
      constructor 1.
      constructor.
      assumption.

      subst.
      constructor 2.
      constructor.
      assumption.

      inv H.
      inv H0.
      subst.
      constructor.
      constructor 1.
      assumption.

      inv H0.
      subst.
      constructor.
      constructor 2.
      assumption.
    Qed.

  End LQProperties.

  Hint Rewrite LQ_Empty LQ_EpsL LQ_SyL_eq LQ_SyL_neq LQ_union : gl_rw.
  Hint Resolve LQ_Empty LQ_EpsL LQ_SyL_eq LQ_SyL_neq LQ_union : gl_rw.

  
  Section LQwProperties.

    Lemma LQw_alt_nil :
      forall l,
        LQw_alt l nil == l.
    Proof.
      gl_goal.
      inv H.
      simpl in H0.
      assumption.
      constructor.
      simpl.
      assumption.
    Qed.
    
    Lemma LQw_alt_eq_LQ :
      forall l a s,
        LQw_alt l ((a,s)::nil) == LQ l a s.
    Proof.
      gl_goal.
      inv H.
      constructor.
      simpl in H0.
      assumption.
      inv H.
      constructor.
      simpl.
      assumption.
    Qed.
    
    Lemma w_in_gl_eq_last_in_LQw :
      forall w l,
        In _ l w -> In _ (LQw_alt l (from_gstring w)) (gs_end (last w)).
    Proof.
      intros.
      econstructor.
      rewrite <- from_to_gstring.
      assumption.
    Qed.
    
    Lemma last_in_LQw_eq_w_in_gl : 
      forall w l, 
        In _ (LQw_alt l (from_gstring w)) (gs_end (last w)) -> In _ l w.
    Proof.
      intros.
      inversion_clear H.
      rewrite <- from_to_gstring in H0.
      assumption.
    Qed.
    
  End LQwProperties.
  
  (** * Right-to-left defined lists *)
  
  Module IList.
    
    Inductive ilist : Type :=
    | inil  : ilist 
    | icons : ilist -> AtSy -> ilist.
    
    Delimit Scope ilist_scope with ilist.
    Open Scope ilist_scope.
    
    Notation "<[]" := inil.
    Infix "<::" := icons (at level 60, right associativity).
    
    (** * Characterization of [ilist] as an instance of [OrderedType] *)
  
    Inductive ilist_eq : ilist -> ilist -> Prop :=
    | ilist_eq_nil : ilist_eq <[] <[]
    | ilist_eq_icons :
      forall a a' l l', _eq a a' -> ilist_eq l l' ->
                        ilist_eq (icons l a) (icons l' a').
    
    Lemma ilist_eq_leibniz : forall x y,
                               ilist_eq x y -> x = y.
    Proof.
      induction 1;auto.
      rewrite IHilist_eq.
      destruct H.
      inv H.
    Qed.
    
    Inductive ilist_lt : ilist -> ilist -> Prop :=
    | ilist_lt_inil :
      forall a l, ilist_lt inil (icons l a)
    | ilist_lt_icons_1 :
      forall a a' l l', _lt a a' -> ilist_lt (icons l a) (icons l' a')
    | list_lt_cons_2 :
      forall a a' l l', _eq a a' -> ilist_lt l l' ->
                        ilist_lt (icons l a) (icons l' a').
    
    Program Instance ilist_Equivalence : Equivalence (ilist_eq).
    Next Obligation.
      repeat red.
      induction x.
      econstructor.
      constructor;auto with typeclass_instances.
    Qed.
    Next Obligation.
      repeat red.
      induction 1;intros.
      constructor.
      constructor;auto.
    Qed.
    Next Obligation.
      repeat red.
      induction 1;intros.
      assumption.
      apply ilist_eq_leibniz in H1.
      symmetry in H1.
      subst.
      constructor;auto.
    Qed.
    
    Hint Constructors ilist_lt : ilist_scope.
    
    Program Instance ilist_StrictOrder :
      StrictOrder ilist_lt ilist_eq.
    Next Obligation.
      red.
      induction x;destruct y;intros;auto with ilist_scope.
      inversion_clear H0;auto with ilist_scope.
      inversion_clear H.
      inversion_clear H0.
      inversion_clear H.
      constructor.
      order.
      constructor.
      rewrite H0.
      assumption.
      inversion_clear H.
      constructor 2.
      rewrite <- H1.
      assumption.
      constructor 3.
      order.
      eapply IHx;eauto.
    Qed.
    Next Obligation.
      revert x y H.
      induction 1.
      intro.
      inversion H.
      intro.
      inversion H0.
      subst.
      order.
      intro.
      inversion_clear H1.
      apply IHilist_lt.
      assumption.
    Qed.
    
    Program Instance ilist_UsualStrictOrder :
      OrderedType.StrictOrder (@ilist_lt ) (@Logic.eq _).
    Next Obligation. (* irreflexivity *)
      intro E; inversion E; subst; clear E.
      revert y H; induction y; intro H; inversion H; subst; auto; order.
    Defined.
  
    Fixpoint ilist_compare (x y : ilist) :=
      match x, y with
        | <[], <[] => Eq
        | <[], _<::_ => Lt
        | _<::_, <[] => Gt
        | l<::a, l'<::a' =>
            match a =?= a' with
              | Eq => ilist_compare l l'
              | Lt => Lt
              | Gt => Gt
            end
      end.
    
    Program Instance ilist_OrderedType: OrderedType (ilist) := 
      { _eq := ilist_eq ;
        _lt := ilist_lt;
        _cmp := ilist_compare;
        OT_Equivalence := ilist_Equivalence;
        OT_StrictOrder := ilist_StrictOrder 
      }.
    Next Obligation.
      revert y; induction x; destruct y; simpl; try (do 2 constructor).
      destruct (compare_dec a a0); try do 2 constructor; auto.
      destruct (IHx y); constructor.
      constructor 3; auto.
      constructor 2; auto.
      constructor 3.
      rewrite H.
      reflexivity.
      assumption.
    Qed.
    
    Program Instance ilist_UsualOrderedType : UsualOrderedType ilist := 
      {
        SOT_lt := ilist_lt (*_lt Logic.eq ;*);
        SOT_cmp := ilist_compare;
        SOT_StrictOrder := ilist_UsualStrictOrder
      }.
    Next Obligation.
      revert y; induction x; destruct y; simpl; try (do 2 constructor).
      destruct (compare_dec a a0); try do 2 constructor; auto.
      destruct (IHx y); constructor.
      constructor 3; auto.
      rewrite H0.
      destruct a.
      destruct a0.
      destruct H.
      inv H.
      constructor 3; auto; symmetry; auto.
    Defined.
    
    Program Instance icons_proper : Proper (_eq ==> _eq ==> _eq) icons.
    Next Obligation.
      repeat red.
      intros;constructor;auto with ilist_scope typeclass_instances.
    Qed.
    
    Reserved Notation "x <++ y" (at level 60,right associativity).
    Fixpoint ilist_app (a b:ilist){struct b} : ilist :=
      match b with
        | <[] => a 
        | x<::y => (a <++ x)<::y
      end where "x <++ y" := (ilist_app x y).
    
    Instance ilist_app_proper : Proper (_eq ==> _eq ==> _eq) ilist_app.
    Proof.
      repeat red.
      induction 2.
      normalize_notations;auto with typeclass_instances.
      constructor;auto.
    Qed.
    
    Lemma ilist_ilist_nil_app : forall l, l === <[] <++ l.
    Proof.
      induction l;simpl;auto.
      constructor;auto.
    Qed.
    
    Lemma ilist_ilist_app_inil : forall l,  <[] <++ l === l.
    Proof.
      induction l;simpl;auto.
      constructor;auto.
    Qed.
    
    Lemma ilist_inil_split : 
      forall l1 l2, 
        <[] === l1 <++ l2 -> l1 === <[] /\ l2 === <[].
    Proof.
      induction l1;destruct l2;split;intros;simpl in *;auto.
      inversion_clear H.
      inversion H.
      inversion H.
    Qed.
    
    Lemma ilist_neq_ilist_icons : 
      forall l a,
        ~(l === l<::a).
    Proof.
      induction l;simpl;intros;intro.
      inversion H.
      inversion_clear H.
      specialize IHl with a.
      contradiction.
    Qed.
    
    Lemma ilist_not_inil_ex : 
      forall l,
        l =/= <[] -> exists a,exists l', l === l'<::a.
    Proof.
      induction l;intros.
      elim H;auto.
      exists a.
      exists l;auto.
    Qed.
    
    Hint Resolve 
         ilist_ilist_nil_app
         ilist_ilist_app_inil
         ilist_inil_split 
         ilist_neq_ilist_icons 
         ilist_not_inil_ex : ilist_scope.
    
    Lemma ilist_ilist_app_assoc : 
      forall w1 w2 w3, 
        w1 <++ (w2 <++ w3) === (w1 <++ w2) <++ w3.
    Proof.
      induction w3;simpl;auto.
      rewrite IHw3;auto.
    Qed.
    
    Lemma ilist_icons_ilist_app_2 : 
      forall u u0 a, 
        (u <++ u0)<::a === u <++ (u0 <::a).
    Proof.
      induction u0;simpl;intros;auto.
    Qed.
    
    Lemma ilist_icons_ilist_app : 
      forall x y w, 
        (x<::y) <++ w === x <++ ((<[]<::y) <++ w).
    Proof.
      induction x;
        intros;simpl;auto with ilist_scope.
      destruct w;simpl;auto with ilist_scope.
      constructor;auto.
      normalize_notations.
      rewrite ilist_ilist_app_assoc.
      simpl.
      reflexivity.
    Qed.
    
    Hint Resolve 
         ilist_ilist_app_assoc
         ilist_icons_ilist_app_2
         ilist_icons_ilist_app : ilist_scope.
    
    Reserved Notation "x ^p< n" (at level 60). 
    Fixpoint IWordPower (x:ilist)(n:nat) := 
      match n with
        | O => <[]
        | S n => (x ^p< n) <++ x
      end where "x ^p< n" := (IWordPower x n).
    
    Instance IWordPower_proper : Proper (_eq ==> _eq ==> _eq) IWordPower.
    Proof.
      repeat red.
      induction x0;simpl;intros.
      rewrite <-H0.
      simpl;auto with ilist_scope.
      constructor.
      rewrite <- H0.
      simpl.
      eapply ilist_app_proper;auto with typeclass_instances.
      apply IHx0;auto.
    Qed.
    
    (** lists to ilists conversion function *)
    
    Reserved Notation "<@ a" (at level 50).
    Fixpoint list_to_ilist (a:list AtSy) : ilist :=
      match a with
        | nil => <[]
        | a::xs => (<[]<::a) <++ (<@ xs)
      end where "<@ a" := (list_to_ilist a).
    
    Instance list_to_ilist_m : Proper (_eq ==> _eq) list_to_ilist.
    Proof.
      repeat red.
      induction 1 .
      reflexivity.
      simpl.
      normalize_notations.
      rewrite H.
      rewrite IHlist_eq.
      reflexivity.
    Qed.
    
    (** ilists to lists conversion function *)
    Reserved Notation "@> a" (at level 50).
    Fixpoint ilist_to_list (a:ilist) : list AtSy :=
      match a with
        | <[] => nil (A:=AtSy)
        | l<::x => app (@> l) (x::nil)
      end where "@> a" := (ilist_to_list a).
  
    Instance ilist_to_list_m : Proper (_eq ==> _eq) ilist_to_list.
    Proof.
      repeat red.
      induction 1 .
      reflexivity.
      simpl.
      normalize_notations;auto with typeclass_instances.
      induction IHilist_eq.
      constructor;auto.
      constructor.
      do 2 rewrite <- app_comm_cons.
      constructor;auto.
    Qed.
    
    Theorem exListFromIlist : forall w, exists w', w' === <@ w.
    Proof.
      induction w.
      simpl.
      exists inil;reflexivity.
      simpl.
      destruct IHw as [w' Hw'].
      exists (ilist_app (icons inil a) w').
      rewrite <- Hw'.
      reflexivity.
    Qed.
    
    (** General rewriting support por [append] and [cons] for lists. *)
    
    Instance app_m : Proper (_eq ==> _eq ==> _eq) (@app AtSy).
    Proof.
      repeat red.
      induction 1;simpl;intros;auto with typeclass_instances.
      normalize_notations.
      constructor;auto.
    Qed.
    
    Instance cons_m : Proper (_eq ==> _eq ==> _eq) (@cons AtSy).
    Proof.
      repeat red.
      induction 1;simpl;intros;auto with typeclass_instances.
      constructor;auto.
      constructor;auto.
    Qed.
    
    Theorem exIlistFromList : forall w', exists w, w === @> w'.
    Proof.
      induction w'.
      simpl.
      exists (@nil AtSy).
      reflexivity.
      simpl.
      destruct IHw' as [w Hw].
      exists (app w (a::nil)).
      rewrite <- Hw;auto.
    Qed.
    
    (** Correctness of conversion operations between lists and ilists *)
    
    Lemma IlistFromListConc : 
      forall w w',
        <@ (w ++ w') === (<@ w) <++ (<@ w').
    Proof.
      induction w.
      intro.
      simpl.
      rewrite ilist_ilist_app_inil.
      reflexivity.
      intros.
      simpl.
      rewrite (IHw w').
      rewrite ilist_ilist_app_assoc.
      reflexivity.
    Qed.
    
    Lemma ListFromIlistConc : 
      forall  w' w'', 
        @> (w' <++ w'') === app (@> w') (@> w'').
    Proof.
      induction w''.
      simpl.
      rewrite <- app_nil_end.
      reflexivity.
      simpl.
      rewrite IHw''.
      rewrite <- app_assoc.
      reflexivity.
    Qed.
    
    Theorem  IlistFromList : 
      forall w', 
        <@ (@> w') === w'.
    Proof.
      induction w'.
      simpl.
      reflexivity.
      simpl.
      rewrite IlistFromListConc.
      rewrite IHw'.
      simpl.
      reflexivity.
    Qed.
  
    Theorem ListFromIlist : 
      forall w, @> (<@ w) === w.
    Proof.
      induction w.
      simpl.
      reflexivity.
      simpl.
      rewrite ListFromIlistConc.
      simpl.
      rewrite IHw;auto.
    Qed.
    
    Lemma nil2inil : forall w, w === nil -> <@ w === <[].
    Proof.
      intros w H;rewrite H;simpl.
      auto.
    Qed.
    
    Lemma inil2nil : forall w,  w === <[] -> @> w === nil.
    Proof.
      intros.
      rewrite H;simpl.
      reflexivity.
    Qed.
    
    Lemma not_nil2inil : forall w, w =/= nil -> <@ w =/= <[].
    Proof.
      intros.
      intro.
      apply inil2nil in H0.
      rewrite ListFromIlist in H0.
      contradiction.
    Qed.
    
    Lemma eq_app_iapp : 
      forall w u v,
        w === app u v -> <@ w === <@ u <++ <@ v.
    Proof.
      intros w u v.
      revert v u w.
      induction v;simpl;intros.
      rewrite <- app_nil_end in H.
      rewrite <- H.
      auto.
      replace (app u (a::v)) with (app (app u (a::nil)) v) in H.
      apply IHv in H.
      rewrite H.
      rewrite IlistFromListConc.
      simpl.
      rewrite ilist_ilist_app_assoc.
      simpl.
      reflexivity.
      rewrite app_ass.
      simpl.
      reflexivity.
    Qed.

    Hint Resolve
         nil2inil
         inil2nil
         IlistFromListConc
         ListFromIlistConc
         ListFromIlist
         IlistFromList
         eq_app_iapp
         not_nil2inil : ilist_scope.
    
    Lemma ilist_eq_dec : 
      forall l1 l2:ilist,
        {l1 === l2}+{l1 =/= l2}.
    Proof.
      intros.
      case_eq(compare l1 l2);intros.
      left.
      apply compare_2 in H.
      assumption.
      right.
      apply compare_1 in H.
      apply lt_not_eq in H.
      assumption.
      apply compare_3 in H.
      apply gt_not_eq in H.
      right;auto.
    Qed.
    
    (** * Some standard functions over [list], adaped to [ilist] *)
    
    (** Function for element containance in a [ilist] *)
    
    Fixpoint iIn (a:AtSy) (l:ilist) : Prop :=
      match l with
        | inil => False
        | m<::b => b === a \/ iIn a m
      end.
    
    (** The length of an [ilist] *)
    
    Fixpoint ilength(w:ilist):nat :=
      match w with 
        | inil => 0
        | icons y a => S (ilength y)
      end.
    
    Instance ilength_m : Proper (_eq ==> eq) ilength.
    Proof.
      repeat red.
      induction x;simpl;intros.
      inversion H.
      simpl.
      reflexivity.
      inversion_clear H.
      simpl.
      apply IHx in H1.
      rewrite H1.
      reflexivity.
    Qed.
    
    (**  Properties of the [ilength] function. *)
    
    Lemma ilength_sum_one : 
      forall l' a,
        ilength ((<[] <:: a) <++ l') = S (ilength l').
    Proof.
      induction l';simpl;intros.
      reflexivity.
      rewrite IHl'.
      reflexivity.
    Qed.
    
    Lemma ilength_sum : 
      forall l l',
        ilength (l <++ l') = ilength l + ilength l'.
    Proof.
      induction l;simpl;intros;auto with arith.
      rewrite <- ilist_ilist_nil_app.
      reflexivity.
      rewrite ilist_icons_ilist_app.
      rewrite IHl.
      rewrite ilength_sum_one;auto with arith.
    Qed.
    
    (** Extra properties of the [iapp] function. *)
    
    Lemma iapp_inv_head:
      forall l l1 l2, l1 <++ l === l2 <++ l -> l1 === l2.
    Proof.
      induction l; simpl; auto. 
      intros.
      inversion_clear H.
      apply IHl in H1.
      assumption.
    Qed.
    
    Lemma iapp_inv_left : 
      forall l l1 l2,
        l <++ l1 === l <++ l2 -> l1 === l2.
    Proof.
      intros l l1 l2; revert l1 l2 l.
      induction l1 as [ | x1 l1]; destruct l2 as [ | x2 l2];
      simpl; auto; intros l H.
      absurd (ilength ((l <++ x2)<::l2) <= ilength l).
      simpl;intro.
      rewrite ilength_sum in H0.
      abstract omega.
      rewrite <- H;auto with arith.
      absurd (ilength ((l <++ x1)<::a) <= ilength l).
      simpl;intro.
      rewrite ilength_sum in H0.
      abstract omega.
      rewrite H;auto with arith.
      apply  ilist_eq_leibniz in  H.
      injection H;intros.
      constructor;subst;auto with typeclass_instances.
      eapply l1 with l.
      rewrite H1.
      reflexivity.
    Qed.

  (* END ILISTS *)
  End IList.

  Export IList.

End GL.