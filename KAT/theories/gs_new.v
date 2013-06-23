Require Export kat_alph atoms ProofIrrelevance.

Ltac inv c := inversion c;try (discriminate||congruence).
Ltac gl_goal := split;red;intros.


Module GS(X:KAT_Alph).

  Export X.

  Notation atom := (ord (pow2 ntests)).
  Notation prim_test := (ord (ntests)).
  Definition AtSy := (atom*Z)%type.

  (** * Type of tests *)

  Inductive test : Type :=
  | ba0 : test
  | ba1 : test
  | baV : prim_test -> test
  | baN : test -> test
  | baAnd : test -> test -> test
  | baOr : test -> test -> test.

  Notation "`` x" := (baV x)(at level 35).
  Notation "! x" := (baN x)(at level 35).
  Infix "`+" := baOr(at level 45).
  Infix "`·" := baAnd(at level 45).


  (** Burocratic definitions and properties that make [test] and odered typ *)

  Inductive test_eq : test -> test -> Prop :=
  | test_eq_ba0 : test_eq ba0 ba0
  | test_eq_ba1 : test_eq ba1 ba1
  | test_eq_baV : forall x y, x === y -> test_eq (baV x) (baV y)
  | test_eq_baN : forall x y:test, test_eq x y -> test_eq (baN x) (baN y)
  | test_eq_baAnd : forall x₁ x₂ y₁ y₂, test_eq x₁ x₂ -> test_eq y₁ y₂ ->
                                        test_eq (baAnd x₁ y₁) (baAnd x₂ y₂)
  | test_eq_baOr : forall x₁ x₂ y₁ y₂, test_eq x₁ x₂ -> test_eq y₁ y₂ ->
                                        test_eq (baOr x₁ y₁) (baOr x₂ y₂).

  Proposition leibniz_test:
    forall x y:test,
      test_eq x  y -> x = y.
  Proof.
    induction 1;intros;subst;auto.
    apply ord_Eq_unique in H.
    rewrite H.
    reflexivity.
  Qed.

  Inductive test_lt : test -> test -> Prop :=
    test_lt_ba0_ba1 : test_lt ba0 ba1
  | test_lt_ba0_baV : forall y1 , test_lt ba0 (baV y1)
  | test_lt_ba0_baN : forall y1 : test, test_lt ba0 (baN y1)
  | test_lt_ba0_baAnd : forall y1 y2 : test, test_lt ba0 (baAnd y1 y2)
  | test_lt_ba0_baOr : forall y1 y2 : test, test_lt ba0 (baOr y1 y2)
  | test_lt_ba1_baV : forall y1 , test_lt ba1 (baV y1)
  | test_lt_ba1_baN : forall y1 : test, test_lt ba1 (baN y1)
  | test_lt_ba1_baAnd : forall y1 y2 : test, test_lt ba1 (baAnd y1 y2)
  | test_lt_ba1_baOr : forall y1 y2 : test, test_lt ba1 (baOr y1 y2)
  | test_lt_baV_1 : forall x1 y1 , x1 <<< y1 -> test_lt (baV x1) (baV y1)
  | test_lt_baV_baN : forall x1 (y1 : test), test_lt (baV x1) (baN y1)
  | test_lt_baV_baAnd : forall x1 (y1 y2 : test),
                        test_lt (baV x1) (baAnd y1 y2)
  | test_lt_baV_baOr : forall x1 (y1 y2 : test),
                       test_lt (baV x1) (baOr y1 y2)
  | test_lt_baN_1 : forall x1 y1 : test,
                    test_lt x1 y1 -> test_lt (baN x1) (baN y1)
  | test_lt_baN_baAnd : forall x1 y1 y2 : test,
                        test_lt (baN x1) (baAnd y1 y2)
  | test_lt_baN_baOr : forall x1 y1 y2 : test, test_lt (baN x1) (baOr y1 y2)
  | test_lt_baAnd_1 : forall x1 y1 x2 y2 : test,
                      test_lt x1 y1 -> test_lt (baAnd x1 x2) (baAnd y1 y2)
  | test_lt_baAnd_2 : forall x1 y1 x2 y2 : test,
                      test_eq x1 y1 ->
                      test_lt x2 y2 -> test_lt (baAnd x1 x2) (baAnd y1 y2)
  | test_lt_baAnd_baOr : forall x1 x2 y1 y2 : test,
                         test_lt (baAnd x1 x2) (baOr y1 y2)
  | test_lt_baOr_1 : forall x1 y1 x2 y2 : test,
                     test_lt x1 y1 -> test_lt (baOr x1 x2) (baOr y1 y2)
  | test_lt_baOr_2 : forall x1 y1 x2 y2 : test,
                     test_eq x1 y1 ->
                     test_lt x2 y2 -> test_lt (baOr x1 x2) (baOr y1 y2).

  Fixpoint test_cmp (x y : test) : comparison :=
  match x with
  | ba0 =>
      match y with
      | ba0 => Eq
      | ba1 => Lt
      | baV _ => Lt
      | baN _ => Lt
      | baAnd _ _ => Lt
      | baOr _ _ => Lt
      end
  | ba1 =>
      match y with
      | ba0 => Gt
      | ba1 => Eq
      | baV _ => Lt
      | baN _ => Lt
      | baAnd _ _ => Lt
      | baOr _ _ => Lt
      end
  | baV x1 =>
      match y with
      | ba0 => Gt
      | ba1 => Gt
      | baV y1 => ord_Cmp (ntests) x1 y1
      | baN _ => Lt
      | baAnd _ _ => Lt
      | baOr _ _ => Lt
      end
  | baN x1 =>
      match y with
      | ba0 => Gt
      | ba1 => Gt
      | baV _ => Gt
      | baN y1 => test_cmp x1 y1
      | baAnd _ _ => Lt
      | baOr _ _ => Lt
      end
  | baAnd x1 x2 =>
      match y with
      | ba0 => Gt
      | ba1 => Gt
      | baV _ => Gt
      | baN _ => Gt
      | baAnd y1 y2 =>
          match test_cmp x1 y1 with
          | Eq => test_cmp x2 y2
          | Lt => Lt
          | Gt => Gt
          end
      | baOr _ _ => Lt
      end
  | baOr x1 x2 =>
      match y with
      | ba0 => Gt
      | ba1 => Gt
      | baV _ => Gt
      | baN _ => Gt
      | baAnd _ _ => Gt
      | baOr y1 y2 =>
          match test_cmp x1 y1 with
          | Eq => test_cmp x2 y2
          | Lt => Lt
          | Gt => Gt
          end
      end
  end.
  
  Functional Scheme test_cmp_ind := Induction for test_cmp Sort Prop.
  Functional Scheme test_cmp_rec := Induction for test_cmp Sort Set.

  Global Instance test_eq_refl : Reflexive test_eq.
  Proof.
    repeat red;intros;induction x;try constructor;auto.
  Qed.

  Global Instance test_eq_symm : Symmetric test_eq.
  Proof.
    repeat red.
    induction 1;try reflexivity.
    - constructor;auto. 
    - constructor;auto.
    - constructor;auto.
    - constructor;auto.
  Qed.

  Global Instance test_eq_trans : Transitive test_eq.
  Proof.
    repeat red.
    induction x;intros.
    - inv H.
    - inv H.
    - inv H;subst;inv H0;subst;constructor.
      rewrite H2;auto.
    - inv H;subst. inv H0;subst. constructor;eauto.
    - inv H;subst;inv H0;subst. constructor;eauto.
    - inv H;subst;inv H0;subst. constructor;eauto.
  Qed.

  Global Instance test_eq_Equiv : Equivalence test_eq.
  Proof.
    constructor;autotc.
  Qed.
  
  (** Auxiliary lemmas for test_cmp *)
  Lemma test_cmp_eq_leibniz :
    forall x y, test_cmp x y = Eq -> x = y.
  Proof.
    intros.
    functional induction (test_cmp x y);
      first [reflexivity|discriminate|auto].
    apply compare_2 in H.
    apply ord_Eq_unique in H.
    rewrite H;auto.
    apply IHc in H;subst;auto.
    apply IHc in e1;apply IHc0 in H;subst;auto.
    apply IHc in e1;apply IHc0 in H;subst;auto.
  Qed.

  Lemma test_cmp_lt :
    forall x y, test_cmp x y = Lt -> test_lt x y.
  Proof.
    intros.
    functional induction (test_cmp x y);
      try (now constructor||discriminate).
    apply compare_1 in H;auto.
    constructor;auto.
    constructor.
    apply IHc;auto.
    apply IHc0 in H.
    apply test_lt_baAnd_2;auto.
    apply test_cmp_eq_leibniz in e1;subst;auto.
    reflexivity.
    constructor.
    apply IHc;auto.
    apply test_cmp_eq_leibniz in e1;subst.
    apply test_lt_baOr_2;auto.
    reflexivity.
    constructor.
    apply IHc;auto.
  Qed.

  Lemma test_cmp_gt :
    forall x y, test_cmp x y = Gt -> test_lt y x.
  Proof.
    intros.
    functional induction (test_cmp x y);
      try (now constructor||discriminate).
    apply compare_3 in H;auto.
    constructor;auto.
    constructor.
    apply IHc;auto.
    apply IHc0 in H.
    apply test_lt_baAnd_2;auto.
    apply test_cmp_eq_leibniz in e1;subst;auto.
    reflexivity.
    constructor.
    apply IHc;auto.
    apply test_cmp_eq_leibniz in e1;subst.
    apply test_lt_baOr_2;auto.
    reflexivity.
    constructor.
    apply IHc;auto.
  Qed.
    
  Proposition test_lt_not_refl :
    forall y, ~test_lt y y.
  Proof.
    intros;intro.
    dependent induction H.
    order.
    elim IHtest_lt.
    elim IHtest_lt.
    elim IHtest_lt.
    elim IHtest_lt.
    elim IHtest_lt.
  Qed.

  Global Program Instance testUOrd : UsualOrderedType test :=
    { SOT_lt := test_lt ; SOT_cmp := test_cmp}.
  Next Obligation.
    constructor.
    - repeat red;induction x;intros;destruct y;try now(inv H);try now(inv H0;constructor).
      + inv H0;subst;econstructor;inv H;subst;transitivity o0;auto. 
      + inv H0;subst;inv H;try (now constructor);subst. constructor. eapply IHx;eauto.
      + inv H0;subst;inv H;subst.
        * constructor;eapply IHx1;eauto. 
        * constructor;apply leibniz_test in H5;subst;assumption.
        * { apply leibniz_test in H3;subst;inv H;subst.    
            - constructor;eauto. 
            - constructor;eauto. 
          }
        * apply leibniz_test in H6;subst. apply test_lt_baAnd_2;auto;eapply IHx2;eauto.
        * { inv H0;subst;inv H;subst. 
            - constructor;eauto.
            - apply leibniz_test in H5;subst. constructor;eauto.
          }
        * { inv H;subst. 
            - apply leibniz_test in H4;subst. constructor. 
            - constructor. 
          }
      + inv H;subst.
        * { inv H0;subst.
            - constructor;eapply IHx1;eauto.
            - apply leibniz_test in H4. subst. apply test_lt_baOr_1;auto. 
          }
        * { apply leibniz_test in H4;subst. inv H0;subst.
            - constructor;auto.
            - apply test_lt_baOr_2;eauto. 
          }
    - intros;intro. rewrite H0 in H. pose proof test_lt_not_refl y. contradiction. 
  Defined.
  Next Obligation.
    - case_eq(test_cmp x y);constructor.
     + apply test_cmp_eq_leibniz;auto.
     + apply test_cmp_lt;auto.
     + apply test_cmp_gt;auto.
  Defined.

  (** * Boolean evaluation of tests wrt. atoms. *)

  (* begin show *)
  Function evalT(a:atom)(x:test){struct x} : bool :=
    match x with
      | ba0 => false
      | ba1 => true
      | baV b => nth_bit _ a b
      | baN a1 => negb (evalT a a1)
      | baAnd a1 a2 => andb (evalT a a1) (evalT a a2)
      | baOr a1 a2 => orb (evalT a a1) (evalT a a2)
    end.
  (* end show*)
  
  (** * Type [gstring] of Guarded Strings *) 

  Inductive gstring : Type :=
  | gs_end  : atom -> gstring
  | gs_conc : atom -> Z -> gstring -> gstring.

  (** Bureocratic definitions and properties that characterize [gstring] as an ordered type *)

  Inductive gstring_eq : gstring -> gstring -> Prop :=
    gstring_eq_gs_end : forall x1 y1 : atom,
                        x1 === y1 -> gstring_eq (gs_end x1) (gs_end y1)
  | gstring_eq_gs_conc : forall (x1 y1 : atom) (x2 y2 : Z) (x3 y3 : gstring),
                         x1 === y1 ->
                         x2 === y2 ->
                         gstring_eq x3 y3 ->
                         gstring_eq (gs_conc x1 x2 x3) (gs_conc y1 y2 y3).

  Hint Constructors gstring_eq.

  Structure can_gstring := 
    { Gs :> Type;
      Gs_end : atom -> Gs;
      Gs_c : atom -> Z -> Gs -> Gs;
      Gs_Eq : Gs -> Gs -> Prop;
      Gs_Eq_equiv : Equivalence Gs_Eq;
      Gs_Eq_def : forall x y:Gs, Gs_Eq x y -> x = y
    }.

  Proposition leibniz_gstring :
    forall x y:gstring, gstring_eq x y -> x = y.
  Proof.
    induction 1.
    - ord_eq_un H;auto.
    - ord_eq_un H;inv H0.
  Qed.

  Instance gstring_eq_equiv : Equivalence gstring_eq.
  Proof.
    constructor;repeat red.
    - intros;induction x;auto.
    - induction 1;inv H;auto.
    - induction x.
      + intros;inv H;subst;ord_eq_un H2;auto.
      + intros;inv H;subst;ord_eq_un H4;inv H6;subst;inv H0;subst;
        constructor;auto;eapply IHx;eauto.
  Qed.

  Inductive gstring_lt : gstring -> gstring -> Prop :=
    gstring_lt_gs_end_1 : forall x1 y1 : atom,
                            x1 <<< y1 -> gstring_lt (gs_end x1) (gs_end y1)
  | gstring_lt_gs_end_gs_conc : forall (x1 y1 : atom) 
                                       (y2 : Z) (y3 : gstring),
                                  gstring_lt (gs_end x1) (gs_conc y1 y2 y3)
  | gstring_lt_gs_conc_1 : forall (x1 y1 : atom) (x2 y2 : Z)
                                  (x3 y3 : gstring),
                             x1 <<< y1 ->
                             gstring_lt (gs_conc x1 x2 x3) (gs_conc y1 y2 y3)
  | gstring_lt_gs_conc_2 : forall (x1 y1 : atom) (x2 y2 : Z)
                                  (x3 y3 : gstring),
                             x1 === y1 ->
                             x2 <<< y2 ->
                             gstring_lt (gs_conc x1 x2 x3) (gs_conc y1 y2 y3)
  | gstring_lt_gs_conc_3 : forall (x1 y1 : atom) (x2 y2 : Z)
                                  (x3 y3 : gstring),
                             x1 === y1 ->
                             x2 === y2 ->
                             gstring_lt x3 y3 ->
                             gstring_lt (gs_conc x1 x2 x3) (gs_conc y1 y2 y3).

  Instance gstring_lt_trans : Transitive gstring_lt.
  Proof.
    repeat red.
    induction x;intros.
    - inv H;inv H0;subst.
      + injection H5;intros;subst;constructor;order.
      + constructor.
      + constructor.
      + constructor.
      + constructor.
    - inv H;subst;inv H0;subst.
      + constructor;order.
      + ord_eq_un H6. constructor;order.
      + ord_eq_un H4. inv H7;subst;constructor;order.
      + ord_eq_un H5. constructor;auto.
      + ord_eq_un H5;inv H7;subst;constructor 4;order.
      + ord_eq_un H5;inv H4;inv H8;subst;constructor 4;order.
      + ord_eq_un H4;inv H6;subst;constructor;auto.
      + ord_eq_un H4;inv H6;inv H8;subst;constructor 4;auto.
      + ord_eq_un H4;inv H6;inv H5;inv H9;subst;constructor 5;auto;
        eapply IHx;eauto.
  Qed.


  Fixpoint gstring_cmp (x y : gstring) : comparison :=
    match x with
      | gs_end x1 =>
        match y with
          | gs_end y1 => ord_Cmp _ x1 y1
          | gs_conc _ _ _ => Lt
        end
      | gs_conc x1 x2 x3 =>
        match y with
          | gs_end _ => Gt
          | gs_conc y1 y2 y3 =>
            match ord_Cmp _ x1 y1 with
              | Eq =>
                match compare x2 y2 with
                  | Eq => gstring_cmp x3 y3
                  | Lt => Lt
                  | Gt => Gt
                end
              | Lt => Lt
              | Gt => Gt
            end
        end
    end.

  Functional Scheme gstring_cmp_ind := Induction for gstring_cmp Sort Prop.
  Functional Scheme gstring_cmp_rec := Induction for gstring_cmp Sort Set.

  Proposition gstring_cmp_eq_leibniz : 
    forall x y, gstring_cmp x y = Eq -> x = y.
  Proof.
    intros.
    functional induction (gstring_cmp x y);try discriminate.
    + apply compare_2 in H. ord_eq_un H;auto.
    + apply compare_2 in e1; apply compare_2 in e2. 
      ord_eq_un e1. inv e2. subst. apply IHc in H;subst;reflexivity.
  Qed.

  Proposition gstring_cmp_lt :
    forall x y, gstring_cmp x y = Lt -> gstring_lt x y.
  Proof.
    intros.
    functional induction (gstring_cmp x y);try (now (discriminate||constructor)).
    + apply compare_1 in H. constructor. order. 
    + apply compare_2 in e1; apply compare_2 in e2;subst;inv e1;inv e2;subst.
      constructor 5;auto.
    + apply compare_2 in e1;apply compare_1 in e2;inv e1;subst;constructor 4;auto.
    + apply compare_1 in e1;constructor;auto.
  Qed.

  Proposition gstring_cmp_gt :
    forall x y, gstring_cmp x y = Gt -> gstring_lt y x.
  Proof.
    intros.
    functional induction (gstring_cmp x y);try (now (discriminate||constructor)).
    + apply compare_3 in H;constructor;auto. 
    + apply compare_2 in e1; apply compare_2 in e2;subst;inv e1;inv e2;subst.
      constructor 5;auto.
    + apply compare_2 in e1;apply compare_3 in e2;inv e1;subst;constructor 4;auto.
    + apply compare_3 in e1;constructor;auto.
  Qed.

  Instance gstring_UOT : UsualOrderedType gstring := 
    { SOT_lt := gstring_lt ; SOT_cmp := gstring_cmp}.
  Proof.
    constructor;autotc.
    - induction 1;intros.
      + intro H0;inv H0;subst;order.
      + intro H0;inv H0.
      + intro H0;inv H0;subst;order.
      + intro H1;inv H1;subst;order.
      + intro H2;inv H2;subst;order.
    - intros. case_eq(gstring_cmp x y);intro;constructor.
      + apply gstring_cmp_eq_leibniz;auto.
      + apply gstring_cmp_lt;auto.
      + apply gstring_cmp_gt;auto.
  Defined.

  Lemma list_leibniz :
    forall l1 l2:list (atom*Z),
      l1 === l2 -> l1 = l2.
  Proof.
    induction 1;try congruence.
    normalize_notations.
    subst.
    destruct a;destruct a'.
    f_equal.
    destruct H.
    normalize_notations. clear H0. inv H1. 
  Qed.

  (** * First and last atom of a guarded string *)

  Fixpoint last gs :=
    match gs with
      | gs_end k => k
      | gs_conc _ _ k => last k
    end.
  Notation "↓ g" := (last g)(at level 44).

  Fixpoint first gs :=
    match gs with
      | gs_end k => k
      | gs_conc k _ _ => k
    end.
  Notation "↑ g" := (first g)(at level 44).

  Notation "⌜  a  , b ⌝:: v" := (gs_conc a b v)(at level 45).
  Notation "⌜  a ⌝" := (gs_end a)(at level 45).
  
  (** Two guarded strings are [compatible] if the last atom of the
      first guarded string is the same as the first atom of the
      second. *)

  Definition compatible gs1 gs2 := last gs1 = first gs2.
  Infix "≀" := (compatible)(at level 10).

  (** Properties of compatibility *)

  Lemma compatible_gs_conc :
    forall g1 g2 x xs,
      compatible g1 g2 -> compatible (gs_conc x xs g1) g2.
  Proof.
    auto.
  Qed.

  Lemma compatible_last :
    forall g1 g2,
      compatible g1 g2 -> compatible (gs_end (last g1)) g2.
  Proof.
    auto.
  Qed.

  Definition compatible_rewrite (gs1 gs2:gstring)(H:compatible gs1 gs2)
              (x:atom)(k:Z)(t:gstring)(L:gs1 = gs_conc x k t) :
    compatible t gs2.
  Proof.
    subst.
    auto.
  Defined.

  (** * Fusion product for guarded strings. *)

  Fixpoint fusion_prod gs1 gs2 (H:compatible gs1 gs2) : gstring :=
    match gs1 as x return gs1=x -> gstring with
      | gs_end _ =>  
          fun H:(gs1 = gs_end _) => gs2
      | gs_conc k s t =>  
          fun H0:(gs1 = gs_conc k s t) => 
            gs_conc k s (fusion_prod t gs2 (compatible_rewrite gs1 gs2 H k s t H0))
    end (refl_equal gs1).

  Notation "a ⋄ b ( c )" := (fusion_prod a b c)(at level 45).

  (** Properties of fusion product. *)

  Lemma fusion_prod_compatible :
    forall a a0 s x y0 T0,
      compatible (gs_end a) (fusion_prod (gs_conc a0 s x) y0 T0) ->
      compatible (gs_end a) (gs_conc a0 s x).
  Proof.
    intros.
    simpl in H.
    unfold compatible in H.
    simpl in H.
    subst.
    unfold compatible.
    simpl.
    reflexivity.
  Qed.

  (** Decidability of the [compatible] predicate. *)

  Lemma compatible_dec : 
    forall x y,
      {compatible x y}+{~compatible x y}.
  Proof.
    unfold compatible.
    induction x;simpl;auto with typeclass_instances.
    intros.
    destruct y;simpl;intros;
    (case_eq(compare o o0);intros;
    [apply compare_2 in H | apply compare_1 in H | apply compare_3 in H]);try auto;
    try (right;intro;subst;order).
  Qed.

  (** Some more properties about [fusion_prod] *)

  Lemma fusion_prod_head :
    forall a a0 s x H,
    fusion_prod (gs_end a) (gs_conc a0 s x) H = gs_conc a0 s x.
  Proof. auto. Qed.

  Lemma fusion_prod_ext :
    forall a y H,
      fusion_prod (gs_end a) y H = y.
  Proof. auto. Qed.
  
  Lemma fusion_prod_end :
    forall x0 a T,
      fusion_prod x0 (gs_end a) T = x0.
  Proof.
    induction x0;simpl;intros.
    -  unfold compatible in T;simpl in T;subst;auto.
    - f_equal;rewrite IHx0;auto.
  Qed.

  Lemma fusion_prod_fst :
    forall x y0 T0,
      first (fusion_prod x y0 T0) = first x.
  Proof. induction x;simpl;intros;auto. Qed.

  Lemma fusion_prod_gs_conc :
    forall a s x0 x y0 T0 T,
      exists t',
        fusion_prod (gs_conc a s x0) (fusion_prod x y0 T0) T =
        gs_conc a s (fusion_prod x0 (fusion_prod x y0 T0) t').
  Proof.
    intros.

    assert(compatible x0 (fusion_prod x y0 T0)).
    unfold compatible in T |- *.
    simpl in *.
    assumption.

    red in T;simpl in T.
    exists T;simpl;f_equal.
  Qed.

  Lemma fusion_prod_gs_conc_rev :
    forall a s x0 x y0 T0 T,
      exists t',
        gs_conc a s (fusion_prod x0 (fusion_prod x y0 T0) T) =
        fusion_prod (gs_conc a s x0) (fusion_prod x y0 T0) t'.
  Proof.
    induction x0.
    simpl.
    intros.
    eexists.
    red.
    simpl.
    red in T.
    simpl in T.
    assumption.
    f_equal.
    intros.
    unfold compatible in *.
    simpl in *.
    exists T.
    f_equal.
  Qed.

  Lemma fusion_prod_gs_generic :
    forall a s x0 z T,
      exists t',
        fusion_prod (gs_conc a s x0) z T =
        gs_conc a s (fusion_prod x0 z t').
  Proof.
    intros.
    simpl.
    eexists.
    f_equal.
  Qed.

  Lemma fusion_prod_proof_inj :
    forall x z T T',
      fusion_prod x z T = fusion_prod x z T'.  
  Proof.
    induction x;simpl;intros.
    reflexivity.
    f_equal.
    unfold compatible in *;simpl in *.
    generalize(
      (compatible_rewrite (gs_conc o z x) z0 T o z x (eq_refl (gs_conc o z x)))).
    generalize(
      (compatible_rewrite (gs_conc o z x) z0 T' o z x (eq_refl (gs_conc o z x)))).
    intros.
    unfold compatible in c,c0.
    pose proof IHx z0 c0 c.
    assumption.
  Qed.

  
  Lemma fusion_prod_gs_generic_inv :
    forall a s x0 z t',
      exists T,
        gs_conc a s (fusion_prod x0 z t') =
        fusion_prod (gs_conc a s x0) z T.   
  Proof.
    intros.
    assert(compatible (gs_conc a s x0) z).
    unfold compatible in *.
    simpl in *.
    assumption.
    simpl.
    exists H.
    f_equal.
    apply fusion_prod_proof_inj.
  Qed.

  Lemma last_fusion_prod :
    forall x0 x c,
    last (fusion_prod x0 x c) = last x.
  Proof.
    induction x0;intros.
    simpl.
    reflexivity.
    erewrite <- (IHx0 x _).
    simpl.
    f_equal.
  Qed.

  Lemma fusion_prod_end_gen :
    forall a s x0 x H,
      last (fusion_prod (gs_conc a s x0) x H) = last x.
  Proof.
    intros.
    simpl.
    generalize((compatible_rewrite (gs_conc a s x0) x H a s x0
           (eq_refl (gs_conc a s x0)))).
    intro.
    rewrite last_fusion_prod.
    reflexivity.
  Qed.

  Lemma fusion_prod_same_last :
    forall x t ,
       x = fusion_prod x (gs_end (last x)) t.
  Proof.
    induction x;intros.
    simpl.
    reflexivity.
    simpl.
    rewrite IHx at 1.
    reflexivity.
  Qed.

  Lemma fusion_product_assoc_left :
    forall x x0 y0 T0 T, 
    exists T', 
      exists T'',
        (fusion_prod x0 (fusion_prod x y0 T0) T) = 
        (fusion_prod (fusion_prod x0 x T') y0 T'').        
  Proof.
    induction x0;intros.
    destruct x.
    simpl in T.
    
    assert(compatible (gs_end o) (gs_end o0)).
    unfold compatible in *.
    rewrite T.
    symmetry.
    assumption.

    exists H.
    simpl.
    exists T0.
    reflexivity.

    pose proof fusion_prod_compatible o o0 z x y0 T0 T.
    exists H.

    assert(compatible (fusion_prod (gs_end o) (gs_conc o0 z x) H) y0).
    unfold compatible in *;simpl in *.
    assumption.
    
    rewrite fusion_prod_head.
    exists T0.
    unfold compatible in T,T0;simpl in T,T0.
    generalize T.
    rewrite T.
    intro.
    rewrite fusion_prod_ext.
    reflexivity.

    assert(compatible (gs_conc o z x0) x).
    apply compatible_last in T.
    simpl in T.
    unfold compatible in T.
    simpl in T.
    red.
    simpl.
    rewrite fusion_prod_fst in T.
    assumption.
    
    exists H.
    assert(compatible x0 (fusion_prod x y0 T0)).
    unfold compatible in H.
    unfold compatible.
    simpl in H.
    rewrite fusion_prod_fst.
    assumption.
    specialize IHx0 with y0 T0 H0.    
    destruct IHx0.
    destruct H1.

    assert(compatible (fusion_prod (gs_conc o z x0) x H) y0).
    unfold compatible in *;simpl in *.
    generalize((compatible_rewrite (gs_conc o z x0) x H o z x0
           (eq_refl (gs_conc o z x0))));intro.
    rewrite last_fusion_prod.
    assumption.
    exists H2.
    simpl.
    assert(fusion_prod x0 (fusion_prod x y0 T0) H0 =
      (fusion_prod x0 (fusion_prod x y0 T0)
        (compatible_rewrite (gs_conc o z x0) (fusion_prod x y0 T0) T o z x0
           (eq_refl (gs_conc o z x0))))).
    apply fusion_prod_proof_inj.
    rewrite <- H3.
    rewrite H1.
    f_equal.
    generalize((compatible_rewrite
        (gs_conc o z
           (fusion_prod x0 x
              (compatible_rewrite (gs_conc o z x0) x H o z x0
                 (eq_refl (gs_conc o z x0))))) y0 H2 o z
        (fusion_prod x0 x
           (compatible_rewrite (gs_conc o z x0) x H o z x0
              (eq_refl (gs_conc o z x0))))
        (eq_refl
           (gs_conc o z
              (fusion_prod x0 x
                 (compatible_rewrite (gs_conc o z x0) x H o z x0
                    (eq_refl (gs_conc o z x0)))))))).
    intro.
    assert(fusion_prod x0 x x1 =
      fusion_prod x0 x
        (compatible_rewrite (gs_conc o z x0) x H o z x0
           (eq_refl (gs_conc o z x0)))).
    apply fusion_prod_proof_inj.
    revert c.
    rewrite <- H4.
    intros.
    apply fusion_prod_proof_inj.
  Qed.

  Lemma fusion_product_assoc_right :
    forall x x0 y0 T' T'', 
    exists T0, 
      exists T,
        (fusion_prod (fusion_prod x0 x T') y0 T'') =
        (fusion_prod x0 (fusion_prod x y0 T0) T).
  Proof.
    induction x0;intros.
    destruct x.
    simpl in T''.
    
    exists T''.
    assert(compatible (gs_end o) (fusion_prod (gs_end o0) y0 T'')).
    simpl.
    unfold compatible in *.
    simpl in *.
    subst.
    reflexivity.
    exists H.
    rewrite fusion_prod_ext.
    simpl.
    reflexivity.
    simpl in T''.
    exists T''.

    assert(compatible (gs_end o) (fusion_prod (gs_conc o0 z x) y0 T'')).
    unfold compatible.
    simpl.
    unfold compatible in T'.
    simpl in T'.
    assumption.
    exists H.
   
    rewrite fusion_prod_ext.
    simpl.
    reflexivity.

    assert(compatible x y0).
    unfold compatible in T'' |- *.
    rewrite fusion_prod_end_gen in T''.
    assumption.

    exists H.
    assert(compatible (gs_conc o z x0) (fusion_prod x y0 H)).
    unfold compatible.
    simpl.
    unfold compatible in T';simpl in T'.
    rewrite fusion_prod_fst.
    assumption.
    
    exists H0.
    assert(compatible x0 x).
    unfold compatible in T'.
    simpl in T'.
    apply T'.

    generalize T''.
   
    pose proof fusion_prod_gs_generic o z x0 _ H0. 
    destruct H2.
    rewrite H2.
    pose proof fusion_prod_gs_generic o z x0 x T'.
    destruct H3.
    rewrite H3.
    intro.
    pose proof fusion_prod_gs_generic o z (fusion_prod x0 x x2) y0 T''0.
    destruct H4.
    rewrite H4.
    f_equal.
    pose proof IHx0 y0 x2 x3.
    destruct H5.
    destruct H5.
    rewrite H5.
    assert(fusion_prod x y0 x4 = fusion_prod x y0 H) by 
      (apply fusion_prod_proof_inj).
    revert x5 H5.
    rewrite H6.
    intros.
    apply fusion_prod_proof_inj.
  Qed.

  Corollary fusion_prod_split_gs_end :
  forall x y a T,
    fusion_prod x y T = gs_end a ->
    x = gs_end a /\ y = gs_end a.
  Proof.
    induction x;intros.
    simpl in H;rewrite H in T.
    red in T;simpl in T.
    subst.
    split;auto.
    split.
    assert(compatible x y).
    apply T.
    pose proof IHx y a T.
    simpl in H.
    discriminate.
    assert(compatible x y).
    apply T.
    assert(fusion_prod x y T = gs_end a).
    revert H.
    induction x.
    simpl.
    intros.
    discriminate.
    simpl.
    intros.
    discriminate.
    apply IHx in H1.
    destruct H1;auto.
  Qed.

  Lemma blop :
      forall x0 y T a s x,
        fusion_prod x0 y T = gs_conc a s x ->
        (exists x',exists t',
                 x0 = gs_conc a s x' /\ fusion_prod x' y t' = x) \/
        (x0 = gs_end a /\ y = gs_conc a s x).
    Proof.
      induction x0;intros.
      simpl in *.
      right.
      split;auto.
      rewrite H in T.
      unfold compatible in T.
      simpl in T.
      subst;auto.
      simpl in H.
      injection H.
      intros.
      clear H.
      subst.
      left.
      exists x0.
      assert(compatible x0 y).
      unfold compatible in T |- *.
      simpl in T.
      assumption.
      exists H.
      split;auto.
      apply fusion_prod_proof_inj.
    Qed.
    

    

  (** Besides guarded strings, we also consider guarded sequences,
      which are lists of type [(atom*Z)]. Sequences can be mapped and
      extracted form a guarded string since sequences are guarded strings
      without their last atom.*)

  Notation seq := (list (atom*Z)).

  Fixpoint to_gstring (l:seq) (g:gstring) : gstring :=
    match l with
      | nil => g
      | x::xs => gs_conc (fst x) (snd x) (to_gstring xs g)
    end.

  Fixpoint from_gstring (g:gstring) : (list (atom*Z)) :=
    match g with
      | gs_end a => nil
      | gs_conc a p x => (a,p)::from_gstring x 
    end.

  Lemma to_gstring_app :
    forall w1 w2 x,
      to_gstring (w1 ++ w2) x = to_gstring w1 (to_gstring w2 x).
  Proof.
    induction w1;simpl;intros.
    reflexivity.
    f_equal.
    rewrite IHw1.
    reflexivity.
  Qed.
  
  Lemma from_to_gstring :
    forall w,
      w = (to_gstring (from_gstring w) (gs_end (last w))).
  Proof.
    induction w;simpl;intros.
    reflexivity.
    rewrite <- IHw.
    reflexivity.
  Qed.

  Lemma from_string_correct :
    forall g,
      g = to_gstring (from_gstring g) (gs_end (last g)).
  Proof.
    induction g;intros.
    simpl.
    reflexivity.
    simpl.
    rewrite <- IHg.
    reflexivity.
  Qed.

End GS.