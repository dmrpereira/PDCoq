Require Export kat_alph atoms gl kat.
Require Import Bool.

Module KATPdrvs(X:KAT_Alph).

  Import X.
  Module Export M := KAT(X).

  Definition lte(x y:kat) := katu x y === y.

  (** Empty word property/boolean satisfiability for kat-terms. *)
  Fixpoint ewp(t:kat)(a:atom) : bool :=
    match t with 
      | kats x => false
      | katb b => evalT a b
      | katu t1 t2 => ewp t1 a || ewp t2 a
      | katc t1 t2 => ewp t1 a && ewp t2 a
      | katst t1 => true
    end.

  Lemma ewp_dec :
    forall k a, 
      {ewp k a = false}+{ewp k a = true}.
  Proof.
    induction k;simpl;intros;intuition.
  Qed.

  Lemma ewp_cases_epsilon_false : 
    forall r a, 
      ewp r a = false -> ~In _ (kat2gl r) (gs_end a).
  Proof.
    induction r;intros.
    simpl in H.
    intro.
    inversion H0.

    simpl in H.
    intro.
    inversion H0.
    congruence.

    simpl in H.
    simpl.
    intro.
    apply Bool.orb_false_iff in H.
    destruct H.
    pose proof (IHr1 a H).
    pose proof (IHr2 a H1).
    inversion H0;contradiction.

    simpl in H.
    intro.
    apply Bool.andb_false_iff in H.
    destruct H.
    pose proof (IHr1 a H).
    inversion H0.
    apply fusion_prod_split_gs_end in H2.
    destruct H2;subst.
    contradiction.
    pose proof (IHr2 a H).
    inversion H0.
    apply fusion_prod_split_gs_end in H2.
    destruct H2;subst.
    contradiction.

    simpl in H;discriminate.
  Qed.

  Lemma ewp_cases_epsilon_true : 
    forall r a, 
      ewp r a = true -> In _ (kat2gl r) (gs_end a).
  Proof.
    induction r;intros;try discriminate.
    constructor;auto.
    apply Bool.orb_true_iff in H.
    destruct H.
    pose proof IHr1 _ H.
    left.
    assumption.
    pose proof IHr2 _ H.
    right;auto.
    apply Bool.andb_true_iff in H.
    destruct H.
    pose proof IHr1 _ H.
    pose proof IHr2 _ H0.
    assert(exists H, fusion_prod (gs_end a) (gs_end a) H = (gs_end a)).
    simpl.
    unfold compatible.
    simpl.
    exists(refl_equal a).
    reflexivity.
    destruct H3.
    rewrite <- H3.
    constructor;auto.
    econstructor 1 with O.
    simpl.
    constructor.
  Qed.

  Lemma ewp_gs_split_aux :
    forall (r1 r2:kat) a,
      ~ In gstring (gl_conc r1 r2) (gs_end a) ->
      ~ In _ (kat2gl r1) (gs_end a) \/
      ~ In _ (kat2gl r2) (gs_end a).
  Proof.
    intros.
    destruct(ewp_dec r1 a);destruct(ewp_dec r2 a).
    apply ewp_cases_epsilon_false in e.
    apply ewp_cases_epsilon_false in e0;auto.
    left;intro.
    apply ewp_cases_epsilon_false in e.
    contradiction.
    right;intro.
    apply ewp_cases_epsilon_false in e0;auto.
    elimtype False.
    apply H.
    apply ewp_cases_epsilon_true in e.
    apply ewp_cases_epsilon_true in e0;auto.
    change (gs_end a) with (fusion_prod (gs_end a) (gs_end a) (refl_equal a)).
    constructor;auto.
  Qed.

  Lemma ewp_cases_epsilon_false_inv : 
    forall r a, 
      ~In _ (kat2gl r) (gs_end a) -> ewp r a = false.
  Proof.
    induction r;simpl;intros;auto.
    apply not_true_is_false.
    intro.
    apply H.
    constructor;auto.
    apply Bool.orb_false_iff.
    split.
    apply IHr1.
    intro;apply H;auto.
    left;auto.
    apply IHr2.
    intro;apply H;right;auto.
    apply Bool.andb_false_iff.
    pose proof ewp_gs_split_aux _ _ _ H.
    destruct H0;eauto.
    elim H.
    constructor 1 with O.
    simpl.
    constructor.
  Qed.

  Lemma ewp_cases_epsilon_true_inv : 
    forall r a, 
      In _ (kat2gl r) (gs_end a) -> ewp r a = true.
  Proof.
    induction r;simpl;intros;auto.
    inversion H.
    inversion H;auto.
    apply Bool.orb_true_iff.
    inversion_clear H.
    left;apply (IHr1 a H0).
    right;apply (IHr2 a H0).
    inversion H.
    apply Bool.andb_true_iff.
    split.
    apply IHr1.
    apply fusion_prod_split_gs_end in H0.
    destruct H0;subst;auto.
    apply fusion_prod_split_gs_end in H0.
    destruct H0;subst;auto.
  Qed.

  (** Partial derivative of a kat-term by a pair (Atom,Symbol) *)
  Fixpoint pdrv(x:kat)(a:atom)(s:Z) : set kat :=
    match x with
      | kats y => 
          match compare y s with
            | Eq => {katb ba1}
            | _ => {}
          end
      | katb b => {}
      | katu x1 x2 => pdrv x1 a s ++ pdrv x2 a s
      | katc x1 x2 => 
          if ewp x1 a then
            dsr (pdrv x1 a s) x2 ++ pdrv x2 a s
          else
            dsr (pdrv x1 a s) x2
      | katst x1 => dsr (pdrv x1 a s) (katst x1)
    end.

  Lemma ewp_empty_symbol :
    forall e x y,
      e === kats y -> ewp e x === false.
  Proof.
    induction e;intros;
    simpl;auto;
    abstract(inversion H).
  Qed.

  Lemma val_with_test_true :
    forall t alpha,
      evalT alpha t = true -> 
      ewp (katb t) alpha === true.
  Proof.
    intros.
    functional induction (evalT alpha t);try discriminate;
    simpl;auto.
  Qed.

  Lemma val_with_test_false :
    forall t alpha,
      evalT alpha t = false -> 
      ewp (katb t) alpha === false.
  Proof.
    intros.
    functional induction (evalT alpha t);try discriminate;
    simpl;auto.
  Qed.

  Lemma not_eq_katu :
    forall e1 e2, katu e1 e2 <> e2.
  Proof.
    double induction e1 e2;intros;intro;
    try discriminate.
    injection H1;intros.
    specialize H0 with z.
    rewrite <- H2 in H0 at 2.
    rewrite <- H3 in H0.
    elim H0;auto.
    injection H1;intros.
    specialize H0 with t.
    rewrite H3 in H0.
    contradiction.
    injection H3;intros.
    eapply H0.
    eapply H1.
    eapply H2.
    rewrite <- H4 at 2.
    rewrite <- H5.
    reflexivity.
    eapply H0.
    apply H1.
    apply H2.
    injection H3;intros.
    rewrite <- H4 at 2.
    rewrite <- H5.
    reflexivity.
    injection H2;intros.
    eapply H0.
    apply H1.
    rewrite <- H3 at 2.
    rewrite <- H4.
    reflexivity.
  Qed.

  Global Instance ewp_m : Proper(_eq ==> _eq ==> _eq) ewp.
  Proof.
    repeat red.
    intros.
    inv H.
  Qed.

  Global Instance pdrv_m : Proper(_eq ==> _eq ==> _eq ==> _eq) pdrv.
  Proof.
    repeat red.
    intros.
    inv H. subst.
    inv H0. subst.
    inv H1;subst.
    split;intros;auto.
  Qed.

  (** Derivatives of a set of kat terms wrt. an atom and a symbol. *)

  Definition pdrv_set (sre:set kat)(a:atom)(s:Z) :=
    fold (fun x => union (pdrv x a s)) sre {}%set.

  Definition ewp_set(sre:set kat)(a:atom) :=
    fold (fun x => orb (ewp x a)) sre false.

  Instance pdrv_set_proper : forall a s, Proper(_eq ==> _eq ==> _eq)
    (fun x0 => union (pdrv x0 a s)).
  Proof.
    repeat red;split;intros;
    normalize_notations;
    [rewrite H0,H in H1|
     rewrite H0,H];auto.
  Qed.

  Instance ewp_set_proper : 
    forall a, 
      Proper(_eq ==> _eq ==> _eq) (fun x => orb (ewp x a)).
  Proof.
    repeat red;intros.
    rewrite H0.
    rewrite H.
    reflexivity.
  Qed.

  Lemma pdrv_set_transpose : forall a s, 
    transpose Equal (fun x0 => union (pdrv x0 a s)).
  Proof.
    repeat red;intros;
    split;intros;auto;
    apply union_iff in H;
    destruct H.
    apply union_3;apply union_2;auto.
    apply union_iff in H;destruct H.
    apply union_2;auto.
    apply union_3;apply union_3;auto.
    apply union_3;apply union_2;auto.
    apply union_iff in H;destruct H.
    apply union_2;auto.
    apply union_3;apply union_3;auto.
  Qed.

  Hint Resolve pdrv_set_transpose : typeclass_instances.

  Lemma ewp_set_transp : forall a, transpose eq (fun y : kat => orb (ewp y a)).
  Proof.
    repeat red;intros;auto with bool.
    destruct(ewp x a);destruct(ewp y a);case z;simpl;reflexivity.
  Qed.

  Hint Resolve ewp_set_transp : typeclass_instances.
  
  Add Morphism pdrv_set : pdrv_set_m.
  Proof.
    induction x using set_induction;intros.
    normalize_notations.
    unfold pdrv_set.
    rewrite fold_1b;auto.
    rewrite H0 in H.
    rewrite fold_1b;auto.
    unfold pdrv_set.
    normalize_notations.
    rewrite H3.
    generalize(@fold_2 kat _ _ _ x1 x2 x3 
               _ _ Equal_ST {}%set (fun x : kat => union (pdrv x x0 y1))
              (pdrv_set_proper x0 y1) (pdrv_set_transpose x0 y1) H H0);intros.
    assert(SetProperties.Add x3 x1 y).
    apply Add_Equal.
    apply Add_Equal in H0.
    rewrite <- H1.
    rewrite H0.
    reflexivity.
    generalize(@fold_2 kat _ _ _ x1 y x3 
              _ _ Equal_ST {}%set (fun x : kat => union (pdrv x y0 y1))
              (pdrv_set_proper y0 y1) (pdrv_set_transpose y0 y1) H H5);intros.
    rewrite H6.
    rewrite H4.
    eapply union_m. apply pdrv_m;auto. inv H2. unfold _eq. 
    apply ord_Eq_unique.
    assumption.
    apply IHx1.
    reflexivity.
    apply H2.
    reflexivity.
  Qed.

  Lemma true_ewp_set : 
    forall s x a, 
      x \In s -> ewp x a = true -> ewp_set s a = true.
  Proof.
    induction s using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    inversion H0.

    unfold ewp_set.
    apply H0 in H1.
    destruct H1.
    generalize (@fold_2 kat _ _ _ s1 s2 x _ (@eq bool) eq_equivalence
      false (fun y : kat => orb (ewp y a))
      (ewp_set_proper a) (ewp_set_transp a) H H0);intro.    
    rewrite H3.
    rewrite H1.
    rewrite H2;simpl.
    reflexivity.

    generalize (@fold_2 kat _ _ _ s1 s2 x _ (@eq bool) eq_equivalence
      false (fun y : kat => orb (ewp y a))
      (ewp_set_proper a) (ewp_set_transp a) H H0);intro.  
    rewrite H3.
    apply (IHs1 _ a H1) in H2.
    unfold ewp_set in H2.
    rewrite H2.
    rewrite Bool.orb_comm;simpl;reflexivity.
  Qed.

  Lemma ewp_set_true : 
    forall s a, 
      ewp_set s a = true -> exists x,( x \In s /\ ewp x a = true).
  Proof.
    induction s using set_induction;intros.
    unfold ewp_set in H0.
    rewrite fold_1b in H0;auto.
    inversion H0.

    unfold ewp_set in H1.
    generalize (@fold_2 kat _ _ _ s1 s2 x _ (@eq bool) eq_equivalence
      false (fun y : kat => orb (ewp y a))
      (ewp_set_proper a) (ewp_set_transp a) H H0);intro.
    rewrite H2 in H1;clear H2.
    assert (Bool.Is_true ((ewp x a)||( fold (fun y : kat => orb (ewp y a)) s1 false))).
    unfold Bool.Is_true.
    rewrite H1.
    trivial.
    apply Bool.orb_prop_elim in H2.
    unfold Bool.Is_true in H2.
    destruct H2.
    exists x.
    destruct(ewp x a).
    split.
    apply H0.
    left;reflexivity.
    reflexivity.
    elim H2.
    apply Bool.Is_true_eq_true in H2.
    apply IHs1 in H2.
    do 2 destruct H2.
    exists x0;split;auto.
    apply H0.
    right;auto.
  Qed.

  Open Scope set_scope.

  Lemma pdrv_set_singleton : forall r a s, 
    (pdrv_set {r}%set a s)===(pdrv r a s).
  Proof.
    intros.
    unfold pdrv_set.
    generalize(@fold_2 kat _ _ _ {}%set {r}%set r 
      _ _ Equal_ST {}%set (fun x : kat => union (pdrv x a s))
        (pdrv_set_proper a s) (pdrv_set_transpose a s));intros.
    assert(~r \In {}).
    intro.
    inversion H0.
    assert(SetProperties.Add r {} {r}).
    apply Add_Equal.
    vm_compute;auto.
    generalize(H H0 H1);clear H;intros.
    rewrite H;clear H.
    rewrite fold_1b.
    rewrite empty_union_2.
    reflexivity.
    vm_compute;intros.
    inversion x0.
    vm_compute;intros.
    inversion x0.
  Qed.
  
  Lemma pdrv_set_empty : forall a s,
    (pdrv_set {} a s)==={}.
  Proof.
    intros.
    unfold pdrv_set.
    rewrite fold_1b.
    reflexivity.
    vm_compute;intros.
    inversion x0.
  Qed.
  
  Lemma In_pdrv_set : forall s x a t,
    x \In (pdrv_set s a t) -> exists y, y \In s /\ x \In (pdrv y a t).
  Proof.
    induction s using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    rewrite pdrv_set_empty in H0.
    inversion H0.
    generalize(@fold_2 kat _ _ _ s1 s2 x _ _ Equal_ST {}%set _
      (pdrv_set_proper a t) (pdrv_set_transpose a t) H H0);intro.
    unfold pdrv_set in H1.
    rewrite H2 in H1.
    clear H2.
    apply union_iff in  H1.
    destruct H1.
    
    exists x.
    split.
    apply H0.
    left;auto.
    assumption.
    
    apply IHs1 in H1.
    do 2 destruct H1.
    exists x1.
    split.
    apply H0.
    right;auto.

    assumption.
  Qed.

  Lemma In_pdrv_in_pdrv_set : forall s x y a t,
    y \In (pdrv x a t) -> x \In s -> y \In (pdrv_set s a t).
  Proof.
    induction s using set_induction;intros.
    elim (H x);auto.

    generalize(@fold_2 kat _ _ _ s1 s2 x _ _ Equal_ST {}%set _
      (pdrv_set_proper a t) (pdrv_set_transpose a t) H H0);intro.
    fold (pdrv_set s2 a t) in H3.
    fold (pdrv_set s1 a t) in H3.
    rewrite H3.
    apply H0 in H2.
    destruct H2.

    rewrite H2.
    apply union_2;auto.
    generalize(IHs1 _ _ _ _ H1).
    intro.
    apply H4 in H2.
    apply union_3.
    assumption.
  Qed.

  (** Monotonicity of the set derivative w.r.t. a symbol [a] *)
  Lemma pdrv_contained : forall x y a t,
    x[<=]y -> (pdrv_set x a t)[<=](pdrv_set y a t).
  Proof.
    induction x using set_induction;intros.
    red;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H1.
    rewrite pdrv_set_empty in H1.
    inversion H1.
    intros a0 H2.
    unfold pdrv_set in H2.
    apply((@fold_2 kat _ _ _ x1 x2 x3 
      _ _ Equal_ST {}%set (fun x : kat => union (pdrv x a t)))) in H2;
    auto with typeclass_instances.
    apply union_1 in H2.
    destruct H2.
    eapply In_pdrv_in_pdrv_set.
    apply H2.
    apply H1.
    apply H0;auto.
    apply IHx1.
    red;intros.
    apply H1.
    apply H0;auto.
    apply H2.
  Qed.
  
  Hint Resolve 
    pdrv_set_singleton 
    pdrv_set_empty 
    In_pdrv_set 
    In_pdrv_in_pdrv_set : gl_hints.
  
  (** Operations on sets of partial derivatives *)
  Lemma pdrv_set_add : forall s x a t,
    (pdrv_set (add x s) a t)===((pdrv x a t)++(pdrv_set s a t)).
  Proof.
    induction s using set_induction;intros.
    generalize H;intro H1;apply empty_is_empty_1 in H1.
    rewrite H1.
    rewrite pdrv_set_empty;auto with sets.

    apply Add_Equal in H0.
    split;intros.
    rewrite H0 in H1.
    apply In_pdrv_set in H1.
    do 2 destruct H1.
    apply add_iff in H1.
    destruct H1.
    rewrite H1. 
    apply union_2;auto.
    apply add_iff in H1.
    destruct H1.
    apply union_3.
    rewrite H0.
    apply IHs1.
    apply union_2.
    rewrite H1.
    assumption.
    rewrite H0.
    apply union_3.
    rewrite IHs1.
    apply union_3.
    apply In_pdrv_in_pdrv_set with x1;auto.

    apply union_1 in H1.
    destruct H1.
    eapply In_pdrv_in_pdrv_set.
    apply H1.
    apply add_1.
    reflexivity.
    
    apply In_pdrv_set in H1.
    do 2 destruct H1.
    eapply In_pdrv_in_pdrv_set.
    apply H2.
    apply add_2.
    assumption.
  Qed.
  
  Lemma pdrv_set_union : forall s1 s2 a t,
    (pdrv_set (s1++s2) a t)===((pdrv_set s1 a t)++(pdrv_set s2 a t)).
  Proof.
    induction s1 using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H.
    rewrite pdrv_set_empty.
    rewrite empty_union_1.
    rewrite empty_union_1.
    reflexivity.

    vm_compute;intros.
    inversion x0.

    vm_compute;intros.
    inversion x0.

    split;intros.
    apply In_pdrv_set in H1.
    do 2 destruct H1.
    apply union_1 in H1.
    destruct H1.
    apply Add_Equal in H0.
    rewrite H0 in H1.
    rewrite add_union_singleton in H1.
    apply union_1 in H1.
    destruct H1.
    apply singleton_1 in H1.
    rewrite H0.
    rewrite pdrv_set_add.
    apply union_2.
    apply union_2.
    rewrite H1;auto.

    generalize(In_pdrv_in_pdrv_set _ _ _ _ _ H2 H1);intro.
    rewrite H0.
    rewrite pdrv_set_add.
    apply union_2.
    apply union_3.
    auto.
    generalize(In_pdrv_in_pdrv_set _ _ _ _ _ H2 H1);intro.
    apply union_3;auto.
    apply union_1 in H1.
    apply Add_Equal in H0.
    destruct H1.
    rewrite H0 in H1.
    rewrite pdrv_set_add in H1.
    apply union_1 in H1;destruct H1.
    rewrite H0.
    rewrite union_add.
    rewrite pdrv_set_add.
    apply union_2;auto.

    rewrite H0.
    rewrite union_add.
    rewrite pdrv_set_add.
    apply union_3.
    rewrite IHs1_1.
    apply union_2;auto.
    rewrite H0.
    rewrite union_add.
    rewrite pdrv_set_add.
    apply union_3.
    rewrite IHs1_1.
    apply union_3;auto.
  Qed.            

  Fixpoint PI (r:kat) : set kat :=
    match r with
      | katb b => {}
      | kats _ => {katb ba1}
      | katu x y  => (PI x)++(PI y)
      | katc x y  => ((PI x)[.]y)++(PI y)
      | katst x   => (PI x)[.](katst x)
    end.
  
  Functional Scheme PI_ind := Induction for PI Sort Prop.
  Functional Scheme PI_rec := Induction for PI Sort Set.

  Add Morphism PI : PI_m.
  Proof.
    intro x.
    functional induction (PI x);
      intros;normalize_notations;inversion_clear H;simpl;auto;
      try (apply leibniz_test in H0;subst;auto).
  Qed.

  Lemma in_pdrv_0 : ~exists y, y \In (PI (katb ba0)).
  Proof.
    intro H.
    destruct H as [y Nin].
    simpl in Nin.
    inversion Nin.
  Qed.

  Lemma in_pdrv_1 : ~exists y, y \In (PI (katb ba1)).
  Proof.
    intro H;simpl in H.
    destruct H as [y Nin].
    inversion Nin.
  Qed.

  Lemma in_pdrv_sy : forall y s, y \In (PI (kats s)) -> y === (katb ba1).
  Proof.
    intros.
    simpl in H.
    apply singleton_1 in H.
    symmetry;auto.
  Qed.
  
  Lemma in_pdrv_union : 
    forall x y z, 
      x \In (PI (katu y z)) ->
      x \In (PI y) \/ x \In (PI z).
  Proof.
    intros.
    simpl in H.
    apply union_1 in H.
    assumption.
  Qed.

  Lemma in_pdrv_conc : 
    forall x y z, 
      Not_0_1 z -> x \In (PI (katc y  z)) ->
      x \In (PI z) \/ exists y', x === katc y' z /\ y' \In (PI y).
  Proof.
    intros.
    simpl in H0.
    apply union_iff in H0.
    destruct H0.
    apply in_dsr in H0.
    destruct H0 as [y' [H11 H12]].
    right.
    exists y'.
    intuition.
    assumption.
    simpl in H0.
    left;assumption.
  Qed.
    
  Lemma in_pdrv_star : 
    forall x y, 
      x \In (PI (katst y)) -> exists y', x === katc y' (katst y) /\ y' \In (PI y).
  Proof.
    intros.
    simpl in H.
    apply in_dsr_re_star in H.
    destruct H as [y' [H11 H12]].
    exists y'.
    intuition.
  Qed.
  
  (** Transitivity of the PI function *)
  Lemma PI_trans : 
    forall x y, 
      y \In (PI x) -> forall z, z \In (PI y) -> z \In (PI x).
  Proof.
    induction x;simpl;intros.
    apply singleton_1 in H.
    rewrite <- H in H0.
    simpl in H0.
    inversion H0.
    inversion H.
    
    apply union_1 in H.
    destruct H.
    generalize(IHx1 _ H _ H0);intro.
    apply union_2;auto.
    generalize(IHx2 _ H _ H0);intro.
    apply union_3;auto.

    destruct (dsr_cases (PI x1) x2).
    rewrite H1 in H.
    apply union_iff in H.
    destruct H.
    inversion H.
    apply union_3.
    eapply IHx2.
    apply H;auto.
    assumption.
    
    destruct H1.
    rewrite H1 in H |- *.
    apply union_iff in H.
    destruct H;[apply union_2|apply union_3].
    eapply IHx1.
    apply H.
    assumption.
    eapply IHx2.
    apply H.
    assumption.
    destruct H1.
    apply union_1 in H.
    destruct H.
    apply (in_dsr (PI x1) x2 y) in H;auto.
    do 2 destruct H.
    rewrite H3 in H0.
    simpl in H0.
    apply union_1 in H0.
    destruct H0.
    apply union_2.
    apply (in_dsr (PI x) x2 z) in H0;auto.
    do 2 destruct H0.
    rewrite H4.
    rewrite H2.
    apply elem_conc_in_fold_conc.
    eapply IHx1.
    apply H.
    assumption.
    apply union_3.
    assumption.
    apply union_3.
    eapply IHx2.
    apply H.
    apply H0.
    (* kleene's star *)
    apply elem_conc_in_ex in H.
    do 2 destruct H.
    rewrite H1 in H0.
    simpl in H0.
    apply union_1 in H0.
    destruct H0.
    apply elem_conc_in_ex in H0.
    do 2 destruct 0.
    rewrite H2.
    apply elem_conc_in_fold_conc;auto.
    eapply IHx.
    apply H.
    assumption.
    assumption.
  Qed.
    
  Definition PD(r:kat) := {r}%set++(PI r).

  Fixpoint sylen (r:kat) : nat :=
    (match r with
      | kats _ => 1
      | katb _ => 0
      | katu x y => sylen x + sylen y
      | katc x y => sylen x + sylen y
      | katst x => sylen x
    end)%nat.

  Lemma PI_upper_bound : forall r, (cardinal (PI r)) <= (sylen r).
  Proof.
    induction r;simpl;auto.
    rewrite union_cardinal_inter.
    abstract omega.
    rewrite union_cardinal_inter.
    generalize(dsr_cardinal (PI r1) r2).
    intro.
    abstract omega.
    rewrite fold_conc_card.
    assumption.
  Qed.

  Theorem PD_upper_bound : forall r, (cardinal (PD r)) <= (S (sylen r)).
  Proof.
    unfold PD.
    intros.
    generalize(PI_upper_bound r);intro H.
    rewrite union_cardinal_inter.
    rewrite singleton_cardinal.
    unfold plus.
    abstract omega.
  Qed.

  Theorem all_pdrv_in_PI : forall x a r, (pdrv x a r)[<=](PI x).
  Proof.
    induction x;unfold Subset;simpl;intros.
    case_eq(compare z r);intros;
    rewrite H0 in H.
    assumption.
    inversion H.
    inversion H.
    assumption.
      
    apply union_1 in H.
    destruct H.
    apply union_2.
    apply (IHx1 a r);assumption.
    apply union_3.
    apply (IHx2 a r).
    assumption.

    destruct(ewp x1 a). 
    apply union_1 in H.
    destruct H.
    generalize(dsr_cases (pdrv x1 a r) x2);intro.
    destruct H0 as [H11 | [ H12 | H13]].
    rewrite H11 in H.
    inversion H.
    
    destruct(eq_dec x2 (katb ba0)).
    rewrite H0 in H.
    simpl in H.
    inversion H.
    destruct(eq_dec x2 (katb ba1)).
    rewrite H1 in H |- *.
    simpl in *.
    apply IHx1 in H.
    apply union_2;auto.
    apply in_dsr in H;auto.
    destruct H as [y' [H11 H13]].
    rewrite H13.
    apply union_2.
    apply elem_conc_dsr_in;auto.
    eapply IHx1.
    apply H11.
    destruct H13.
    apply in_dsr in H;auto.
    destruct H as [y' [H11 H12]].
    rewrite H12.
    apply union_2.
    apply elem_conc_dsr_in;auto.
    eapply IHx1.
    apply H11.
    apply union_3.
    eapply IHx2.
    apply H.

    destruct(eq_dec x2 (katb ba0)).
    rewrite H0 in H.
    simpl in H.
    inversion H.
    destruct(eq_dec x2 (katb ba1)).
    rewrite H1 in H |- *.
    simpl in *.
    apply union_2.
    apply (IHx1 _ _ _ H).
    apply in_dsr in H;auto.
    destruct H as [y' [H11 H12]].
    rewrite H12.
    apply union_2.
    apply elem_conc_dsr_in;auto.
    apply (IHx1 _ _ _ H11).

    apply elem_conc_in_ex in H.
    destruct H as [y [H11 H12]].
    rewrite H12.
    apply elem_conc_in_fold_conc.
    eapply IHx.
    apply H11.
  Qed.
   
 
  Lemma PD_trans : 
    forall x y, 
      y \In (PD x) -> forall z, z \In (PD y) -> z \In (PD x).
  Proof.
    intros.
    unfold PD in *.
    apply union_1 in H0;destruct H0.
    apply singleton_1 in H0;subst;auto.
    apply union_1 in H;destruct H.
    apply union_2.
    rewrite <- H0.
    assumption.

    apply union_3.
    rewrite <- H0.
    assumption.

    apply union_1 in H.
    destruct H.
    apply singleton_1 in H.
    apply (PI_m x y) in H.
    apply H in H0.
    apply union_3;auto.
    
    apply union_3.
    eapply PI_trans.
    apply H.
    assumption.
  Qed.

  (** Derivation by a guarded string. *)
  Reserved Notation "x %dw y" (at level 60).
  Fixpoint pdrv_iw (sre:set kat)(w:ilist) : set kat :=
    match w with
      | <[] => sre
      | xs <:: x => pdrv_set (sre %dw xs) (fst x) (snd x)
    end
    where "x %dw y" := (pdrv_iw x y).
  
  Functional Scheme pdrv_iw_ind := Induction for pdrv_iw Sort Prop.
  Functional Scheme pdrv_iw_rec := Induction for pdrv_iw Sort Set.

(** Simple/base properties *)
  Lemma pdrv_iw_sy_icons : forall w r s,
    (s %dw (w <:: r))=== (pdrv_set (s %dw w) (fst r) (snd r)).
  Proof.
    induction w;simpl;split;intros;
      try assumption.
  Qed.

  Lemma pdrv_iw_sy_nil : forall s,
    (s %dw <[])===s.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma pdrv_iw_empty : forall w,
    ({} %dw w)==={}%set.
  Proof.
    induction w;simpl.
    reflexivity.
    split;intros.
    rewrite IHw in H.
    rewrite pdrv_set_empty in H.
    assumption.
    inversion H.
  Qed.

  Add Morphism pdrv_iw : pdrv_iw_m.
  Proof.
    intros.
    apply ilist_eq_leibniz in H0.
    rewrite H0.
    revert x y H.
    clear H0.
    revert y0.
    induction y0.
    simpl;intros. 
    assumption.
    intros.
    do 2 rewrite pdrv_iw_sy_icons.
    generalize H;intro.
    apply IHy0 in H0.
    rewrite H0.
    reflexivity.
  Qed.

  (** wprdv expansion by concatenation of two words *)
  Lemma pdrv_iw_app : forall w w' s, 
    (s %dw (w <++ w'))===(pdrv_iw (s %dw w) w').
  Proof.
    intros w w';revert w' w.
    induction w';simpl;intros.
    reflexivity.
    rewrite IHw'.
    reflexivity.
  Qed.
  
  Lemma pdrv_iw_union : forall w s1 s2,
    ((s1++s2) %dw w)===((s1 %dw w)++(s2 %dw w)).
  Proof.
    induction w;simpl.
    reflexivity.
    intros.
    split;intros.
    rewrite IHw in H.
    rewrite <- pdrv_set_union.
    assumption.
    rewrite IHw.
    rewrite <- pdrv_set_union in H.
    auto.
  Qed.
  
  (** Existance of elements *)
  Lemma in_pdrv_iw_pdrv : forall s w x, 
    x \In (s %dw w) -> exists y, y \In s /\ x \In ({y}%set %dw  w).
  Proof.
    induction s using set_induction;simpl;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    rewrite pdrv_iw_empty in H0.
    inversion H0.

    
    apply Add_Equal in H0.
    rewrite H0 in H1.
    rewrite add_union_singleton in H1.
    rewrite pdrv_iw_union in H1.
    eapply union_1 in H1.
    destruct H1.
    exists x.
    split;auto.
    rewrite H0.
    apply add_1.
    reflexivity.
    apply IHs1 in H1.
    destruct H1 as [y [H2 H3]].
    exists y.
    split;auto. 
    rewrite H0.
    apply add_2.
    assumption.
  Qed.

  Lemma iw_pdrv_in_pdrv : forall w s x y, 
     y \In s ->  x \In ({y}%set %dw  w) -> x \In (s %dw w).
  Proof.
    induction w ;simpl;intros.
    apply singleton_1 in H0;subst;auto.
    rewrite <- H0.
    assumption.

    apply In_pdrv_set in H0.
    do 2 destruct H0.
    apply IHw with (x:=x0) in H;auto.
    eapply In_pdrv_in_pdrv_set.
    apply H1.
    assumption.
  Qed.

  Lemma pdrv_set_comp : forall s x a0 a1, 
    x \In (pdrv_set (pdrv_set s (fst a1) (snd a1)) (fst a0) (snd a0)) -> 
    x \In (s %dw ((<[]<::a1)<::a0)).
  Proof.
    intros.
    simpl.
    assumption.
  Qed.

  (** Finally, the definition [wpdrv] uses [pdrv_iw] but first transforms an [ilist] into its corresponding [word] type. *)

  Definition wpdrv (r:kat)(w:list AtSy) :=
    pdrv_iw ({r}%set) (list_to_ilist w).
  Notation "x %dW y" := (wpdrv x y)(at level 60).

  (** Derivation of a single regular expression by a word *)
  Definition wpdrv_set (s:set kat)(w:list AtSy) :=
    s %dw (<@ w).

  Notation "x %dWS y" := (wpdrv_set x y)(at level 60).
  
  Add Morphism wpdrv with signature _eq ==> _eq ==> Equal as wpdrv_m.
  Proof.
    induction 2.
    normalize_notations.
    unfold wpdrv.
    simpl.
    rewrite H.
    reflexivity.
    unfold wpdrv.
    simpl.
    do 2 rewrite pdrv_iw_app.
    apply pdrv_iw_m.
    split;intros;
    normalize_notations.
    apply  in_pdrv_iw_pdrv in H2.
    destruct H2 as [y' [H11 H12]].
    eapply iw_pdrv_in_pdrv with y'.
    rewrite <- H.
    assumption.
    rewrite <- H0.
    assumption.
    rewrite H.
    rewrite H0.
    assumption.
    normalize_notations.
    induction H1.
    simpl.
    reflexivity.
    normalize_notations.
    destruct a0.
    destruct a'0.
    inversion_clear H1.
    rewrite H4.
    inv H3.
    simpl.
    rewrite H2.
    reflexivity.
  Qed.

  Add Morphism wpdrv_set with signature Equal ==> _eq ==> Equal as wpdrv_set_m.
  Proof.
    unfold wpdrv_set.
    intuition.
    normalize_notations.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.
  
  Add Morphism wpdrv_set with signature Subset ++> _eq  ++> Subset 
    as wpdrv_set_subset.
  Proof.
    induction 2;simpl.
    unfold wpdrv_set in *;simpl.
    assumption.
    
    red;intros.
    normalize_notations.
    apply in_pdrv_iw_pdrv in H2.
    do 2 destruct H2.
    eapply iw_pdrv_in_pdrv.
    apply H in H2.
    apply H2.
    simpl in *.
    rewrite H0 in H3.
    rewrite H1 in H3.
    assumption.
  Qed.

  Lemma wpdrv_nil : forall r, 
    (r %dW nil)==={r}%set.
  Proof.
    intro.
    unfold wpdrv;simpl.
    reflexivity.
  Qed.

  Lemma wpdrv_set_nil : forall s,
    (s %dWS nil)===s.
  Proof.
    intros.
    unfold wpdrv_set.
    simpl.
    reflexivity.
  Qed.

  Lemma wpdrv_set_singleton : forall s w,
    {s}%set %dWS w === s %dW w.
  Proof.
    induction w;simpl.
    rewrite wpdrv_set_nil.
    rewrite wpdrv_nil.
    reflexivity.
    unfold wpdrv_set;simpl.
    rewrite  pdrv_iw_app.
    simpl.
    rewrite pdrv_set_singleton.
    unfold wpdrv;simpl.
    rewrite pdrv_iw_app.
    simpl.
    rewrite pdrv_set_singleton.
    reflexivity.
  Qed.

  Lemma wpdrv_set_empty : forall w,
    ({} %dWS w)==={}%set.
  Proof.
    intro.
    unfold wpdrv_set.
    rewrite pdrv_iw_empty.
    reflexivity.
  Qed.

  Lemma wpdrv_sy_nil : forall r x,
    (r %dW (x::nil))===(pdrv_set {r}%set (fst x) (snd x)).
  Proof.
    intros.
    unfold wpdrv;simpl.
    reflexivity.
  Qed.

  Lemma wpdrv_cons : forall r x w,
      (r %dW (w++(x::nil)))===((r %dW w) %dWS (x::nil)).
  Proof.
    intros.
    unfold wpdrv,wpdrv_set.
    destruct(exListFromIlist (w)).
    rewrite IlistFromListConc.
    rewrite <- H.
    revert x0 H r.
    induction x0;simpl;intros.
    reflexivity.
    reflexivity.
  Qed.

  Lemma wpdrv_set_app : forall s w1 w2, 
    (s %dWS (w1++w2)) === ((s %dWS w1) %dWS w2).
  Proof.
    induction w1;simpl;intros.
    rewrite wpdrv_set_nil;auto.
    unfold wpdrv_set;simpl.
    repeat rewrite pdrv_iw_app.
    unfold wpdrv_set in IHw1.
    rewrite IlistFromListConc.
    rewrite pdrv_iw_app.
    reflexivity.
  Qed.

  Lemma wpdrv_set_eq_prv_set_case : forall s a, 
    (pdrv_set s (fst a) (snd a))===(s %dWS (a::nil)).
  Proof.
    intros.
    unfold wpdrv_set.
    simpl.
    reflexivity.
  Qed.
  
  Lemma wpdrv_app : forall r w w',
    (r %dW (w++w'))===((r %dW w) %dWS w').
  Proof.
    intros.
    unfold wpdrv,wpdrv_set.
    destruct(exListFromIlist (w')).
    rewrite IlistFromListConc.
    rewrite <- H.
    revert  x r w w' H.
    induction x;simpl;intros.
    reflexivity.
    rewrite <-  pdrv_iw_app.
    reflexivity.
  Qed.

  (** * Partial derivatives w.r.t words belong to PD *)
  Lemma all_wpdrv_in_PD : forall w x r, x \In ({r}%set %dw w) -> x \In PD(r).
  Proof.
    induction w.
    simpl.
    unfold PD;intros.
    apply union_2;auto.
    
    simpl;intros.
    eapply In_pdrv_set in H.
    do 2 destruct H.
    apply IHw in H.
    unfold PD.
    unfold PD in H.
    apply union_1 in H.
    destruct H.
    apply singleton_1 in H.
    subst.
    apply all_pdrv_in_PI in H0.
    apply union_3.
    apply(PI_m _ _ H) in H0;auto.
    
    apply all_pdrv_in_PI in H0.
    apply union_3.
    eapply PI_trans.
    apply H.
    assumption.
  Qed.

  Lemma SL_conc :
      forall (l1 l2:kat) a s,
      if ewp l1 a then
        LQ (gl_conc l1 l2) a s == gl_union (gl_conc (LQ l1 a s) l2) (LQ l2 a s)
        else
          LQ (gl_conc l1 l2) a s == (gl_conc (LQ l1 a s) l2).
  Proof.
    intros.
    destruct(ewp_dec l1 a) as [H1|H1];rewrite H1.
    split;red;intros.
    inv H.
    subst.
    inv H0.
    apply blop in H2.
    destruct H2 as [H2|H2].
    destruct H2 as [x' [t' [H2 H5]]].
    rewrite <- H5.
    constructor.
    constructor.
    rewrite <- H2 ; auto.
    assumption.
    destruct H2.
    apply ewp_cases_epsilon_false in H1.
    rewrite <- H2 in H1.
    contradiction.
    inv H.
    inv H0.
    inv H3.
    subst.
    constructor.
    pose proof fusion_prod_gs_generic_inv a s x0 y T.
    destruct H3.
    rewrite H3.
    constructor.
    inv H0.
    assumption.

    split;red;intros.
    inv H.
    inv H0.
    subst.
    apply blop in H5.
    destruct H5.
    destruct H2.
    destruct H2.
    destruct H2.
    subst.
    left.
    constructor;auto.
    constructor;auto.
    destruct H2.
    subst.
    right.
    constructor.
    assumption.
    inv H.
    inv H0.
    subst.
    constructor.
    pose proof fusion_prod_gs_generic_inv a s x1 y T.
    destruct H2.
    rewrite H2.
    constructor.
    inv H3.
    assumption.
    constructor.
    inv H0.
    subst.
    change(gs_conc a s x) with (fusion_prod (gs_end a) (gs_conc a s x) (refl_equal a)).
    constructor.
    apply ewp_cases_epsilon_true in H1.
    assumption.
    assumption.
  Qed.

  Lemma LQ_star_l :
    forall (l:kat)  a s,
      LQ (gl_star (kat2gl l)) a s == gl_conc (LQ l a s) (gl_star l).
  Proof.
    intros.
    split;red;intros.
    inv H.
    subst.
    inv H0.
    subst.
    revert n H1.
    induction n;intros.
    simpl in H1.
    inv H1.
    simpl in H1.
    inversion H1.
    apply blop in H2.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H2.
    rewrite <- H5.
    constructor.
    constructor.
    rewrite <- H2;auto.
    econstructor 1 with n.
    assumption.
    destruct H2.
    rewrite H5 in H4.
    apply IHn in H4.
    assumption.

    constructor.
    inv H.
    subst.
    inv H1.
    subst.
    inv H1.
    subst.
    constructor 1 with (S n).
    simpl.
    pose proof fusion_prod_gs_generic_inv a s x0 y T.
    destruct H4.
    rewrite H4.
    constructor;auto.
    inv H0.
  Qed.

  Theorem pdrv_correct :
    forall a s r,
      SkatL (pdrv r a s) == LQ (kat2gl r) a s.
  Proof.
    induction r;simpl;intros.
    
    case_eq(compare z s);intros.
    normalize_notations.
    apply compare_2 in H.
    inv H.
    subst.
    rewrite(LQ_SyL_eq a _ _ H).
    rewrite SkatL_singleton.
    autorewrite with gl_rw.
    reflexivity.
    apply compare_1 in H.
    apply lt_not_eq in H.
    rewrite(LQ_SyL_neq a _ _ H).
    rewrite SkatL_empty.
    reflexivity.
    apply compare_3 in H.
    apply lt_not_eq in H.
    symmetry in H.
    rewrite(LQ_SyL_neq a _ _ H).
    rewrite SkatL_empty.
    reflexivity.
    
    rewrite LQ_Test.
    rewrite SkatL_empty.
    reflexivity.
    
    rewrite LQ_union.
    rewrite SkatL_union.
    rewrite IHr1,IHr2.
    reflexivity.

    case_eq(ewp r1 a);intros.
    rewrite SkatL_union.
    rewrite SkatL_dsr.
    rewrite IHr1.
    rewrite IHr2.
    symmetry.
    pose proof H.
    apply ewp_cases_epsilon_true in H0.
    pose proof SL_conc r1 r2 a s.
    rewrite H in H1.
    assumption.
    pose proof SL_conc r1 r2 a s.
    rewrite H in H0.
    rewrite SkatL_dsr.
    rewrite IHr1.
    symmetry.
    assumption.
       
    rewrite LQ_star_l.
    rewrite SkatL_fconc.
    rewrite IHr.
    reflexivity.
  Qed.
  
  Lemma LangOfPdrvSet :  
    forall s a x, 
      L[pdrv_set s a x] == LQ L[s] a x.
  Proof.
    induction s using set_induction;simpl;intros.
    apply empty_is_empty_1 in H.
    rewrite H.
    rewrite pdrv_set_empty.
    gl_goal.
    inversion H0.
    inversion H1.
    inversion_clear H0.
    apply SkatL_empty in H1.
    inversion H1.
    apply Add_Equal in H0.
    rewrite H0.
    rewrite add_union_singleton.
    rewrite pdrv_set_union.
    do 2 rewrite SkatL_union.
    rewrite LQ_union.
    rewrite pdrv_set_singleton.
    rewrite pdrv_correct.
    rewrite SkatL_singleton.
    rewrite IHs1.
    reflexivity.
  Qed.

  Lemma SkatL_dsr_re0 : forall s, L[s[.](katb ba0)] == L[{}%set].
  Proof.
    intro.
    simpl.
    reflexivity.
  Qed.

  Lemma Skat_dsr_re1 : forall s, L[s[.](katb ba1)] == L[s].
  Proof.
    intro.
    simpl.
    reflexivity.
  Qed.
  
  Lemma LQw_single : forall (r:kat) a s,
    LQw_alt (kat2gl r) ((a,s)::nil) == LQ (kat2gl r) a s.
  Proof.
    intros.
    apply LQw_alt_eq_LQ.
  Qed.

  Lemma LQw_split_app : 
    forall w1 w2 r,
      LQw_alt (kat2gl r) (w1 ++ w2) == LQw_alt (LQw_alt r w1) (w2).
  Proof.
    induction w1;simpl.
    intros.
    gl_goal.
    inv H;subst.
    constructor.
    constructor.
    simpl.
    assumption.
    inv H;subst.
    inv H0;subst.
    simpl in H1.
    constructor.
    assumption.

    intros;simpl.
    gl_goal.
    inv H.
    subst.
    constructor.
    constructor.
    simpl.
    simpl in H0.
    rewrite to_gstring_app in H0.
    assumption.

    inv H.
    subst.
    inv H0.
    subst.
    constructor.
    rewrite app_comm_cons.
    simpl.
    simpl in H1.
    rewrite to_gstring_app.
    assumption.
  Qed.

  Lemma LQw_alt_split_app : 
    forall w1 w2 r,
      LQw_alt r (app w1 w2) == LQw_alt (LQw_alt r w1) w2.
  Proof.
    induction w1;simpl;intros.
    gl_goal.
    repeat constructor.
    destruct H.
    simpl;auto.
    
    inversion H.
    subst;simpl in *.
    inversion H0.
    subst.
    constructor;simpl in *.
    assumption.

    gl_goal.
    inversion H.
    subst.
    constructor.
    constructor.
    simpl in *.
    rewrite <- to_gstring_app.
    auto.
    
    inversion H;simpl in *;subst.
    inversion H0;subst.
    constructor.
    simpl in *.
    rewrite to_gstring_app.
    assumption.
  Qed.

  (* Lemma SkatL_iw_pdrv_app : *)
  (*   forall w r a, *)
  (*     SkatL ({r}%set %dw ((<[] <:: a) <++ <@ w)) == *)
  (*           LQw_alt (SkatL ({r}%set %dw ((<[] <:: a)))) (w). *)
  (* Proof. *)
  (*   induction w;intros. *)
  (*   simpl;gl_goal. *)
  (*   inv H;subst. *)
  (*   constructor. *)
  (*   simpl. *)
  (*   econstructor 1 with r0;auto. *)
  (*   inv H. *)
  (*   inv H0. *)
  (*   subst. *)
  (*   constructor 1 with r0;auto. *)

  (*   admit. *)
  (* Qed. *)

  Lemma Lqw_Lq_app : forall w (r:kat) a s,
    LQw_alt r (@>((inil<::(a,s))<++w)) == LQw_alt (LQ r a s) (@>w).
  Proof.
    induction w;simpl;intros.
    gl_goal.
    inversion H.
    subst.
    simpl in H0.
    constructor.
    constructor.
    simpl.
    auto.
    constructor.
    simpl.
    inversion H;subst.
    inversion H0;subst.
    simpl in H1.
    assumption.

    rewrite LQw_split_app.
    rewrite IHw.
    gl_goal.
    inv H.
    subst.
    constructor.
    simpl.
    inv H0.
    subst.
    rewrite to_gstring_app.
    assumption.
    inv H.
    subst.
    inv H0.
    subst.
    constructor.
    constructor.
    constructor.
    rewrite <- to_gstring_app.
    assumption.
  Qed.

  Lemma wpdrv_corr : 
    forall w r, 
      SkatL (pdrv_iw r w) == LQw_alt (SkatL r) (@>w).
  Proof.
    induction w;simpl;intros.
    rewrite LQw_alt_nil.
    reflexivity.
    
    rewrite LQw_alt_split_app.
    rewrite LangOfPdrvSet.
    gl_goal.
    inv H;subst.
    apply IHw in H0.
    constructor.
    simpl.
    assumption.

    inv H.
    subst.
    apply IHw in H0.
    constructor.
    simpl in H0.
    assumption.
  Qed.

  Theorem wpdrv_correct :
    forall w r,
      SkatL (wpdrv r w) == LQw_alt (kat2gl r) w.
  Proof.
    intros.
    unfold wpdrv.
    rewrite wpdrv_corr.
    rewrite ListFromIlist.
    rewrite SkatL_singleton.
    reflexivity.
  Qed.

  Instance ewp_set_m : Proper (_eq ==> _eq ==> _eq) ewp_set.
  Proof.
    repeat red.
    induction x using set_induction;intros.
    unfold ewp_set.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    assert(y[=]{}).
    rewrite <- H0.
    reflexivity.
    apply empty_is_empty_2 in H.
    apply empty_is_empty_2 in H2.
    rewrite fold_1b;auto.
    rewrite fold_1b;auto.
    unfold ewp_set.
    rewrite fold_2;eauto with typeclass_instances.
    fold(ewp_set x1 x).
    assert(SetProperties.Add x3 x1 y).
    apply Add_Equal.
    rewrite <- H1.
    apply Add_Equal.
    assumption.
    rewrite fold_2;eauto with typeclass_instances.
    fold(ewp_set x1 y0).
    inv H2.
  Qed.

  Lemma ewp_of_re_set_singleton : forall s a,
      ewp_set {s}%set a = ewp s a.
    Proof.
      intros.
      unfold ewp_set.
      rewrite (@fold_2 kat _ _ _ {} {s} s bool);eauto with typeclass_instances.
      rewrite fold_1b;eauto with typeclass_instances.
      rewrite Bool.orb_comm.
      simpl.
      reflexivity.
      intro.
      inv H.
      red;intros.
      split;intros.
      apply singleton_1 in H;auto.
      destruct H.
      apply singleton_2;auto.
      inv H.
    Qed.

    Lemma gs_end_aux :
      forall w a0,
        (gs_end (last (to_gstring w (gs_end a0)))) = gs_end a0.
    Proof.
      induction w;simpl;intros.
      reflexivity.
      rewrite IHw.
      reflexivity.
    Qed.

    Lemma gs_in_pdrv : 
      forall w (r:kat) a, 
        In _ (kat2gl r) ((to_gstring w) (gs_end a)) -> ewp_set (wpdrv r w) a = true.
    Proof.
      induction w;simpl.
      intros.
      unfold wpdrv;simpl.
      unfold ewp_set;simpl.
      replace (fold (fun x : kat => orb (ewp x a)) {r} false) with ((ewp r a) || false).
      apply ewp_cases_epsilon_true_inv in H.
      rewrite H;auto.
      fold (ewp_set {r} a).
      rewrite ewp_of_re_set_singleton.
      apply ewp_cases_epsilon_true_inv in H.
      rewrite H.
      simpl.
      reflexivity.
    
      intros.
      simpl in H.
      apply w_in_gl_eq_last_in_LQw in H.
      simpl in H.
      apply wpdrv_correct in H.
      inversion_clear H.
      apply true_ewp_set with (x:=r0).
      rewrite <- surjective_pairing in H0.
      assert(forall z, from_gstring (to_gstring z (gs_end a0)) = z).
      induction z.
      simpl.
      reflexivity.
      simpl.
      rewrite IHz;auto.
      rewrite <- surjective_pairing.
      reflexivity.
      rewrite (H w) in H0.
      assumption.
      apply ewp_cases_epsilon_true_inv. 
      simpl in H1.
      rewrite gs_end_aux in H1.
      assumption.
    Qed. 

    Lemma gs_in_pdrv_true : 
      forall w (r:kat) a, 
        ewp_set (wpdrv r w) a = true -> In _ (kat2gl r) ((to_gstring w) (gs_end a)).
    Proof.
      induction w;simpl;intros.
      unfold wpdrv in H;simpl in H.
      apply ewp_set_true in H.
      do 2 destruct H.
      apply singleton_1 in H.
      apply ewp_cases_epsilon_true in H0.
      inv H.
      
      apply last_in_LQw_eq_w_in_gl.
      eapply wpdrv_correct.
      apply ewp_set_true in H.
      do 2 destruct H.
      econstructor 1 with x.
      simpl.
      rewrite <- surjective_pairing.
      assert(forall z, from_gstring (to_gstring z (gs_end a0)) = z).
      induction z.
      simpl.
      reflexivity.
      simpl.
      rewrite IHz;auto.
      rewrite <- surjective_pairing.
      reflexivity.
      rewrite (H1 w).
      assumption.
      apply ewp_cases_epsilon_true in H0.
      simpl.
      rewrite gs_end_aux.
      assumption.
    Qed.
    
    

    Lemma gs_not_in_pdrv :
      forall w (r:kat) a, 
        ~In _ (kat2gl r) ((to_gstring w) (gs_end a)) -> ewp_set (wpdrv r w) a = false.
    Proof.
      intros.
      apply Bool.not_true_is_false.
      intro.
      apply H.
      apply gs_in_pdrv_true;auto.
    Qed.
    
    
    Lemma gs_not_in_pdrv_true :
      forall w (r:kat) a, 
        ewp_set (wpdrv r w) a = false ->  ~In _ (kat2gl r) ((to_gstring w) (gs_end a)).
    Proof.
      intros.
      intro.
      apply  gs_in_pdrv in H0.
      rewrite H in H0.
      discriminate.
    Qed.

    Lemma ewp_set_fails_imp_gl_eq_false :
      forall w r1 r2 a,
        ewp_set (wpdrv r1 w) a <> ewp_set (wpdrv r2 w) a ->
        ~(r1 == r2).
    Proof.
      intros.
      case_eq(ewp_set (r1 %dW w) a);
        case_eq(ewp_set (r2 %dW w) a);intros.
      rewrite H0,H1 in H;elim H;auto.
      apply gs_not_in_pdrv_true in H0.
      apply gs_in_pdrv_true in H1.
      intro.
      apply H2 in H1.
      contradiction.
      apply gs_in_pdrv_true in H0.
      apply gs_not_in_pdrv_true in H1.
      intro.
      apply H2 in H0.
      contradiction.
      rewrite H0,H1 in H;elim H;auto.
    Qed.

    Lemma ewp_set_singleton :
      forall r a,
        ewp_set {r} a = ewp r a.
    Proof.
      intros.
      unfold ewp_set.
      pose proof @fold_2 kat _ _ _ {} {r} r bool _ _ false (fun x : kat => orb (ewp x a)).
      rewrite H;auto with typeclass_instances.
      clear H.
      case_eq(ewp r a);intros.
      simpl.
      reflexivity.
      simpl.
      rewrite fold_1b;auto.
      red;intros.
      intro.
      inversion H0.
      intro.
      inversion H0.
      red.
      intros.
      split;intros.
      apply singleton_1 in H0.
      left;auto.
      destruct H0.
      rewrite H0.
      apply singleton_2;auto.
      inv H0.
    Qed.
                                  
  Lemma all_ewp_set_tru_gl_eq_true :
    forall r1 r2,
      (forall w a,
         ewp_set (wpdrv r1 w) a = ewp_set (wpdrv r2 w) a) ->
      r1 == r2.
  Proof.
    intros.
    split;intros.
    red;intros.
    pose proof H (from_gstring x).
    clear H.
    revert x r1 r2 H1 H0.
    induction x;simpl;intros.
    specialize H1 with o.
    case_eq(ewp_set (r1 %dW nil) o);intros.
    unfold AtSy in H.
    rewrite H in H1.
    assert(ewp_set (r2 %dW nil) o = true).
    symmetry in H1.
    assumption.
    apply gs_in_pdrv_true in H2.
    simpl in H2.
    assumption.
    apply gs_not_in_pdrv_true in H.
    simpl in H.
    contradiction.
    specialize H1 with (last x).
    case_eq(ewp_set (r1 %dW ((o, z) :: from_gstring x)) (last x));
      case_eq(ewp_set (r2 %dW ((o, z) :: from_gstring x)) (last x));intros.
    apply gs_in_pdrv_true in H.
    apply gs_in_pdrv_true in H2.
    simpl in H.
    simpl in H2.
    rewrite <- from_to_gstring in H.
    assumption.
    rewrite H,H2 in H1.
    discriminate.
    rewrite H,H2 in H1.
    discriminate.
    apply gs_not_in_pdrv_true in H2.
    simpl in H2.
    elim H2.
    rewrite <- from_to_gstring.
    assumption.

    red;intros.
    pose proof H (from_gstring x).
    clear H.
    revert x r1 r2 H1 H0.
    induction x;simpl;intros.
    specialize H1 with o.
    case_eq(ewp_set (r2 %dW nil) o);intros.
    unfold AtSy in H.
    rewrite H in H1.
    apply gs_in_pdrv_true in H1.
    simpl in H1.
    assumption.
    apply gs_not_in_pdrv_true in H.
    simpl in H.
    contradiction.
    specialize H1 with (last x).
    case_eq(ewp_set (r1 %dW ((o, z) :: from_gstring x)) (last x));
      case_eq(ewp_set (r2 %dW ((o, z) :: from_gstring x)) (last x));intros.
    apply gs_in_pdrv_true in H.
    apply gs_in_pdrv_true in H2.
    simpl in H.
    simpl in H2.
    rewrite <- from_to_gstring in H2.
    assumption.
    rewrite H,H2 in H1.
    discriminate.
    rewrite H,H2 in H1.
    discriminate.
    apply gs_not_in_pdrv_true in H.
    simpl in H.
    elim H.
    rewrite <- from_to_gstring.
    assumption.
  Qed.

  (* Lemma all_ewp_set_tru_gl_eq_true_eq : *)
  (*   forall r1 r2, *)
  (*     (forall w a, *)
  (*        ewp_set (wpdrv r1 w) a = ewp_set (wpdrv r2 w) a) <-> *)
  (*     (forall w a, List.In a (smaller_ords (pow2 ntests)) -> *)
  (*                  ewp_set (wpdrv r1 w) a = ewp_set (wpdrv r2 w) a). *)
  (* Proof. *)
  (*   split;intros. *)
  (*   apply H. *)
  (*   apply H. *)
  (*   apply all_in_smaller_ords. *)
  (* Qed. *)

  Lemma all_ewp_set_tru_gl_eq_true_eq_set :
    forall r1 r2,
      (forall w a,
         ewp_set (wpdrv r1 w) a = ewp_set (wpdrv r2 w) a) <->
      (forall w a, a \In (smaller_ordsS (pow2 ntests)) ->
                   ewp_set (wpdrv r1 w) a = ewp_set (wpdrv r2 w) a).
  Proof.
    split;intros.
    apply H.
    apply H.
    apply all_in_smaller_ordsS.
  Qed.

  (* Lemma all_ewp_set_tru_gl_eq_true_final : *)
  (*   forall r1 r2, *)
  (*     (forall w a, List.In a (smaller_ords (pow2 ntests)) -> *)
  (*        ewp_set (wpdrv r1 w) a = ewp_set (wpdrv r2 w) a) -> *)
  (*     r1 == r2. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply all_ewp_set_tru_gl_eq_true. intros. *)
  (*   apply all_ewp_set_tru_gl_eq_true_eq. *)
  (*   apply H. *)
  (* Qed. *)

  Lemma all_ewp_set_tru_gl_eq_true_final_set :
    forall r1 r2,
      (forall w a, a \In (smaller_ordsS (pow2 ntests)) ->
         ewp_set (wpdrv r1 w) a = ewp_set (wpdrv r2 w) a) ->
      r1 == r2.
  Proof.
    intros.
    apply all_ewp_set_tru_gl_eq_true. intros.
    apply all_ewp_set_tru_gl_eq_true_eq_set.
    apply H.
  Qed.

End KATPdrvs.