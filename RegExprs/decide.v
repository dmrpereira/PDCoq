Require Export pdrvs.

Open Scope set_scope.
  
(** * Datatype of word-derivative certified pair
     We now define the datatype [ReW] witch is a pair of sets of [re], that
     also contains a word and a proof that the pair being considered corresponds
     to a word-partial derivative wrt. the original pair of regular expressions
     being tested for equivalence. *)

Section DataTypes.
  Variables r1 r2:re.

  (** First we define the notion of word partial derivative of pair of
       sets of regular expressions. *)
  
  Definition pdrvp(x:set re*set re)(a:Z) :=
    (pdrv_set (fst x) a,pdrv_set (snd x) a).
  
  Definition wpdrvp(x:set re * set re)(a:word) :=
    (wpdrv_set (fst x) a,wpdrv_set (snd x) a).

  Instance wpdrvp_m : Proper (_eq ==> _eq ==> _eq) wpdrvp.
  Proof.
    repeat red.
    intros.
    normalize_notations.
    split;intros.
    unfold _eq;simpl.
    normalize_notations.
    rewrite H0.
    destruct x.
    destruct y.
    simpl.
    inversion H.
    subst.
    rewrite H4.
    reflexivity.
    unfold _eq;simpl.
    normalize_notations.
    rewrite H0.
    destruct x.
    destruct y.
    simpl.
    inversion H.
    subst.
    rewrite H6.
    reflexivity.
  Qed.
 
  (** The type [ReW] is defined as a record with an inner coercion of [ReW] terms
       to pairs of sets, in order to allow an easier and less-verbose notion of
       equality and order, which corresponds to the already existing order of
       pairs of sets of regular expressions. *)

  Record ReW := 
    {
      dp :> set re * set re ;
      w  : word ;
      cw : dp === wpdrvp ({r1}%set,{r2}%set) w
    }.

    Global Transparent cw.

    Program Definition ReW_1st : ReW .
    Proof.
      refine(Build_ReW ({r1}%set,{r2}%set) nil _).
      unfold wpdrvp;simpl.
      constructor;unfold wpdrv_set;simpl;
        normalize_notations;auto.
    Defined.

    Corollary ReW_1st_dp_fst : fst (ReW_1st) = {r1}%set.
    Proof.
      simpl;reflexivity.
    Qed.

    Corollary ReW_1st_dp_snd : snd (ReW_1st) = {r2}%set.
    Proof.
      simpl;reflexivity.
    Qed.

    (** Now, we just provide the notions of equality and order, together with
       an instance of the [OrderedType] class, that ensures that elements of
       type [ReW] are ordered types. *)

    Definition ReW_eq(x y:ReW) :=
      _eq (A:=set re * set re) x y.

    Definition ReW_lt(x y:ReW) :=
      _lt (A:=set re * set re) x y.

    Global Program Instance ReW_ord : OrderedType ReW := {
      _eq := ReW_eq ;
      _lt := ReW_lt ;
      _cmp := _cmp (A:=set re * set re)
    }.
    Next Obligation.
      constructor.
      repeat red;order.
      repeat red;order.
      repeat red;order.
      unfold ReW_eq in H,H0;simpl in H,H0.
      normalize_notations;order.
    Defined.
    Next Obligation.
      constructor.
      unfold ReW_lt.
      repeat red;order.
      unfold ReW_lt;simpl;intros;intro.
      normalize_notations.
      apply lt_not_eq in H.
      contradiction.
    Defined.
    Next Obligation.
      case_eq(OrderedTypeEx.prod_compare x y);intros.
      constructor 2.
      unfold ReW_eq.
      normalize_notations.
      apply compare_2.
      assumption.
      constructor 1.
      apply compare_1;auto.
      constructor 3.
      apply compare_3;auto.
    Defined.

End DataTypes.

Typeclasses Opaque ReW_ord.

(** * Derivation of [ReW] terms.

     We now extend the notions of derivatives for terms of type [ReW], so that
     this type can be used in our decision procedure. The usage of these kind of
     terms facilitates the soundness proof for de decision procedures, which is
     based on the empty language property of the derivatives of the original 
     regular expressions.
 *)
(*Generalizable All Variables.*)

Section ReW_Derivation.
  Variables r1 r2:re.
  
  (** Extension of partial derivatives wrt. a symbol of type [A] *)
  
  Definition ReW_pdrv (x:ReW r1 r2)(a:Z) : ReW r1 r2.
  Proof.
    refine(match x with
             | Build_ReW K w P => 
               Build_ReW r1 r2 (pdrvp K a) (w++[a])%list _
           end).
    abstract(unfold pdrvp;
    inversion_clear P;
    simpl in *;
    constructor;normalize_notations;simpl;
    [rewrite H|rewrite H0];
    rewrite wpdrv_set_app;unfold wpdrv_set;simpl;reflexivity).
  Defined.
  
  (** Build a particular derivative of [r1] and [r2], directly from a given word. *)
  
  Definition ReW_wpdrv (w:word) : ReW r1 r2.
  Proof.
    refine(Build_ReW r1 r2 (wpdrvp (singleton r1, singleton r2) w) w _).
    abstract(reflexivity).
  Defined.
  
  Global Instance ReW_pdrv_m : Proper(_eq ==> _eq ==> _eq) ReW_pdrv.
  Proof.
    repeat red;intros.
    destruct x.
    destruct y.
    inversion H.
    normalize_notations.
    simpl.
    simpl in H3,H4.
    rewrite <- H3,<- H4.
    rewrite H0.
    clear cw0 H3 cw1 H4 H.
    unfold pdrvp.
    simpl.
    constructor;
      [rewrite H1|rewrite H2];reflexivity.
  Qed.

  (** Generalization to sets *)
  Definition ReW_wpdrv_ReW (w:word)(s:ReW r1 r2) : ReW r1 r2.
  Proof.
    destruct s.
    destruct dp0;simpl in *.
    refine(Build_ReW r1 r2 (wpdrvp (s,s0) w) (w0++w)%list _).
    abstract(unfold wpdrvp;
             simpl;
             inversion cw0;
             normalize_notations;
             constructor;[
               rewrite wpdrv_set_app;
               rewrite <- H2;
               reflexivity |
               rewrite wpdrv_set_app;
                 rewrite <- H4;
                 reflexivity]).
  Defined.
  
  Instance ReW_wpdrv_ReW_m_same_w : 
    forall w,
      Proper (_eq ==> _eq) (fun x => ReW_wpdrv_ReW w x).
  Proof.
    repeat red.
    intros.
    destruct x.
    destruct y.
    inversion H.
    simpl in H2,H3.
    Opaque ReW_wpdrv_ReW.
    simpl.
    normalize_notations.
    Transparent ReW_wpdrv_ReW.
    destruct dp0.
    destruct dp1.
    simpl.
    rewrite <- H2,<- H3.
    unfold wpdrvp.
    simpl.
    constructor;[rewrite H0|rewrite H1];reflexivity.
  Qed.
  
  Instance ReW_wpdrv_ReW_m : Proper (_eq ==> _eq ==> _eq) ReW_wpdrv_ReW.
  Proof.
    repeat red;intros.
    destruct x0.
    destruct y0.
    inversion H0.
    simpl in H3,H4.
    Opaque ReW_wpdrv_ReW.
    simpl.
    normalize_notations.
    destruct dp0;destruct dp1.
    Transparent ReW_wpdrv_ReW.
    simpl.
    rewrite <- H3,<- H4.
    constructor;simpl;normalize_notations;
    [rewrite H1 | rewrite H2];rewrite H;reflexivity.
  Qed.
  
  Lemma ReW_wpdrv_step : 
    forall w a,
      ReW_wpdrv ((@>w)++[a])%list === ReW_pdrv (ReW_wpdrv (@>w)) a.
  Proof.
    induction w0.
    intro.
    change(@>(inil)) with (@nil Z).
    change ((@nil Z)++[a])%list with [a].
    assert((ReW_wpdrv []) === ReW_1st r1 r2).
    vm_compute;split;auto.
    rewrite H.
    unfold ReW_wpdrv , ReW_pdrv.
    simpl.
    unfold wpdrvp, pdrvp.
    simpl.
    constructor;reflexivity.
    intro.
    unfold ReW_wpdrv, ReW_pdrv.
    constructor.
    simpl.
    normalize_notations.
    rewrite wpdrv_set_app.
    unfold wpdrv_set.
    simpl.
    reflexivity.
    simpl.
    normalize_notations.
    rewrite wpdrv_set_app.
    unfold wpdrv_set.
    simpl.
    reflexivity.
  Qed.

  (** Extension of derivation of [ReW] terms to finite sets *)

  Definition ReW_pdrv_set(s:ReW r1 r2)(Sig:set Z) : set (ReW r1 r2) :=
    fold (fun x:Z => add (ReW_pdrv s x)) Sig {}%set.

  Definition ReW_wpdrv_set(s:set (ReW r1 r2))(w:word) : set (ReW r1 r2) :=
    fold (fun x => add (ReW_wpdrv_ReW w x)) s {}%set.

  Instance add_ReW_pdrv : forall x0, Proper (_eq ==> _eq ==> _eq) 
                                 (fun x1 : Z => add (ReW_pdrv x0 x1)).
  Proof.
    repeat red;intros.
    split;intros.
    apply add_iff in H1;destruct H1.
    rewrite <- H1.
    apply add_1.
    apply ReW_pdrv_m;auto.
    apply add_2;auto.
    apply H0;auto.
    apply add_iff in H1;destruct H1.
    rewrite <- H1.
    apply add_1.
    apply ReW_pdrv_m;auto.
    apply add_2.
    apply H0;auto.
  Qed.

  Instance add_ReW_wpdr : forall x0, Proper (_eq ==> _eq ==> _eq)
                                 (fun x : word => add (ReW_wpdrv_ReW x x0)).
  Proof.
    repeat red;intros.
    split;intros.
    apply add_iff in H1;destruct H1.
    rewrite <- H1.
    apply add_1.
    rewrite H.
    reflexivity.
    apply add_2.
    rewrite <- H0;assumption.
    apply add_iff in H1.
    destruct H1.
    rewrite <- H in H1.
    rewrite H1.
    apply add_1;auto.
    rewrite <- H0 in H1.
    apply add_2;auto.
  Qed.

  Lemma add_ReW_pdrv_transp : forall x0,
                                transpose _eq (fun x1 : Z => add (ReW_pdrv x0 x1)).
  Proof.
    repeat red;intros.
    split;intros;
    apply add_iff in H;
    destruct H.
    rewrite <- H.
    apply add_2;apply add_1;auto.
    apply add_iff in H;destruct H.
    rewrite H.
    apply add_1;auto.
    do 2 apply add_2;auto.
    intuition.
    apply add_iff in H;destruct H. 
    apply add_1;auto.
    do 2 apply add_2;auto.
  Qed.

  Lemma ReW_pdrv_set_elem_in : forall sig s a,
                                 a \In sig -> ReW_pdrv s a \In ReW_pdrv_set s sig.
  Proof.
    induction sig using set_induction.
    intros s a H1.
    apply H in H1.
    elim H1.
    intros.
    apply H0 in H1.
    destruct H1.
    unfold ReW_pdrv_set.
    rewrite (@fold_2 Z _ _ _ sig1 sig2 x (set (ReW r1 r2)) _eq OT_Equivalence 
                     (empty (A:=ReW r1 r2)) (fun x0 : Z => add (ReW_pdrv s x0))
                     _ (add_ReW_pdrv_transp s) H H0).
    apply add_1.
    apply ReW_pdrv_m;auto.
    eapply IHsig1 with s a in H1.
    unfold ReW_pdrv_set.
    rewrite (@fold_2 Z _ _ _ sig1 sig2 x (set (ReW r1 r2)) _eq OT_Equivalence 
                     (empty (A:=ReW r1 r2)) (fun x0 : Z => add (ReW_pdrv s x0))
                     _ (add_ReW_pdrv_transp s) H H0).
    apply add_2.
    apply H1.
  Qed.

  Lemma A_leibniz : forall x y:Z, x === y -> x = y.
  Proof.
    induction 1.
    reflexivity.
  Qed.

  Global Instance ReW_pdrv_set_aux_m : Proper(eq ==> _eq ==> _eq)
                                             (fun x a => ReW_pdrv_set x a).
  Proof.
    repeat red;intros.
    rewrite H.
    clear H x.
    revert x0 y0 H0 a.
    induction x0 using set_induction.
    intros y0 H1.
    unfold ReW_pdrv_set.
    rewrite fold_1b;auto.
    rewrite H1 in H.
    rewrite fold_1b;auto.
    intros.
    unfold ReW_pdrv_set.
    generalize (@fold_2 Z _ _ _ x0_1 x0_2 x (set (ReW r1 r2)) _eq OT_Equivalence {}%set
                (fun x0 : Z => add (ReW_pdrv y x0)) (add_ReW_pdrv _) (add_ReW_pdrv_transp y) H H0).
    intro.
    split;intros.
    apply H2 in H3.
    cut(SetProperties.Add x x0_1 y0).
    intro.
    generalize (@fold_2 Z _ _ _ x0_1 y0 x (set (ReW r1 r2)) _eq OT_Equivalence {}%set
               (fun x1 : Z => add (ReW_pdrv y x1)) (add_ReW_pdrv _) (add_ReW_pdrv_transp y) H H4).
    intro.
    apply H5.
    apply add_iff in H3;destruct H3.
    apply add_1;auto.
    apply add_2;auto.
    apply Add_Equal in H0.
    apply Add_Equal.
    rewrite <- H0;auto.
    rewrite H1.
    reflexivity.
    cut(SetProperties.Add x x0_1 y0).
    intro.
    apply H2.
    generalize (@fold_2 Z _ _ _ x0_1 y0 x (set (ReW r1 r2)) _eq OT_Equivalence {}%set
                   (fun x1 : Z => add (ReW_pdrv y x1)) (add_ReW_pdrv _) (add_ReW_pdrv_transp y) H H4).
    intro.
    apply H5 in H3.
    apply add_iff in H3;destruct H3.
    apply add_1;auto.
    apply add_2.
    assumption.
    apply Add_Equal in H0.
    apply Add_Equal.
    rewrite <- H0;auto.
    rewrite H1;auto.
    reflexivity.
  Qed.

  Global Instance ReW_pdrv_set_aux_2_m : Proper(_eq ==> eq ==> _eq)
                                               (fun x a => ReW_pdrv_set x a).
  Proof.
    repeat red;intros.
    rewrite H0.
    clear H0 x0.
    revert y0 a.
    induction y0 using set_induction.
    unfold ReW_pdrv_set.
    rewrite fold_1b;auto.
    rewrite fold_1b;auto.
    intro.
    unfold ReW_pdrv_set.
    generalize (@fold_2 Z _ _ _ y0_1 y0_2 x0 (set (ReW r1 r2)) _eq OT_Equivalence 
                        {}%set
                        (fun x1 : Z => add (ReW_pdrv x x1)) (add_ReW_pdrv _) (add_ReW_pdrv_transp x) H0 H1).
    intro.
    generalize (@fold_2 Z _ _ _ y0_1 y0_2 x0 (set (ReW r1 r2)) _eq OT_Equivalence 
                        {}%set
                        (fun x1 : Z => add (ReW_pdrv y x1)) (add_ReW_pdrv _) (add_ReW_pdrv_transp y) H0 H1).
    intro.
    split;intros.
    apply H3.
    apply H2 in H4.
    apply add_iff in H4;destruct H4.
    apply add_1.
    rewrite <- H4.
    eapply ReW_pdrv_m;auto.
    specialize IHy0_1 with a.
    destruct IHy0_1.
    apply add_2.
    apply H5.
    assumption.
    apply H2.
    apply H3 in H4.
    apply add_iff in H4;destruct H4.
    apply add_1.
    rewrite <- H4.
    apply ReW_pdrv_m;auto.
    apply add_2.
    specialize IHy0_1 with a.
    destruct IHy0_1.
    apply H6;auto.
  Qed.

  Global Instance ReW_pdrv_set_m : Proper(_eq ==> _eq ==> _eq) 
                                         (fun x a => ReW_pdrv_set x a).
  Proof.
    repeat red.
    intros.
    revert x0 y0 H0.
    induction x0 using set_induction.
    unfold ReW_pdrv_set.
    intros y0 H1.
    rewrite fold_1b;auto.
    rewrite H1 in H0.
    rewrite fold_1b;auto.
    intros y0 H2.
    split;intros.
    unfold ReW_pdrv_set in H3 |- *.
    generalize (@fold_2 Z _ _ _ x0_1 x0_2 x0 (set (ReW r1 r2)) _eq OT_Equivalence 
                        {}%set
                        (fun x0 : Z => add (ReW_pdrv x x0)) (add_ReW_pdrv _) (add_ReW_pdrv_transp x) H0 H1);
      intros.
    cut(SetProperties.Add x0 x0_1 y0).
    intro.
    generalize (@fold_2 Z _ _ _ x0_1 y0 x0 (set (ReW r1 r2)) _eq OT_Equivalence 
                        {}%set
                        (fun x1 : Z => add (ReW_pdrv y x1)) (add_ReW_pdrv _) (add_ReW_pdrv_transp y) H0 H5);
      intros.
    apply H6.
    apply H4 in H3.
    apply add_iff in H3.
    destruct H3.
    apply add_1.
    rewrite <- H3.
    apply ReW_pdrv_m;auto.
    clear H4 H6.
    apply add_2.
    revert H3.
    apply ReW_pdrv_set_aux_2_m;auto.
    apply Add_Equal in H1.
    apply Add_Equal.
    rewrite <- H1.
    rewrite H2.
    reflexivity.
    unfold ReW_pdrv_set in H3 |- *.
    generalize (@fold_2 Z _ _ _ x0_1 x0_2 x0 (set (ReW r1 r2)) _eq OT_Equivalence 
                        {}%set
                        (fun x0 : Z => add (ReW_pdrv x x0)) (add_ReW_pdrv _) (add_ReW_pdrv_transp x) H0 H1);
      intros.
    cut(SetProperties.Add x0 x0_1 y0).
    intro.
    generalize (@fold_2 Z _ _ _ x0_1 y0 x0 (set (ReW r1 r2)) _eq OT_Equivalence 
                        {}%set
                        (fun x1 : Z => add (ReW_pdrv y x1)) (add_ReW_pdrv _) (add_ReW_pdrv_transp y) H0 H5);
      intros.
    apply H4.
    apply H6 in H3.
    apply add_iff in H3.
    destruct H3.
    apply add_1.
    rewrite <- H3.
    apply ReW_pdrv_m;auto.
    clear H4 H6.
    apply add_2.
    revert H3.
    apply ReW_pdrv_set_aux_2_m;auto.
    apply Add_Equal in H1.
    apply Add_Equal.
    rewrite <- H1.
    rewrite H2.
    reflexivity.
  Qed.
  
End ReW_Derivation.

Notation "x %d[ y  ]" := 
  (ReW_pdrv _ _ x y)
    (at level 45, y at next level).

Notation "x %dS[ y  ]" := 
  (ReW_pdrv_set _ _ x y)
    (at level 45, y at next level).

(** * Filtering the new pairs of derivatives

     Not all new derivatives are considered for further processing. If a new pair [x]
     already exists in the historic set [h], then it is discarded (this happens every time is appears along the execution of the main procedure. The only role that this function, named [ReW_pdrv_set_filtered] plays is to avoid cyclic behavior of the procedure. *)

Section ReW_Derivation_filtered.
  Variables r1 r2:re.
  
  Definition ReW_pdrv_set_filtered(x:ReW r1 r2)(h:set (ReW r1 r2))
             (sig:set Z) : set (ReW r1 r2) :=
    filter (fun x => negb (mem x h)) (x %dS[sig]).

  Instance ReW_negb_m : 
   forall y0, Proper (_eq ==> eq) (fun x2 : ReW r1 r2 => negb (x2 \in y0)).
  Proof.
    repeat red;intros.
    rewrite H.
    reflexivity.
  Qed.

  Global Instance ReW_pdrv_set_filtered_m :
    Proper(_eq ==> _eq ==> _eq ==> _eq) ReW_pdrv_set_filtered.
  Proof.
    repeat red;intros.
    split;intros.
    unfold ReW_pdrv_set_filtered in *.
    apply filter_iff in H2;auto with typeclass_instances.
    apply filter_iff;auto with typeclass_instances.
    rewrite <- H.
    rewrite <- H1.
    rewrite H0 in H2.
    assumption.
    unfold ReW_pdrv_set_filtered in *.
    apply filter_iff in H2;auto with typeclass_instances.
    apply filter_iff;auto with typeclass_instances.
    rewrite H.
    rewrite H1.
    rewrite <- H0 in H2.
    assumption.
  Qed.

  (** Exclusion of elements already present in the historic set [h] *)
  Lemma ReW_pdrv_set_filtered_no_dup : forall x h sig y,
                                         y \In ReW_pdrv_set_filtered x h sig ->
                                         ~y \In h.
  Proof.
    intros.
    unfold ReW_pdrv_set_filtered in H.
    apply filter_iff in H;auto with typeclass_instances.
    destruct H.
    intro.
    apply mem_iff in H1.
    apply Bool.negb_true_iff in H0.
    rewrite H0 in H1;discriminate.
  Qed.

  Global Instance ReW_pdrv_add_m : 
    forall r:ReW r1 r2, 
      Proper (_eq ==> _eq ==> _eq) (fun x0 : Z => add (r %d[ x0 ])).
  Proof.
    repeat red.
    split;intros.
    rewrite H,H0 in H1.
    assumption.
    rewrite H,H0;assumption.
  Qed.
  
  Fact ReW_pdrv_add_transpose :
    forall r:ReW r1 r2, 
      transpose Equal (fun x0 : Z => add (r %d[ x0 ])).
  Proof.
    repeat red.
    split;intros.
    apply add_iff in H.
    destruct H.
    rewrite H.
    apply add_2;apply add_1;auto.
    apply add_iff in H.
    destruct H;
      [rewrite H;apply add_1 | apply add_2;apply add_2];auto.
    apply add_iff in H.
    destruct H.
    rewrite H;apply add_2;apply add_1;auto.
    apply add_iff in H;destruct H.
    rewrite H;apply add_1;auto.
    apply add_2;apply add_2;auto.
  Qed.

  Hint Resolve ReW_pdrv_add_transpose : typeclass_instances.

  Lemma ReW_in_pdrv_set : 
    forall sig (r:ReW r1 r2) a, a \In sig ->
                                (ReW_pdrv _ _ r a) \In (ReW_pdrv_set _ _ r sig).
  Proof.
    intro sig.
    induction sig using set_induction.
    intros.
    generalize(H a).
    intro.
    contradiction.
    intros.
    eapply ReW_pdrv_set_m.
    reflexivity.
    reflexivity.
    apply Add_Equal in H0.
    rewrite H0.
    unfold ReW_pdrv_set.
    rewrite H0 in H1.
    apply add_iff in H1.
    destruct H1.
    rewrite fold_add;auto with typeclass_instances.
    apply add_1.
    rewrite H1.
    reflexivity.
    rewrite fold_add;auto with typeclass_instances.
    apply add_2.
    apply IHsig1;assumption.
  Qed.

  Lemma ReW_pdrv_set_filtered_ex : 
    forall x h sig y,
      y \In ReW_pdrv_set_filtered x h sig -> 
      exists a, a \In sig /\ y === ReW_pdrv r1 r2 x a.
  Proof.
    intros.
    unfold ReW_pdrv_set_filtered in H.
    apply filter_iff in H;auto with typeclass_instances.
    destruct H.
    revert sig y H H0.
    induction sig using set_induction.
    intros.
    unfold ReW_pdrv_set in H0.
    rewrite fold_1b in H0;auto with typeclass_instances.
    inversion H0.
    intro y.
    unfold ReW_pdrv_set.
    intros.
    generalize (@fold_2 Z _ _ _ sig1 sig2 x0 (set (ReW r1 r2)) _eq OT_Equivalence 
                        {}%set
                        (fun x1 : Z => add (ReW_pdrv r1 r2 x x1)) (ReW_pdrv_add_m x) 
                        (add_ReW_pdrv_transp r1 r2 x) H H0);intro.
    rewrite H3 in H1.
    apply add_iff in H1.
    destruct H1.
    exists x0.
    split.
    apply H0;auto.
    rewrite H1;reflexivity.
    apply IHsig1 in H1;auto.
    destruct H1  as [a [h4 H5]].
    exists a.
    split.
    apply H0;auto.
    assumption.
  Qed.
  
End ReW_Derivation_filtered.

Notation "x %dF[ h , y  ]" := 
  (ReW_pdrv_set_filtered _ _ x h y)
    (at level 45, h at next level, y at next level).

  (** * Empty language property for [ReW]
     
     We now extend the notion of the syntactical property of the empty language
     for terms of type [ReW]. This notion if fulcral for finding and exhibiting
     counter-examples of the equivalence of regular expressions.
     *)

Section ReW_Emptyness.
  Variables r1 r2:re.

  Definition c_of_rep(x:set re  * set re) :=
    Bool.eqb (c_of_re_set (fst x)) (c_of_re_set (snd x)).
  
  Global Instance c_of_rep_m : Proper(_eq ==> _eq) c_of_rep.
  Proof.
    repeat red.
    intros.
    destruct x;destruct y;normalize_notations.
    unfold c_of_rep;simpl in *.
    inversion_clear H.
    rewrite H0.
    rewrite H1.
    reflexivity.
  Qed.

  Definition c_of_ReW(x:ReW r1 r2) :=
    c_of_rep x.

  Global Instance c_of_ReW_m : Proper(_eq ==> _eq) c_of_ReW.
  Proof.
    repeat red;intros.
    unfold c_of_ReW.
    apply c_of_rep_m.
    assumption.
  Qed.

  Definition c_of_ReW_set (x:set (ReW r1 r2)) : bool :=
    fold (fun x => andb (c_of_ReW x)) x true.

  Global Instance andb_c_of_ReW_m : 
    Proper (_eq ==> _eq ==> _eq) (fun x : ReW r1 r2 => andb (c_of_ReW x)). 
  Proof.
    repeat red.
    intros.
    rewrite H0.
    apply (c_of_ReW_m) in H.
    rewrite H.
    reflexivity.
  Qed.

  Lemma andb_c_of_ReW_m_transpose : 
    transpose _eq (fun x : ReW r1 r2 => andb (c_of_ReW x)).
  Proof.
    repeat red;intros.
    destruct(c_of_ReW x).
    simpl;auto.
    simpl.
    rewrite Bool.andb_false_r.
    reflexivity.
  Qed.

  Global Instance c_of_ReW_set_m : Proper(_eq ==> _eq) c_of_ReW_set.
  Proof.
    repeat red.
    induction x using set_induction;intros.
    unfold c_of_ReW_set.
    rewrite fold_1b;auto.
    rewrite H0 in H.
    rewrite fold_1b;auto.
    assert(SetProperties.Add x3 x1 y).
    apply Add_Equal in H0.
    apply Add_Equal.
    rewrite <- H0;symmetry;auto.
    unfold c_of_ReW_set.
    generalize (@fold_2 (ReW r1 r2) _ _ _ x1 x2 x3 (bool) _eq OT_Equivalence true
                        (fun x : ReW r1 r2 => andb (c_of_ReW x)) _ (andb_c_of_ReW_m_transpose) H H0);
      intro.
    rewrite H3.
    generalize (@fold_2 (ReW r1 r2) _ _ _ x1 y x3 (bool) _eq OT_Equivalence true
                        (fun x : ReW r1 r2 => andb (c_of_ReW x)) _ (andb_c_of_ReW_m_transpose) H H2);
      intro.
    rewrite H4.
    reflexivity.
  Qed.

  Lemma wit_in_c_of_ReW_set : forall s,
                                c_of_ReW_set s = false -> exists x, x \In s /\
                                                                    c_of_ReW x = false.
  Proof.
    induction s using set_induction.
    intro.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    unfold c_of_ReW_set in H0.
    vm_compute in H0.
    discriminate.
    intro.
    unfold c_of_ReW_set in H1.
    generalize (@fold_2 (ReW r1 r2) _ _ _ s1 s2 x (bool) _eq OT_Equivalence true
                        (fun x : ReW r1 r2 => andb (c_of_ReW x)) _ (andb_c_of_ReW_m_transpose) H H0).
    intro.
    rewrite H2 in H1;clear H2.
    case_eq(c_of_ReW x).
    intro.
    rewrite H2 in H1.
    simpl in H1.
    apply IHs1 in H1.
    destruct H1.
    destruct H1.
    exists x0.
    split;auto.
    apply H0;auto.
    intro.
    exists x.
    split;auto.
    apply H0;auto.
  Qed.

  Lemma wit_all_in_c_of_ReW_set : forall s,
                                    c_of_ReW_set s = true -> forall x, x \In s ->
                                                                       c_of_ReW x = true.
  Proof.
    induction s using set_induction.
    intros.
    apply H in H1;elim H1.
    intros.
    generalize (@fold_2 (ReW r1 r2) _ _ _ s1 s2 x (bool) _eq OT_Equivalence true
                        (fun x : ReW r1 r2 => andb (c_of_ReW x)) _ (andb_c_of_ReW_m_transpose) H H0).
    intro.
    apply H0 in H2.
    unfold c_of_ReW_set in H1;rewrite H3 in H1.
    destruct H2.
    rewrite <- H2.
    case_eq(c_of_ReW x);intros;auto.
    rewrite H4 in H1;simpl in H1;discriminate.
    case_eq(c_of_ReW x);intros;auto.
    rewrite H4 in H1;simpl in H1.
    generalize(IHs1 H1 _ H2);auto.
    rewrite H4 in H1;discriminate.
  Qed.

  (** *Acrescentar propriedades das constantes para os conjuntos *)

  Lemma c_of_ReW_nequiv : forall x, c_of_ReW x = false ->
                                    c_of_rep x = false.
  Proof.
    intros.
    unfold c_of_ReW in H.
    assumption.
  Qed.

  Lemma c_of_ReW_wpdrv : forall x b,
                           c_of_ReW x = b -> exists w, c_of_rep(wpdrvp ({r1}%set,{r2}%set) w) = b.
  Proof.
    intros.
    destruct x.
    exists w0.
    unfold c_of_ReW in H.
    simpl in H.
    rewrite <- cw0.
    assumption.
  Qed.

  Lemma c_of_rep_diff_constant : forall x y w,
                                   c_of_rep(wpdrvp (x,y) w) = false ->
                                   c_of_re_set(wpdrv_set x w) <> c_of_re_set(wpdrv_set y w).
  Proof.
    intros.
    unfold c_of_rep in H.
    intro.
    simpl in H.
    apply Bool.eqb_false_iff in H.
    contradiction.
  Qed.

  Lemma c_of_ReW_diff_wpdrvs_orig : forall x,
                                      c_of_ReW x = false -> exists w,
                                                              c_of_re_set(wpdrv r1 w) <> c_of_re_set(wpdrv r2 w).
  Proof.
    intros.
    apply c_of_ReW_wpdrv in H.
    destruct H.
    apply c_of_rep_diff_constant in H.
    exists x0.
    do 2 rewrite wpdrv_set_singleton in H.
    assumption.
  Qed.

  (** Lemma that proves the inequivalence of regular expressions *)

  Lemma c_of_ReW_diff_wpdrvs_Srels : forall x,
                                       c_of_ReW x = false -> r1 !∼ r2.
  Proof.
    intros.
    apply c_of_ReW_diff_wpdrvs_orig in H.
    destruct H.
    case_eq(εs(∂w(r1,x0)));intros.
    case_eq(εs(∂w(r2,x0)));intros.
    rewrite H0,H1 in H;elim H;auto.
    apply c_of_re_set_has_nil in H0.
    apply c_of_re_set_has_not_nil in H1.
    intro.
    apply wpdrv_correct in H0.
    apply H1.
    apply wpdrv_correct.
    inversion_clear H0.
    constructor.
    apply H2 in H3.
    assumption.
    case_eq(εs(∂w(r2,x0)));intros.
    intro.
    apply c_of_re_set_has_nil in H1.
    apply c_of_re_set_has_not_nil in H0.
    apply H0.
    apply wpdrv_correct in H1.
    apply wpdrv_correct.
    inversion_clear H1.
    constructor.
    apply H2 in H3.
    assumption.
    rewrite H0,H1 in H;elim H;auto.
  Qed.

  Lemma false_in_c_of_ReW_set : forall x s,
                                  c_of_ReW x = false -> x \In s -> c_of_ReW_set s = false.
  Proof.
    intros x s.
    revert s x.
    induction s using set_induction.
    intros.
    apply H in H1;inversion H1.
    intros.
    generalize (@fold_2 (ReW r1 r2) _ _ _ s1 s2 x (bool) _eq OT_Equivalence true
                        (fun x : ReW r1 r2 => andb (c_of_ReW x)) _ (andb_c_of_ReW_m_transpose) H H0).
    apply H0 in H2.
    destruct H2.
    intro.
    unfold c_of_ReW_set.
    rewrite H3.
    rewrite H2.
    rewrite H1.
    simpl.
    reflexivity.
    intro.
    rewrite H3.
    generalize(IHs1 _ H1 H2);intro.
    unfold c_of_ReW_set in H4.
    rewrite H4.
    rewrite Bool.andb_comm.
    simpl.
    reflexivity.
  Qed.

End ReW_Emptyness.

Notation "%e_p x"  := (c_of_rep x)(at level 30).
Notation "%e_rew c " := (c_of_ReW _ _ c)(at level 30).

Section DerivativesGenerator.
  Variables r1 r2:re.

  Definition _cmpRP := _cmp (A:=set re).

  Inductive DisjPP (h s:set (ReW r1 r2)) : Prop :=
  | disjPP : inter h s === {}%set -> DisjPP h s.

  Inductive DP (h s:set (ReW r1 r2)) : Prop :=
  | is_dpt : inter h s === {} -> (*DisjPP h s -> *)
             c_of_ReW_set _ _ h = true -> DP h s.

  Inductive StepFastCase' : Type :=
  |Process' : StepFastCase' 
  |TermTrue' : set (ReW r1 r2) -> StepFastCase' 
  |TermFalse' : ReW r1 r2 -> StepFastCase'.
  
  Generate OrderedType StepFastCase'.
  
  Definition StepFast' (h s:set (ReW r1 r2))(sig:set Z) : 
    (set (ReW r1 r2) * set (ReW r1 r2)) * StepFastCase' :=
    match choose s with
      | None => ((h,s),TermTrue' h)
      | Some x => 
        if c_of_ReW _ _ x then
          let h' := add x h in 
          let s' := remove x s in 
          let ns :=  ReW_pdrv_set_filtered _ _ x h' sig in 
          ((h',union ns s'),Process')
        else
          ((h,s),TermFalse' x)
    end.

End DerivativesGenerator.

Require Export wf_extra.

Section Cardinality_Properties.
  Variables r1 r2 : re.

  Lemma ReW_in_PD_fst : forall (x:ReW r1 r2) (s:set (ReW r1 r2)), 
                          x \In s -> cardinal (fst x) <= cardinal (PD r1).
  Proof.
    intros.
    destruct x.
    simpl.
    destruct dp0.
    simpl in *.
    unfold wpdrvp in cw0.
    simpl in cw0.
    inversion_clear cw0.
    normalize_notations.
    rewrite H0.
    apply subset_cardinal.
    rewrite wpdrv_set_singleton.
    red;intros.
    eapply all_wpdrv_in_PD with (<@w0).
    assumption.
  Qed.

  Lemma ReW_in_PD_snd : forall x (s:set (ReW r1 r2)), 
                          x \In s -> cardinal (snd x) <= cardinal (PD r2).
  Proof.
    intros.
    destruct x.
    simpl.
    destruct dp0.
    simpl in *.
    unfold wpdrvp in cw0.
    simpl in cw0.
    inversion_clear cw0.
    normalize_notations.
    rewrite H1.
    apply subset_cardinal.
    rewrite wpdrv_set_singleton.
    red;intros.
    eapply all_wpdrv_in_PD with (<@w0).
    assumption.
  Qed.

  Definition ReW_to_set_re (s:set (ReW r1 r2)) : set (set re * set re) :=
    fold (fun x => add (@dp r1 r2 x)) s  {}%set.

  Instance add_dp_m : Proper (_eq ==> _eq ==> _eq) 
                             (fun x : ReW r1 r2 => add (@dp r1 r2 x)).
  Proof.
    Opaque _eq.
    repeat red;intros.
    change (_eq x y) with (prod_eq (Equal_pw (set re) re SetInterface.In)
        (Equal_pw (set re) re SetInterface.In) x y) in H.
    Transparent _eq.
    split;intros;normalize_notations.
    abstract(apply add_iff in H1;destruct H1;
    [apply add_1;rewrite <- H;assumption|apply add_2;apply H0 ; auto]).
    abstract(apply add_iff in H1;destruct H1;
             [apply add_1;rewrite  H;assumption|apply add_2;apply H0;auto]).
  Qed.

  Lemma add_pd_transpose :
    transpose _eq (fun x : ReW r1 r2 => add (@dp r1 r2 x)).
  Proof.
    repeat red;intros.
    split;intros;
    apply add_iff in H;
    destruct H;
    try (rewrite <- H).
    abstract(apply add_2;apply add_1;auto).
    apply add_iff in H;destruct H.
    abstract(rewrite <- H;apply add_1;auto).
    abstract(do 2 apply add_2;auto).
    abstract(apply add_2;apply add_1;auto).
    apply add_iff in H;destruct H.
    abstract(rewrite <- H;apply add_1;auto).
    abstract(do 2 apply add_2;auto).
  Qed.

  Hint Resolve add_pd_transpose : typeclass_instances.
    
  Lemma in_powerset_PDs : 
    forall (s:set (ReW r1 r2)),
      (ReW_to_set_re s)[<=]cart_prod (powerset(PD(r1))) (powerset(PD(r2))).
  Proof.
    induction s using set_induction;intros.
    red;intros.
    unfold ReW_to_set_re in H0.
    abstract(rewrite fold_1b in H0;auto;inversion H0).
    red;intros.
    unfold ReW_to_set_re in H1.
    rewrite (@fold_2 (ReW r1 r2) _ _ _ s1 s2 x (set (set re * set re)) _eq _ {}%set)
      in H1;auto with typeclass_instances.
    apply add_iff in H1.
    destruct H1.
    rewrite <- H1.
    destruct x.
    simpl.
    apply cart_prod_spec.
    destruct dp0.
    simpl in *;split.
    unfold wpdrvp in cw0.
    simpl in cw0.
    inversion cw0.
    subst.
    rewrite H5.
    rewrite wpdrv_set_singleton.
    apply powerset_spec.
    red;intros.
    unfold wpdrv in H2.
    apply all_wpdrv_in_PD with (<@w0);assumption.
    unfold wpdrvp in cw0.
    simpl in cw0.
    inversion cw0.
    subst.
    rewrite H7.
    rewrite wpdrv_set_singleton.
    apply powerset_spec.
    red;intros.
    unfold wpdrv in H2.
    apply all_wpdrv_in_PD with (<@w0);assumption.
    apply IHs1.
    assumption.
  Qed.

  Lemma in_ReW_in_set_re : forall (x:ReW r1 r2) s,
                             x \In s -> (@dp r1 r2 x) \In  (ReW_to_set_re s).
  Proof.
    induction s using set_induction;intros.
    apply H in H0.
    elim H0.
    unfold ReW_to_set_re.
    rewrite (@fold_2 (ReW r1 r2) _ _ _ s1 s2 x0 _);auto with 
                                                   typeclass_instances.
    apply H0 in H1.
    destruct H1.
    apply add_1;auto.
    apply add_2.
    apply IHs1;auto.
  Qed.

  Lemma in_ReW_in_set_re_rev : forall (x:ReW r1 r2) s,
                                 (@dp r1 r2 x) \In  (ReW_to_set_re s) -> x \In s.
  Proof.
    induction s using set_induction;intros.
    unfold ReW_to_set_re in H0.
    rewrite fold_1b in H0;auto with typeclass_instances.
    inversion H0.
    unfold ReW_to_set_re in H1.
    rewrite (@fold_2 (ReW r1 r2) _ _ _ s1 s2 x0 (set (set re * set re)) _eq _ {}%set)
      in H1;auto with typeclass_instances.
    apply add_iff in H1;destruct H1.
    apply H0;auto.
    apply IHs1 in H1.
    apply H0;auto.
  Qed.

  Lemma ReW_to_set_re_same_card : forall s:set (ReW r1 r2),
                                    cardinal s = cardinal (ReW_to_set_re s).
  Proof.
    intros.
    induction s using set_induction.
    unfold ReW_to_set_re.
    rewrite fold_1b;auto with typeclass_instances.
    apply cardinal_Empty in H.
    rewrite H.
    vm_compute.
    reflexivity.
    unfold ReW_to_set_re.
    rewrite (@fold_2 (ReW r1 r2) _ _ _ s1 s2 x _);auto with 
                                                  typeclass_instances.
    apply Add_Equal in H0.
    rewrite H0.
    rewrite add_cardinal_2;auto.
    rewrite add_cardinal_2;auto.
    intro.
    apply in_ReW_in_set_re_rev in H1.
    contradiction.
  Qed.
  
End Cardinality_Properties.

Section WellFoundedDecide.
  Variables r1 r2:re.

  Definition MAX_fst := S |<r1>|.
                          Definition MAX_snd := S |<r2>|.

                                                  Require Import NArith.
  
  Definition MAX := Nsucc (pow2N MAX_fst * pow2N MAX_snd)%N.

  Definition LLim := (lim_cardN (ReW r1 r2) MAX).
  
  Theorem LLim_wf : well_founded LLim.
  Proof.
    unfold LLim.
    apply lim_cardN_wf.
  Qed.

  Fixpoint guard (n : nat) (wf : well_founded (LLim)) : 
    well_founded (LLim) :=
    match n with
      | O => wf
      | S n' => fun x => Acc_intro x (fun y _ => guard n' (guard n' wf) y)
    end.

End WellFoundedDecide.

Section DecreasingMeasures.
  Variables r1 r2:re.

  Lemma disj_h_s_inv : 
    forall (h s : set (ReW r1 r2)) (sig : set Z),
      inter h s === {} -> inter (fst (fst (StepFast' _ _ h s sig)))
                                (snd (fst (StepFast' _ _ h s sig))) === {}.
  Proof.
    intros.
    split;intros.
    apply inter_iff in H0.
    destruct H0 as [H1 H2].
    revert H1 H2.
    unfold StepFast';simpl in *.
    case_eq(choose s).
    intros r Hr.
    destruct(c_of_ReW _ _ r);simpl in *.
    apply choose_1 in Hr.
    intros H1 H2;apply add_iff in H1;destruct H1.
    apply union_1 in H2;destruct H2.
    apply ReW_pdrv_set_filtered_no_dup in H1.
    rewrite H0 in H1.
    elim H1.
    apply add_1;reflexivity.
    apply remove_iff in H1.
    destruct H1;contradiction.
    apply union_1 in H2;destruct H2.
    apply ReW_pdrv_set_filtered_no_dup in H1.
    elim H1.
    apply add_2;assumption.
    apply remove_iff in H1;destruct H1.
    (*apply e;apply inter_iff;split;auto.*)
    assert(a \In inter h s) by (apply inter_iff;split;auto).
    apply H in H3;inversion H3.
    intros;apply H.
    apply inter_iff;auto.
    simpl.
    intros.
    assert(a \In inter h s) by (apply inter_iff;split;auto).
    apply H in H3;inversion H3.
    inversion H0.
  Qed.

  Lemma c_of_Rew_set_h_inv : forall (h s : set (ReW r1 r2)) (sig : set Z),
                               inter h s === {} -> c_of_ReW_set _ _ h = true -> 
                               c_of_ReW_set _ _ (fst (fst (StepFast' _ _ h s sig))) = true.
  Proof.
    intros.
    case_eq(choose s);intros.
    case_eq(%e_rew r);intros.
    unfold StepFast'.
    rewrite H1,H2.
    simpl.
    unfold c_of_ReW_set.
    rewrite fold_add;auto with typeclass_instances.
    rewrite H2;simpl.
    exact H0.
    repeat red.
    intros.
    destruct(%e_rew x).
    simpl.
    reflexivity.
    simpl.
    rewrite andb_comm;simpl.
    reflexivity.
    intro.
    apply choose_1 in H1.
    assert(r \In inter h s).
    apply inter_iff;auto with typeclass_instances.
    apply H in H4;inversion H4.
    unfold StepFast'.
    rewrite H1,H2.
    simpl.
    exact H0.
    unfold StepFast'.
    rewrite H1.
    simpl.
    assumption.
  Qed.
  
  Lemma DP_upd : forall (h s : set (ReW r1 r2)) (sig : set Z),
                   DP _ _ h s -> 
                   DP _ _ (fst (fst (StepFast' _ _ h s sig)))
                      (snd (fst (StepFast' _ _ h s sig))).
  Proof.
    intros.
    destruct H.
    constructor.
    apply disj_h_s_inv with (sig:=sig) in H.
    exact H.
    apply c_of_Rew_set_h_inv;assumption.
  Qed.
  

  Lemma  cardinal_less_than_pow2 : forall h,
                                     cardinal (ReW_to_set_re r1 r2 h) <= pow2 (MAX_fst r1) * pow2 (MAX_snd r2).
  Proof.
    intros.
    generalize(in_powerset_PDs r1 r2 h).
    intro.
    eapply Le.le_trans with 
    (cardinal (cart_prod (powerset (PD r1)) (powerset (PD r2)))).
    apply subset_cardinal.
    assumption.
    rewrite cart_prod_card.
    unfold MAX_fst,MAX_snd.
    do 2 rewrite pow2_S.
    do 2 rewrite powerset_cardinal.
    generalize( PD_upper_bound r1).
    generalize( PD_upper_bound r2).
    intros.
    apply pow2_le in H0.
    apply pow2_le in H1.
    rewrite pow2_S in H0,H1.
    apply Mult.mult_le_compat;assumption.
  Qed. 

  Lemma LLim_disj_h_s : forall (h s : set (ReW r1 r2)) (sig : set Z),
                          inter h s === {} -> snd (StepFast' _ _ h s sig) = Process' _ _->
                          LLim _ _ (fst (fst (StepFast' _ _ h s sig))) h.
  Proof.
    intros h s sig D.
    case_eq(choose s);intros r Hr.
    case_eq(c_of_ReW _ _ r);simpl;intros.
    unfold LLim,lim_cardN.
    (*destruct D.*)
    revert H0.
    unfold StepFast'.
    rewrite Hr.
    rewrite H.
    intro.
    Opaque MAX.
    simpl.
    apply choose_1 in Hr.
    assert(~r \In h).
    intro.
    assert(r \In inter h s) by (apply inter_iff;split;auto).
    apply D in H2;inversion H2.
    rewrite add_cardinal_2;auto.
    rewrite  ReW_to_set_re_same_card.
    Transparent MAX.
    clear H0.
    generalize(in_powerset_PDs _ _ h);intro.
    apply subset_cardinal in H0.
    generalize(cardinal_less_than_pow2 h);intro.
    unfold MAX.
    rewrite Nnat.nat_of_Nsucc.
    rewrite Nnat.nat_of_Nmult.
    do 2 rewrite pow2_pow2N_equiv.
    abstract omega.
    unfold StepFast' in H0.
    rewrite Hr,H in H0.
    abstract discriminate.
    unfold StepFast' in Hr.
    rewrite r in Hr.
    abstract discriminate.
  Qed.
  
  Lemma DP_wf : forall (h s : set (ReW r1 r2)) (sig : set Z),
                  DP _ _ h s -> snd (StepFast' _ _ h s sig) = Process' _ _ ->
                  LLim _ _ (fst (fst (StepFast' _ _ h s sig))) h.
  Proof.
    intros.
    destruct H.
    apply LLim_disj_h_s. 
    exact H.
    exact H0.
  Qed.

End DecreasingMeasures.

Section Iterator.
  Variables r1 r2:re.
  
  Inductive LastCases : Type := 
    Ok : set (ReW r1 r2) -> LastCases | NotOk : ReW r1 r2 -> LastCases.

  (* begin show *)
  Function decide_re_ref'(h s:set (ReW r1 r2))
           (sig:set Z)(D:DP _ _ h s){wf (LLim r1 r2) h}: LastCases :=
    let f := StepFast' _ _ h s sig in 
    let next := snd f in
    let HistStack := (fst f) in
    match next  with
      | TermFalse' x => NotOk x
      | TermTrue' h  => Ok h(*(fst HistStack)*)
      | Process'  => decide_re_ref' (fst HistStack) (snd HistStack) 
                                    sig (DP_upd _ _ h s sig D)
    end.
  Proof.
    abstract(apply DP_wf).
    exact(guard r1 r2 100 (LLim_wf r1 r2)).
  Defined.
(* end show *)

End Iterator.

Section ResultContainsOriginal.
  Variables r1 r2: re.

  Lemma decide_re_ref'_1 : forall s h sig D,
                           forall x , decide_re_ref' _ _ h s sig D = x -> 
                                      forall r s', StepFast' _ _ h s sig = (({r;h},s'),Process' r1 r2) ->
                                                   forall D', decide_re_ref' _ _ {r;h} s' sig D' = x.
  Proof.
    intros.
    rewrite decide_re_ref'_equation in H.
    pattern (StepFast' _ _ h s sig) at 1 in H.
    rewrite H0 in H.
    (* Truque acelera a gravacao da prova. Caso use [simpl] a gravacao 
         da funcao nao sei se termina. *)
    assert(match snd ({r; h}, s',Process' _ _) with
             | Process' =>
               decide_re_ref' _ _ (fst (fst (StepFast' _ _ h s sig)))
                              (snd (fst (StepFast' _ _ h s sig))) sig
                              (DP_upd _ _ h s sig D)
             | TermTrue' h => Ok _ _ h
             | TermFalse' x => NotOk _ _ x
           end = x -> (decide_re_ref' _ _ (fst (fst (StepFast' _ _ h s sig))) 
                                      (snd (fst (StepFast' _ _ h s sig))) sig
                                      (DP_upd _ _ h s sig D) = x)). 
    abstract (simpl;auto).
    generalize(H1 H).
    intro.
    clear H H1.
    revert H2.
    generalize(DP_upd _ _ h s sig D).
    generalize(D').
    rewrite H0.
    simpl.
    intros.
    assert(d=D'0).
    apply proof_irrelevance.
    rewrite <- H.
    assumption.
  Qed.

  Lemma in_first_ref : forall s h sig D x,
                         decide_re_ref' _ _ h s sig D = Ok r1 r2 x -> h[<=]x.
  Proof.
    intros.
    functional induction (decide_re_ref' r1 r2 h s sig D).
    discriminate.
    injection H;intro;subst;clear H.
    revert e.
    unfold StepFast'.
    case_eq(choose s);intros r Hr.
    case_eq(%e_rew r);intro.
    discriminate.
    discriminate.
    simpl in Hr.
    injection Hr;intros.
    subst.
    intuition.
    generalize(IHl H);intro;clear IHl.
    transitivity (fst (fst (StepFast' r1 r2 h s sig)));auto.
    revert e.
    unfold StepFast'.
    case_eq(choose s);intros r Hr.
    case_eq(%e_rew r);intro.
    simpl.
    intro.
    red;intros.
    apply add_2;auto.
    discriminate.
    discriminate.
  Qed.

  Lemma in_first_step_fast' : forall s h sig D x r,
                                decide_re_ref' r1 r2 h s sig D = Ok r1 r2 x -> choose s = Some r ->
                                {r;h}[<=]x.
  Proof.
    intros.
    assert(DP r1 r2 {r; h} (r %dF[ {r; h}, sig ] ++ (remove r s))).
    destruct D.
    constructor.
    split;intros.
    apply inter_iff in H1.
    destruct H1.
    apply union_1 in H2.
    destruct H2.
    apply ReW_pdrv_set_filtered_no_dup in H2.
    contradiction.
    apply remove_iff in H2.
    destruct H2.
    apply add_iff in H1.
    destruct H1.
    contradiction.
    assert(a \In inter h s).
    apply inter_iff;split;auto.
    (*destruct d.*)
    apply e in H4;inversion H4.
    inversion H1.
    case_eq(%e_rew r);intro.
    unfold c_of_ReW_set.
    rewrite fold_add;auto with typeclass_instances.
    rewrite H1.
    simpl.
    exact e0.
    repeat red.
    intros.
    destruct(%e_rew x0).
    simpl.
    reflexivity.
    simpl.
    rewrite andb_comm.
    simpl;reflexivity.
    intro.
    apply choose_1 in H0.
    assert(r \In inter h s).
    apply inter_iff;split;auto with typeclass_instances.
    apply e in H3.
    inversion H3.
    rewrite decide_re_ref'_equation in H.
    revert H.
    generalize(is_dpt r1 r2 h s e e0).
    unfold StepFast'.
    intro.
    generalize(DP_upd r1 r2 h s sig d).
    unfold StepFast'.
    rewrite H0,H1.
    discriminate.
    revert H.
    rewrite decide_re_ref'_equation.
    generalize(DP_upd r1 r2 h s sig D).
    unfold StepFast'.
    rewrite H0.
    case_eq(%e_rew r).
    intro.
    simpl.
    intros.
    apply in_first_ref in H2.
    assumption.
    simpl.
    discriminate.
  Qed.

  Lemma in_first_stepfast' : forall s h sig D x r,
                               decide_re_ref' r1 r2 h s sig D = Ok r1 r2 x -> choose s = Some r ->
                               {r;h}[<=]x.
  Proof.
    intros.
    assert(StepFast' r1 r2 h s sig = 
           (({r;h},r %dF[ {r;h}, sig ] ++ (remove r s)),Process' r1 r2)).
    unfold StepFast'.
    rewrite H0.
    case_eq(%e_rew r);intro.
    reflexivity.
    rewrite decide_re_ref'_equation in H.
    revert H.
    generalize(DP_upd r1 r2 h s sig D).
    unfold StepFast'.
    rewrite H0.
    rewrite H1.
    simpl.
    discriminate.
    assert(DP r1 r2 {r; h} (r %dF[ {r; h}, sig ] ++ (remove r s))).
    destruct D.
    (*destruct d.*)
    constructor.
    (*constructor.*)
    split;intros.
    apply inter_iff in H2.
    destruct H2.
    apply union_1 in H3.
    destruct H3.
    apply ReW_pdrv_set_filtered_no_dup in H3.
    contradiction.
    apply remove_iff in H3.
    destruct H3.
    apply add_iff in H2.
    destruct H2.
    contradiction.
    assert(a \In inter h s).
    apply inter_iff;split;auto.
    apply e in H5;inversion H5.
    inversion H2.
    case_eq(%e_rew r);intro.
    unfold c_of_ReW_set.
    rewrite fold_add;auto with typeclass_instances.
    rewrite H2.
    simpl.
    exact e0.
    repeat red.
    intros.
    destruct(%e_rew x0).
    simpl.
    reflexivity.
    simpl.
    rewrite andb_comm.
    simpl;reflexivity.
    intro.
    apply choose_1 in H0.
    assert(r \In inter h s).
    apply inter_iff;split;auto with typeclass_instances.
    apply e in H4.
    inversion H4.
    unfold StepFast' in H1.
    rewrite H0,H2 in H1.
    discriminate.
    generalize(decide_re_ref'_1 _ _ _ _ _ H r _ H1 H2).
    intro.
    generalize(in_first_step_fast' _ _ _ _ _ r H H0);auto.
  Qed.

  Lemma decide_re_ref'_contains_orig_aux : forall sig D x r,
                                             decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set sig D = Ok r1 r2 x -> 
                                             choose {ReW_1st r1 r2}%set = Some r ->
                                             ReW_1st r1 r2 \In x.
  Proof.
    intros.
    assert(forall r, choose {ReW_1st r1 r2}%set = Some r -> 
                     r === ReW_1st r1 r2).
    intros.
    apply choose_1 in H1.
    apply singleton_1 in H1;auto.
    generalize(H1 _ H0).
    intro.
    generalize(in_first_step_fast' _ _ _ _ x r H H0).
    intro.
    apply H3.
    apply add_1.
    assumption.
  Qed.

  Lemma decide_re_ref'_contains_orig_hip : forall sig D x,
                                             decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set sig D = Ok r1 r2 x -> 
                                             exists r, choose {ReW_1st r1 r2}%set = Some r.
  Proof.
    intros.
    rewrite decide_re_ref'_equation in H.
    unfold StepFast' at 1 in H.
    case_eq(choose {ReW_1st r1 r2});intros.
    rewrite H0 in H.
    case_eq(%e_rew r);intro.
    rewrite H1 in H.
    simpl in H.
    exists r;auto.
    rewrite H1 in H.
    simpl in H.
    discriminate.
    rewrite H0 in H.
    simpl in H.
    apply choose_2 in H0.
    elim (H0 (ReW_1st r1 r2)).
    apply singleton_2;auto.
  Qed.

  Lemma decide_re_ref'_contains_orig : forall sig D x,
                                         decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set sig D = Ok r1 r2 x -> 
                                         ReW_1st r1 r2 \In x.
  Proof.
    intros.
    destruct (decide_re_ref'_contains_orig_hip sig D x). 
    assumption.
    exact(decide_re_ref'_contains_orig_aux sig D x x0 H H0). 
  Qed.

End ResultContainsOriginal.

Require Import symbs.

Section IteratorInvariant.
  Variables r1 r2:re.

  Global Instance not_in_set_add_m : 
    forall r h, Proper (_eq ==> eq) (fun x : ReW r1 r2 => negb (x \in {r; h})).
  Proof.
    repeat red;intros.
    rewrite H.
    reflexivity.
  Qed.

  (** Invariant of [decide_re]. *)
  Definition invP'(h s:set (ReW r1 r2))(sig:set Z) :=
    forall x, x \In h ->
              forall a, a \In sig -> (ReW_pdrv r1 r2 x a) \In (h ++ s).
  
  (** Invariant enriched with correctness criteria of [c_of_ReW]. *)
  Definition invP_final'(h s:set (ReW r1 r2))(sig:set Z) :=
    (ReW_1st r1 r2) \In (h ++ s) /\
    (forall x, x \In (h++s) -> c_of_ReW r1 r2 x = true) /\ invP' h s sig.

  Lemma invP_inv' : forall h s (sig:set Z), 
                      invP' h s sig -> 
                      invP' (fst (fst (StepFast' r1 r2 h s sig))) 
                            (snd (fst (StepFast' r1 r2 h s sig))) sig. 
  Proof.
    intros *.
    case_eq(choose s);intros.
    unfold invP' in H0.
    unfold StepFast'.
    rewrite H.
    case_eq(%e_rew r);intros.
    simpl.
    unfold invP';intros.
    destruct(@In_dec (ReW r1 r2) _ _ _ (ReW_pdrv _ _ x a) h).
    apply union_2.
    apply add_2;auto.
    apply add_iff in H2;destruct H2.
    destruct(eq_dec (x %d[a]) x).
    rewrite H4.
    apply union_2;apply add_1;auto.
    apply union_3.
    apply union_2.
    apply filter_iff;auto with typeclass_instances.
    split.
    rewrite <- H2.
    apply ReW_in_pdrv_set.
    assumption.
    apply Bool.eq_true_not_negb.
    intro.
    apply mem_iff in H5.
    apply add_iff in H5.
    destruct H5.
    rewrite H2 in H5.
    symmetry in H5.
    contradiction.
    contradiction.
    generalize(H0 _ H2 _ H3).
    intro.
    apply union_1 in H4.
    destruct H4.
    contradiction.
    destruct(eq_dec (x %d[a]) r).
    rewrite H5.
    apply union_2.
    apply add_1;reflexivity.
    apply union_3.
    apply union_3.
    apply remove_iff.
    split.
    assumption.
    intro.
    symmetry in H6;contradiction.
    simpl.
    assumption.
    unfold StepFast'.
    rewrite H.
    simpl.
    assumption.
  Qed.

  Lemma invP_decide_re_correct' :
    forall h s sig D x,
      invP' h s sig -> decide_re_ref' r1 r2 h s sig D = Ok r1 r2 x -> 
      invP' x {}%set sig.
  Proof.
    intros.
    functional induction (decide_re_ref' r1 r2 h s sig D).
    discriminate.
    case_eq(choose s);intros.
    unfold StepFast' in e.
    rewrite H1 in e.
    case_eq(%e_rew r);intros.
    rewrite H2 in e.
    discriminate.
    rewrite H2 in e.
    discriminate.
    unfold StepFast' in e.
    rewrite H1 in e.
    simpl in e.
    injection e;injection H0;intros;subst.
    clear H0 e.
    unfold invP' in H.
    unfold invP'.
    intros.
    generalize(H x0 H0 _ H2).
    intro.
    apply choose_2 in H1.
    apply empty_is_empty_1 in H1.
    rewrite H1 in H3.
    assumption.
    apply IHl.
    apply invP_inv'.
    assumption.
    assumption.
  Qed.

  Definition mkDP_ini : DP r1 r2 ({}%set) ({ReW_1st r1 r2}%set).
  Proof.
    constructor.
    split;intros;try abstract(inversion H).
    vm_compute.
    reflexivity.
  Defined.
  
  Lemma invP'_decide_re_initial_correct : forall x, 
                                            decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set 
                                                           (ss r1 ++ ss r2) (mkDP_ini) = Ok r1 r2 x ->  
                                            invP' x {}%set (ss r1 ++ ss r2).
  Proof.
    intros.
    eapply (invP_decide_re_correct' {} {ReW_1st r1 r2}  (ss r1 ++ ss r2) mkDP_ini).
    unfold invP'.
    intros.
    abstract(inversion H0).
    apply H.
  Qed.
  
End IteratorInvariant.

Section CorrectnessArgument.
  Variables r1 r2 : re.

  (* ESTE TEM QUE SAIR DAQUI E IR PARA O dsr_dsl.v *)
  Lemma c_of_re_set_singleton : 
    forall s, εs({s}%set) = ε(s).
  Proof.
    intros.
    case_eq(c_of_re_set {s});intro.
    apply c_of_re_set_true in H.
    do 2 destruct H.
    apply singleton_1 in H.
    rewrite H.
    rewrite H0;auto.
    generalize(c_of_re_set_false _ H).
    intro.
    assert(s \In {s}%set).
    apply singleton_2;auto.
    apply H0 in H1.
    rewrite H1;auto.
  Qed.

  Lemma leibniz_word : forall w1 w2:word,
                         w1 === w2 -> w1 = w2.
  Proof.
    induction 1.
    reflexivity.
    normalize_notations.
    inv H.
  Qed.

  Lemma invP_final_eq_lang' : 
    forall x,
      decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set (ss r1 ++ ss r2) (mkDP_ini r1 r2) 
      = Ok r1 r2 x ->   
      invP_final' r1 r2 x {}%set (ss r1 ++ ss r2) -> r1 ∼ r2.
  Proof.
    intros.
    unfold invP_final' in H0.
    destruct H0 as [H1 [H2 H3]].
    unfold invP' in H3.
    assert(ReW_1st r1 r2 \In x).
    apply union_1 in H1;destruct H1.
    assumption.
    abstract(inversion H0).
    clear H1.
    assert(forall x0 : ReW r1 r2, x0 \In x -> c_of_ReW _ _ x0 = true).
    intros.
    apply H2.
    apply union_2;auto.
    clear H2.
    assert(forall x0 : ReW r1 r2,
             x0 \In x -> forall a : Z, a \In (ss r1 ++ ss r2) -> x0 %d[ a ] \In x).
    intros.
    generalize(H3 _ H2 _ H4);intro.
    apply union_iff in H5;destruct H5.
    assumption.
    abstract(inversion H5).
    clear H3.
    assert(forall w, (@>w) ∈ langSsy (ss r1 ++ ss r2) -> ReW_wpdrv r1 r2 (@>w) \In x).
    induction w0.
    simpl.
    assert(ReW_wpdrv r1 r2 [] === ReW_1st r1 r2) by 
        (vm_compute;split;intros;auto).
    intro.
    rewrite H3.
    assumption.
    simpl.
    rewrite ReW_wpdrv_step.
    intro.
    eapply H2.
    apply IHw0.
    apply word_concat_sy_in_langSsy in H3.
    destruct H3;auto.
    apply word_concat_sy_in_langSsy in H3;
      destruct H3;auto.
    inversion_clear H4.
    assumption.

    assert(forall w, w ∈ langSsy (ss r1 ++ ss r2) ->
                     ReW_wpdrv r1 r2 w \In x).
    intro.
    generalize(ListFromIlist w0).
    intro.
    assert(ReW_wpdrv r1 r2 w0 === ReW_wpdrv r1 r2 (@>(<@w0))).
    red.
    unfold _eq.
    simpl.
    red in H4.
    unfold _eq in H4;simpl in H4.
    unfold ReW_eq.
    simpl.
    normalize_notations.
    apply leibniz_word in H4.
    rewrite H4.
    reflexivity.
    intros.
    rewrite H5.
    apply H3.
    apply leibniz_word in H4.
    rewrite H4.
    assumption.
    
    assert(forall w, w ∈ langSsy (ss r1 ++ ss r2) -> c_of_ReW _ _ (ReW_wpdrv r1 r2 w) = true).
    intros.
    apply H1.
    apply H4.
    assumption.
    assert(forall w,  w ∈ langSsy (ss r1 ++ ss r2) -> c_of_re_set (wpdrv r1 w) = c_of_re_set (wpdrv r2 w)).
    intros.
    specialize H5 with w0.
    unfold c_of_ReW in H5;simpl in H5.
    unfold wpdrvp in H5;simpl in H5.
    unfold c_of_rep in H5;simpl in H5.
    do 2 rewrite wpdrv_set_singleton in H5.
    apply Bool.eqb_prop in H5.
    assumption.
    assumption.
    clear H3 H H0 H1 H2 H4 H5.
    apply word_of_langSsy_decide_equiv.
    apply H6.
  Qed.

  Definition equiv_re_ref_aux'(h s:set (ReW r1 r2))
             (sig:set Z)(D:DP r1 r2 h s) :=
    let H := decide_re_ref' r1 r2 h s sig D in
    match H with
      | Ok _ => true
      | _ => false
    end.
  
  Definition equiv_re_ref' (sig:set Z) :=
    equiv_re_ref_aux' {}%set {ReW_1st r1 r2}%set sig (mkDP_ini r1 r2).

  Definition equivP := equiv_re_ref' (ss r1 ++ ss r2).

  Lemma decide_ref_subset_decide_re_all_c : forall h s sig D x,
                                              decide_re_ref' r1 r2 h s sig D = Ok r1 r2 x -> c_of_ReW_set r1 r2 x = true.
  Proof.
    intros.
    functional induction (decide_re_ref' r1 r2 h s sig D).
    abstract discriminate.
    injection H;intros.
    rewrite H0 in e.
    (*clear H H0 h0.*)
    revert e.
    unfold StepFast'.
    case_eq(choose s).
    intros r Hr.
    case_eq(%e_rew r);simpl;intros.
    abstract discriminate.
    abstract discriminate.
    simpl;intros.
    injection e;intros.
    destruct D.
    rewrite H2 in H4. (*;clear H H0.*)
    exact H4.
    exact(IHl H).
  Qed.

  Lemma correct_aux_1 : forall s,
                          decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set (ss r1 ++ ss r2) 
                                         (mkDP_ini r1 r2) 
                          = Ok r1 r2 s -> equiv_re_ref' (ss r1 ++ ss r2) = true.
  Proof.
    intros.
    unfold equiv_re_ref'.
    unfold equiv_re_ref_aux'.
    rewrite H.
    reflexivity.
  Qed.

  Lemma correct_aux_2 : forall s,
                          decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set (ss r1 ++ ss r2)
                                         (mkDP_ini r1 r2) 
                          = NotOk r1 r2 s -> equiv_re_ref' (ss r1 ++ ss r2) = false.
  Proof.
    intros.
    unfold equiv_re_ref'.
    unfold equiv_re_ref_aux'.
    rewrite H.
    reflexivity.
  Qed.
  
  Lemma decide_ref_subset_decide_re_not_ok : forall h s sig D x,
                                               decide_re_ref' r1 r2 h s sig D = NotOk r1 r2 x -> %e_rew x = false.
  Proof.
    intros.
    functional induction (decide_re_ref' r1 r2 h s sig D).
    injection H;clear H;intros.
    subst.
    revert e.
    unfold StepFast'.
    case_eq(choose s).
    intros r Hr.
    case_eq(%e_rew r);intro.
    discriminate.
    intros.
    injection e;intros;subst.
    assumption.
    discriminate.
    discriminate.
    apply IHl in H.
    assumption.
  Qed.

End CorrectnessArgument.

Section EquivPCorrectness.
  Variables r1 r2 : re.

  Lemma equiv_re_true : equiv_re_ref' r1 r2 (ss r1 ++ ss r2) = true -> r1 ∼ r2.
  Proof.
    intro.
    case_eq(decide_re_ref' r1 r2 {} {ReW_1st r1 r2} (ss r1 ++ ss r2) (mkDP_ini r1 r2)).
    intros s H1.

    apply invP_final_eq_lang' with (x:=s).
    exact H1.
    split.
    abstract(apply union_2;
             exact(decide_re_ref'_contains_orig r1 r2 (ss r1 ++ ss r2) (mkDP_ini r1 r2) s H1)).
    split;intros.
    abstract(apply decide_ref_subset_decide_re_all_c in H1;
             apply union_1 in H0;destruct H0;[
               exact(wit_all_in_c_of_ReW_set r1 r2 s H1 x H0)|
               inversion H0]).
    abstract(apply invP'_decide_re_initial_correct in H1;
             exact H1).
    
    intros.
    apply correct_aux_2 in H0.
    rewrite H0 in H.
    abstract(discriminate).
  Qed.

  Lemma equiv_re_false : equiv_re_ref' r1 r2 (ss r1 ++ ss r2) = false -> r1 !∼ r2.
  Proof.
    intros.
    case_eq(decide_re_ref' r1 r2 {} {ReW_1st r1 r2} (ss r1 ++ ss r2) (mkDP_ini r1 r2));
      intros.
    apply correct_aux_1 in H0.
    abstract(rewrite H0 in H;discriminate).
    apply decide_ref_subset_decide_re_not_ok in H0.
    apply  c_of_ReW_diff_wpdrvs_Srels in H0.
    exact H0.
  Qed.

End EquivPCorrectness.

Section EquivPCompleteness.
  Variables r1 r2:re.

  Theorem equiv_re_complete_true : r1 ∼ r2 -> 
                                   equiv_re_ref' r1 r2 (ss r1 ++ ss r2) = true.
  Proof.
    intros.
    case_eq(equiv_re_ref' r1 r2 (ss r1 ++ ss r2));intros.
    reflexivity.
    apply equiv_re_false in H0.
    contradiction.
  Qed.
  
  Lemma equiv_re_complete_false : r1 !∼ r2 -> 
                                  equiv_re_ref' r1 r2 (ss r1 ++ ss r2) = false.
  Proof.
    intros.
    case_eq(equiv_re_ref' r1 r2 (ss r1 ++ ss r2));intros.
    apply equiv_re_true in H0.
    contradiction.
    reflexivity.
  Qed.
  
End EquivPCompleteness.

(** * The automatic proof tactic [dec_equivP] *)
Ltac re_inequiv :=
  apply equiv_re_false;vm_compute;
  first [ reflexivity | fail 2 "Regular expressions not inequivalent" ].

Ltac re_equiv :=
  apply equiv_re_true;vm_compute;
  first [ reflexivity | fail 2 "Regular expressions are not equivalent" ].

Ltac dec_re :=
  match goal with
    | |- re2rel (?R1) ∼ re2rel (?R2) => re_equiv
    | |- re2rel (?R1) !∼ re2rel (?R2) => re_inequiv
    | |- re2rel (?R1) ≤ re2rel (?R2) => 
      unfold lleq;change (R1 ∪ R2) with (re2rel (R1 + R2));
      re_equiv
    | |- _  => fail 2 "Not a regular expression (in-)equivalence equation."
  end.

