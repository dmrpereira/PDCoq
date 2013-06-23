Require Export kat_alph atoms gl kat kat_pdrvs wf_extra symbs.

Module KATDec(X:KAT_Alph).

  Import X.
  Module Export M := KATPdrvs(X).
  Module Export Sy := Symbs(X).

  Open Scope set_scope.
  
  (** Datatype of word-derivative of kat terms. *)
  
  Section DataTypes.
    Variables r1 r2:kat.

    (** First we define the notion of word partial derivative of pair of
       sets of regular expressions. *)

    Definition pdrvp(x:set kat*set kat)(a:atom)(s:Z) :=
      (pdrv_set (fst x) a s,pdrv_set (snd x) a s).
    
    Definition wpdrvp(x:set kat * set kat)(a:list AtSy) :=
      (wpdrv_set (fst x) a,wpdrv_set (snd x) a).

    (** The type [ReW] is defined as a record with an inner coercion of [ReW] terms
       to pairs of sets, in order to allow an easier and less-verbose notion of
       equality and order, which corresponds to the already existing order of
       pairs of sets of regular expressions. *)

    Record ReW := 
      {
        dp :> set kat * set kat ;
        w  : list AtSy ;
        cw : dp === wpdrvp ({r1}%set,{r2}%set) w
      }.

    Global Transparent cw.

    Program Definition ReW_1st : ReW .
    Proof.
      refine(Build_ReW ({r1}%set,{r2}%set) nil _).
      abstract(
      unfold wpdrvp;simpl;
      constructor;unfold wpdrv_set;simpl;
        normalize_notations;auto).
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
      _eq (A:=set kat * set kat) x y.

    Definition ReW_lt(x y:ReW) :=
      _lt (A:=set kat * set kat) x y.

    Global Program Instance ReW_ord : OrderedType ReW := {
      _eq := ReW_eq ;
      _lt := ReW_lt ;
      _cmp := _cmp (A:=set kat * set kat)
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

  (** Derivation of [ReW] terms.  *)

  Generalizable All Variables.

  Section ReW_Derivation.
    Variables r1 r2:kat.

    (** Extension of partial derivatives wrt. a symbol of type [A] *)

    Definition ReW_pdrv (x:ReW r1 r2)(a:atom)(s:Z) : ReW r1 r2.
    Proof.
      refine(match x with
               | Build_ReW K w P => 
                 Build_ReW r1 r2 (pdrvp K a s) (w++((a,s)::nil))%list _
             end).
      abstract(unfold pdrvp;inversion_clear P;simpl in *;
      constructor;normalize_notations;simpl;
        [rewrite H|rewrite H0];
        rewrite wpdrv_set_app;
      unfold wpdrv_set;simpl;reflexivity;unfold wpdrv_set;
      simpl;reflexivity).
    Defined.

    (** Build a particular derivative of [r1] and [r2], directly 
        from a given word. *)

    Definition ReW_wpdrv (w:list AtSy) : ReW r1 r2.
    Proof.
      refine(Build_ReW r1 r2 (wpdrvp (singleton r1, singleton r2) w) w _).
      abstract(reflexivity).
    Defined.

    Global Instance ReW_pdrv_m : Proper(_eq ==> _eq ==> _eq ==> _eq) ReW_pdrv.
    Proof.
      repeat red;intros.
      destruct x.
      destruct y.
      inversion H.
      normalize_notations.
      simpl.
      simpl in H4;destruct dp0.
      simpl in H5;destruct dp1.
      injection H4;injection H5;intros;subst.
      inv H0.
      unfold pdrvp.
      simpl.
      constructor.
      rewrite H2.
      rewrite H1.
      reflexivity.
      rewrite H3.
      rewrite H1.
      reflexivity.
    Qed.

    (** Generalization to sets *)
    Definition ReW_wpdrv_ReW (w:list AtSy)(s:ReW r1 r2) : ReW r1 r2.
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

    Instance ReW_wpdrv_ReW_m_same_w : forall w,
      Proper (_eq ==> _eq) (fun x => ReW_wpdrv_ReW w x).
    Proof.
      repeat red.
      intros.
      destruct x.
      destruct y.
      inversion H.
      simpl in * |-.
      destruct dp0;destruct dp1.
      injection H2;injection H3;intros;subst.
      normalize_notations.
      simpl.
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
      simpl in H3,H4;destruct dp0;destruct dp1;
      injection H3;injection H4;intros;subst.
      simpl.
      constructor;simpl;
        [rewrite H1 | rewrite H2];rewrite H;reflexivity.
    Qed.

    Lemma ReW_wpdrv_step : 
      forall w a,
        ReW_wpdrv ((@>w)++(a::nil))%list ===
                  ReW_pdrv (ReW_wpdrv (@>w)) (fst a) (snd a).
    Proof.
      induction w0.
      intro.
      change(@>(inil)) with (@nil AtSy).
      change ((@nil AtSy)++(a::nil))%list with (a::nil).
      assert((ReW_wpdrv nil) === ReW_1st r1 r2).
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

    Definition ReW_pdrv_set(s:ReW r1 r2)(Sig:set AtSy) : set (ReW r1 r2) :=
      fold (fun x:AtSy => add (ReW_pdrv s (fst x) (snd x))) Sig {}%set.

    Definition ReW_wpdrv_set(s:set (ReW r1 r2))(w:list AtSy) : set (ReW r1 r2) :=
      fold (fun x => add (ReW_wpdrv_ReW w x)) s {}%set.

    Instance add_ReW_pdrv : Proper (_eq ==> _eq ==> _eq) 
      (fun x1 : AtSy => add (ReW_pdrv x0 (fst x1) (snd x1))).
    Proof.
      repeat red;intros.
      split;intros.
      apply add_iff in H1;destruct H1.
      rewrite <- H1.
      apply add_1.
      destruct H;simpl in *.
      normalize_notations.
      rewrite H.
      rewrite H2.
      reflexivity.
      rewrite H0 in H1.
      apply add_2;auto.
      apply add_iff in H1;destruct H1.
      rewrite <- H1.
      apply add_1.
      destruct H;simpl in *.
      apply ReW_pdrv_m;auto.
      apply add_2.
      apply H0;auto.
    Qed.

    Instance add_ReW_wpdr : Proper (_eq ==> _eq ==> _eq)
      (fun x : list AtSy => add (ReW_wpdrv_ReW x x0)).
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
      transpose _eq (fun x1 : AtSy => add (ReW_pdrv x0 (fst x1) (snd x1))).
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
      apply add_iff in H;destruct H;intuition.
    Qed.

    Lemma ReW_pdrv_set_elem_in : forall sig s a,
      a \In sig -> ReW_pdrv s (fst a) (snd a) \In ReW_pdrv_set s sig.
    Proof.
      induction sig using set_induction.
      intros s a H1.
      apply H in H1.
      elim H1.
      intros.
      apply H0 in H1.
      destruct H1.
      unfold ReW_pdrv_set.
      rewrite (@fold_2 AtSy _ _ _ sig1 sig2 x (set (ReW r1 r2)) _eq OT_Equivalence 
        (empty (A:=ReW r1 r2)) (fun x0 : AtSy => add (ReW_pdrv s (fst x0) (snd x0)))
        _ (add_ReW_pdrv_transp s) H H0).
      apply add_1.
      destruct H1;simpl in *.
      rewrite H2.
      rewrite H1.
      reflexivity.
      eapply IHsig1  in H1.
      unfold ReW_pdrv_set.
      rewrite (@fold_2 AtSy _ _ _ sig1 sig2 x (set (ReW r1 r2)) _eq OT_Equivalence
        (empty (A:=ReW r1 r2)) (fun x0 : AtSy => add (ReW_pdrv s (fst x0) (snd x0)))
        _ (add_ReW_pdrv_transp s) H H0).
      apply add_2.
      apply H1.
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
      generalize (@fold_2 AtSy _ _ _ x0_1 x0_2 x (set (ReW r1 r2)) _eq
                   OT_Equivalence {}%set
                   (fun x0 : AtSy => add (ReW_pdrv y (fst x0) (snd x0))) 
                   add_ReW_pdrv (add_ReW_pdrv_transp y) H H0).
      intro.
      split;intros.
      apply H2 in H3.
      cut(SetProperties.Add x x0_1 y0).
      intro.
      generalize (@fold_2 AtSy _ _ _ x0_1 y0 x (set (ReW r1 r2)) _eq 
                  OT_Equivalence {}%set
                  (fun x1 : AtSy => add (ReW_pdrv y (fst x1) (snd x1)))
                  add_ReW_pdrv (add_ReW_pdrv_transp y) H H4).
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
      generalize (@fold_2 AtSy _ _ _ x0_1 y0 x (set (ReW r1 r2)) _eq 
                  OT_Equivalence {}%set
                  (fun x1 : AtSy => add (ReW_pdrv y (fst x1) (snd x1)))
                  add_ReW_pdrv (add_ReW_pdrv_transp y) H H4).
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
      generalize (@fold_2 AtSy _ _ _ y0_1 y0_2 x0 (set (ReW r1 r2)) _eq 
                   OT_Equivalence {}%set
                   (fun x1 : AtSy => add (ReW_pdrv x (fst x1) (snd x1)))
                   add_ReW_pdrv (add_ReW_pdrv_transp x) H0 H1).
      intro.
      generalize (@fold_2 AtSy _ _ _ y0_1 y0_2 x0 (set (ReW r1 r2)) _eq 
                   OT_Equivalence {}%set
                   (fun x1 : AtSy => add (ReW_pdrv y (fst x1) (snd x1))) 
                   add_ReW_pdrv (add_ReW_pdrv_transp y) H0 H1).
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
      generalize (@fold_2 AtSy _ _ _ x0_1 x0_2 x0 (set (ReW r1 r2)) _eq
                   OT_Equivalence {}%set
                   (fun x0 : AtSy => add (ReW_pdrv x (fst x0) (snd x0)))
                   add_ReW_pdrv (add_ReW_pdrv_transp x) H0 H1);
      intros.
      cut(SetProperties.Add x0 x0_1 y0).
      intro.
      generalize (@fold_2 AtSy _ _ _ x0_1 y0 x0 (set (ReW r1 r2)) _eq 
                   OT_Equivalence {}%set
                   (fun x1 : AtSy => add (ReW_pdrv y (fst x1) (snd x1))) 
                   add_ReW_pdrv (add_ReW_pdrv_transp y) H0 H5);
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
      generalize (@fold_2 AtSy _ _ _ x0_1 x0_2 x0 (set (ReW r1 r2)) _eq
                   OT_Equivalence {}%set
                   (fun x0 : AtSy => add (ReW_pdrv x (fst x0) (snd x0)))
                   add_ReW_pdrv (add_ReW_pdrv_transp x) H0 H1);
      intros.
      cut(SetProperties.Add x0 x0_1 y0).
      intro.
      generalize (@fold_2 AtSy _ _ _ x0_1 y0 x0 (set (ReW r1 r2)) _eq 
                   OT_Equivalence {}%set
                   (fun x1 : AtSy => add (ReW_pdrv y (fst x1) (snd x1))) 
                   add_ReW_pdrv (add_ReW_pdrv_transp y) H0 H5);
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

  (** Filtering the new pairs of derivatives. *)

  Section ReW_Derivation_filtered.
    Variables r1 r2:kat.

    Definition ReW_pdrv_set_filtered(x:ReW r1 r2)(h:set (ReW r1 r2))
      (sig:set AtSy) : set (ReW r1 r2) :=
        filter (fun x => negb (mem x h)) (x %dS[sig]).

    Instance ReW_negb_m : 
      Proper (_eq ==> eq) (fun x2 : ReW r1 r2 => negb (x2 \in y0)).
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

    Global Instance ReW_pdrv_add_m : forall r:ReW r1 r2, 
      Proper (_eq ==> _eq ==> _eq) 
             (fun x0 : AtSy => add (ReW_pdrv _ _ r (fst x0) (snd x0))).
    Proof.
      repeat red.
      split;intros;
      apply add_iff in H1;
      destruct H1.
      destruct x.
      destruct y.
      destruct H.
      inv H;subst.
      inv H2;subst.
      apply add_1.
      apply H1.
      rewrite H0 in H1.
      apply add_2;auto.
      destruct H.
      inv H;inv H2;subst.
      apply add_1.
      assumption.
      rewrite <- H0 in H1.
      apply add_2;auto.
    Qed.
    
    Fact ReW_pdrv_add_transpose : forall r:ReW r1 r2, 
      transpose Equal (fun x0 : AtSy => add (ReW_pdrv r1 r2 r (fst x0) (snd x0))).
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

    Lemma ReW_in_pdrv_set : forall sig (r:ReW r1 r2) a, a \In sig ->
      (ReW_pdrv _ _ r (fst a) (snd a)) \In (ReW_pdrv_set _ _ r sig).
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
      destruct a.
      destruct x.
      destruct H1.
      inv H1;inv H2;subst.
      reflexivity.
      rewrite fold_add;auto with typeclass_instances.
      apply add_2.
      apply IHsig1;assumption.
    Qed.

    Lemma ReW_pdrv_set_filtered_ex : forall x h sig y,
      y \In ReW_pdrv_set_filtered x h sig -> 
      exists a, a \In sig /\ y === ReW_pdrv r1 r2 x (fst a) (snd a).
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
      generalize (@fold_2 AtSy _ _ _ sig1 sig2 x0 (set (ReW r1 r2)) _eq OT_Equivalence 
        {}%set
          (fun x1 : AtSy => add (ReW_pdrv r1 r2 x (fst x1) (snd x1))) (ReW_pdrv_add_m x) 
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
    Variables r1 r2:kat.

    Definition ewp_of_rep(x:set kat  * set kat)(a:atom) :=
      Bool.eqb (ewp_set (fst x) a) (ewp_set (snd x) a).

    Definition ewp_of_rep_at(x:set kat  * set kat)(a:set atom) :=
      fold (fun p => andb (ewp_of_rep x p)) a true.

    Instance ewp_of_rep_m : Proper(_eq ==> _eq ==> _eq) ewp_of_rep.
    Proof.
      repeat red.
      intros.
      destruct H.
      pose proof ewp_set_m a c H x0 y0 H0.
      unfold ewp_of_rep.
      simpl.
      rewrite H2.
      pose proof ewp_set_m b d H1 x0 y0 H0.
      rewrite H3.
      reflexivity.
    Qed.

    Instance andb_ewp_of_rep_m : 
      Proper (_eq ==> eq ==> eq) (fun p : atom => andb (ewp_of_rep y p)).
    Proof.
      repeat red.
      intros.
      unfold ewp_of_rep.
      rewrite H.
      rewrite H0.
      reflexivity.
    Qed.

    Lemma andb_ewp_of_rep_transp : 
      forall y, 
        transpose eq (fun p : atom => andb (ewp_of_rep y p)).
    Proof.
      repeat red.
      intros.
      rewrite Bool.andb_assoc.
      rewrite (Bool.andb_comm (ewp_of_rep y x) (ewp_of_rep y y0)).
      rewrite Bool.andb_assoc;auto.
    Qed.

    Hint Resolve andb_ewp_of_rep_transp : typeclass_instances.

    Instance ewp_of_rep_at_m : Proper(_eq ==> _eq ==> _eq) ewp_of_rep_at.
    Proof.
      repeat red.
      intros.
      revert x0 y0 H0 x y H.
      induction x0 using set_induction;intros.
      apply empty_is_empty_1 in H.
      rewrite H in H0.
      assert(y0[=]{}).
      rewrite <- H0.
      reflexivity.
      apply empty_is_empty_2 in H.
      apply empty_is_empty_2 in H2.
      unfold ewp_of_rep_at.
      rewrite fold_1b;auto.
      rewrite fold_1b;auto.
      unfold ewp_of_rep_at.
      rewrite fold_2;eauto with typeclass_instances.
      fold(ewp_of_rep_at x0 x0_1).
      assert(SetProperties.Add x x0_1 y0).
      apply Add_Equal in H0.
      apply Add_Equal.
      rewrite <- H1.
      assumption.
      rewrite fold_2;eauto with typeclass_instances.
      fold(ewp_of_rep_at y x0_1).
      assert(_eq x x) by reflexivity.
      pose proof ewp_of_rep_m _ _ H2 x x H4.
      rewrite H5.
      destruct(ewp_of_rep y x).
      simpl.
      apply IHx0_1;auto.
      simpl.
      reflexivity.
    Qed.

    Definition ewp_of_ReW(x:ReW r1 r2)(a:set atom) :=
      ewp_of_rep_at x a.

    Global Instance ewp_of_ReW_m : Proper(_eq ==> _eq ==> _eq) ewp_of_ReW.
    Proof.
      repeat red;intros.
      unfold ewp_of_ReW.
      apply ewp_of_rep_at_m;
      assumption.
    Qed.

    Definition ewp_of_ReW_set (x:set (ReW r1 r2))(a:set atom) : bool :=
      fold (fun x => andb (ewp_of_ReW x a)) x true.

    Instance andb_ewp_of_ReW_m :
      Proper (_eq ==> _eq ==> _eq)  (fun (x : ReW r1 r2) => andb (ewp_of_ReW x a)).
    Proof.
      repeat red.
      intros.
      rewrite H0.
      rewrite H.
      reflexivity.
    Qed.
    
    Lemma andb_ewp_of_ReW_m_transpose :
      forall a, transpose _eq (fun (x : ReW r1 r2) => andb (ewp_of_ReW x a)).
    Proof.
      repeat red;intros.
      destruct(ewp_of_ReW x).
      simpl;auto.
      simpl.
      rewrite Bool.andb_false_r.
      reflexivity.
    Qed.

    Hint Resolve andb_ewp_of_ReW_m_transpose : typeclass_instances.

    Global Instance ewp_of_ReW_set_m : 
             Proper(_eq ==> _eq ==> _eq) ewp_of_ReW_set.
    Proof.
      repeat red.
      induction x using set_induction;intros.
      unfold ewp_of_ReW_set.
      rewrite fold_1b;auto.
      rewrite H0 in H.
      rewrite fold_1b;auto.
      assert(SetProperties.Add x3 x1 y).
      apply Add_Equal in H0.
      apply Add_Equal.
      rewrite <- H0;symmetry;auto.
      unfold ewp_of_ReW_set.
      rewrite fold_2;eauto with typeclass_instances.
      symmetry.
      rewrite fold_2;eauto with typeclass_instances.
      symmetry.
      rewrite H2.
      fold (ewp_of_ReW_set x1 x);fold (ewp_of_ReW_set x1 y0).
      erewrite (IHx1).
      3:apply H2.
      apply Add_Equal in H3.
      reflexivity.
      reflexivity.
    Qed.

    Instance atom_flip_m : Proper (_eq ==> flip eq ==> flip eq)
                                  (fun p : atom => andb (ewp_of_rep x0 p)).
    Proof.
      repeat red.
      intros.
      red in H0.
      subst.
      inv H.
    Qed.

    Lemma atom_transpose_flip :
      forall x0, transpose (flip eq) (fun p : atom => andb (ewp_of_rep x0 p)).
    Proof.
      intros.
      repeat red.
      intros.
      rewrite Bool.andb_assoc.
      rewrite (Bool.andb_comm (ewp_of_rep x0 y) (ewp_of_rep x0 x)).
      rewrite Bool.andb_assoc.
      reflexivity.
    Qed.

    Hint Resolve atom_transpose_flip : typeclass_instances.

    Instance wit_in_ewp_of_ReW_set_flip : 
     Proper (_eq ==> flip eq ==> flip eq)
            (fun x0 : ReW r1 r2 => andb (ewp_of_ReW x0 a)).
    Proof.
      repeat red.
      unfold flip.
      intros.
      subst.
      symmetry in H.
      assert(_eq a a) by reflexivity.
      pose proof ewp_of_ReW_m _ _ H a a  H0.
      rewrite H1.
      reflexivity.
    Qed.

    Lemma wit_in_ewp_of_ReW_set_flip_transp : 
      forall a, transpose (flip eq) (fun x0 : ReW r1 r2 => andb (ewp_of_ReW x0 a)).
    Proof.
      repeat red.
      intros.
      rewrite Bool.andb_assoc.
      rewrite (Bool.andb_comm (ewp_of_ReW y a) (ewp_of_ReW x a)).
      rewrite Bool.andb_assoc.
      reflexivity.
    Qed.

    Hint Resolve wit_in_ewp_of_ReW_set_flip_transp : typeclass_instances.

    Lemma wit_in_ewp_of_ReW_set : forall s a,
      ewp_of_ReW_set s a = false -> exists x, x \In s /\
        ewp_of_ReW x a = false.
    Proof.
      induction s using set_induction.
      intros.
      apply empty_is_empty_1 in H.
      rewrite H in H0.
      unfold ewp_of_ReW_set in H0.
      vm_compute in H0.
      discriminate.
      intros.
      unfold ewp_of_ReW_set in H1.
      rewrite fold_2 in H1;eauto with typeclass_instances.
      case_eq(ewp_of_ReW x a).
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

    Lemma wit_all_in_ewp_of_ReW_set : forall s a,
      ewp_of_ReW_set s a = true -> forall x, x \In s ->
        ewp_of_ReW x a = true.
    Proof.
      induction s using set_induction.
      intros.
      apply H in H1;elim H1.
      intros.
      unfold ewp_of_ReW_set in H1.
      rewrite fold_2 in H1;eauto with typeclass_instances.
      apply H0 in H2.
      destruct H2.
      rewrite <- H2.
      case_eq(ewp_of_ReW x a);intros;auto.
      rewrite H3 in H1;simpl in H1;discriminate.
      case_eq(ewp_of_ReW x a);intros;auto.
      rewrite H3 in H1;simpl in H1.
      generalize(IHs1 a H1 _ H2);auto.
      rewrite H3 in H1;discriminate.
    Qed.

    Lemma ewp_of_ReW_wpdrv : forall x b a,
      ewp_of_ReW x a = b -> 
        exists w, ewp_of_rep_at (wpdrvp ({r1}%set,{r2}%set) w) a = b.
    Proof.
      intros.
      destruct x.
      exists w0.
      unfold ewp_of_ReW in H.
      simpl in H.
      rewrite <- cw0.
      assumption.
    Qed.

    Lemma ewp_of_rep_diff_constant : forall x y a w,
      ewp_of_rep (wpdrvp (x,y) w) a = false ->
      ewp_set (wpdrv_set x w) a <> ewp_set (wpdrv_set y w) a.
    Proof.
      intros.
      unfold ewp_of_rep in H.
      intro.
      simpl in H.
      apply Bool.eqb_false_iff in H.
      contradiction.
    Qed.

    Lemma ewp_of_ReW_diff_wpdrvs_orig : forall a x,
      ewp_of_ReW x a = false -> exists w,exists b, b \In a /\
        ewp_set (wpdrv r1 w) b <> ewp_set (wpdrv r2 w) b.
    Proof.
      induction a using set_induction.
      intros.
      apply empty_is_empty_1 in H.
      rewrite H in H0.
      unfold ewp_of_ReW in H0.
      unfold ewp_of_rep_at in H0.
      rewrite fold_1b in H0;auto with typeclass_instances.
      discriminate.
      intros.
      unfold ewp_of_ReW in H1.
      unfold ewp_of_rep_at in H1.
      rewrite fold_2 in H1;eauto with typeclass_instances.
      fold(ewp_of_rep_at x0 a1) in H1.
      apply Bool.andb_false_iff in H1.
      destruct H1.
      destruct x0.
      simpl in H1.
      rewrite cw0 in H1.
      apply ewp_of_rep_diff_constant in H1.
      exists w0.
      exists x.
      split.
      apply H0;auto.
      intro.
      apply H1.
      do 2 rewrite wpdrv_set_singleton.
      assumption.
      fold(ewp_of_ReW x0 a1) in H1.
      apply IHa1 in H1.
      destruct H1.
      destruct H1.
      destruct H1.
      exists x1.
      exists x2.
      split.
      apply H0;auto.
      assumption.
    Qed.

    (** Lemma that proves the inequivalence of regular expressions *)

    Lemma ewp_of_ReW_diff_wpdrvs_Srels : forall x a,
      ewp_of_ReW x a = false -> ~(gl_eq (kat2gl r1) (kat2gl r2)).
    Proof.
      intros.
      apply ewp_of_ReW_diff_wpdrvs_orig in H.
      destruct H.
      destruct H.
      destruct H.
      case_eq(ewp_set (r1 %dW x0) x1);intros.
      case_eq(ewp_set (r2 %dW x0) x1);intros.
      rewrite H1,H2 in H0;elim H0;auto.
      apply gs_in_pdrv_true in H1.
      apply gs_not_in_pdrv_true in H2.
      intro.
      apply H2.
      apply H3.
      assumption.

      case_eq(ewp_set (r2 %dW x0) x1);intros.
      apply gs_in_pdrv_true in H2.
      apply gs_not_in_pdrv_true in H1.
      intro.
      apply H1.
      apply H3;auto.
      rewrite H1,H2 in H0.
      elim H0;auto.
    Qed.

  End ReW_Emptyness.

  (* Notation "%e_p x"  := (ewp_of_rep x)(at level 30). *)
  (* Notation "%e_rew c " := (ewp_of_ReW _ _ c)(at level 30). *)

  Section DerivativesGenerator.
    Variables r1 r2:kat.

    Definition _cmpRP := _cmp (A:=set kat).

    (* Inductive DisjPP (h s:set (ReW r1 r2)) : Prop := *)
    (* | disjPP : inter h s === {}%set -> DisjPP h s. *)

                                  
    Inductive DP (h s:set (ReW r1 r2))(aps:set atom) : Prop :=
    | is_dpt : inter h s === {} -> 
      ewp_of_ReW_set _ _ h aps = true -> DP h s aps.
    
    Inductive StepFastCase' : Type :=
    |Process' : StepFastCase' 
    |TermTrue' : set (ReW r1 r2) -> StepFastCase' 
    |TermFalse' : ReW r1 r2 -> StepFastCase'.
    
    Generate OrderedType StepFastCase'.

    Definition set_sig_atom_set(a:atom)(s:set Z) :=
      fold (fun x => add (a,x)) s {}.
    Definition set_sig_atom_set_SyAt(a:set atom)(s:set Z) :=
      fold (fun x => union (set_sig_atom_set x s)) a {}.
    
    (** Must change the input here! Instead of [sat] and [sig], this function should
        receive as input the pairs [(atom,sy)] already combined to be more efficient. *)

    Definition StepFast'' (h s:set (ReW r1 r2))(ats:set atom)(sig:set Z) : 
      (set (ReW r1 r2) * set (ReW r1 r2)) * StepFastCase' :=
      match choose s with
        | None => ((h,s),TermTrue' h)
        | Some x => 
            if ewp_of_ReW _ _ x ats then
              let h' := add x h in 
                let s' := remove x s in 
                  let syats := set_sig_atom_set_SyAt ats sig in
                  let ns :=  ReW_pdrv_set_filtered _ _ x h' syats in 
                    ((h',union ns s'),Process')
            else
              ((h,s),TermFalse' x)
      end.

    Definition StepFast' (h s:set (ReW r1 r2))(ats:set atom)(atsig:set (atom*Z)) : 
      (set (ReW r1 r2) * set (ReW r1 r2)) * StepFastCase' :=
      match choose s with
        | None => ((h,s),TermTrue' h)
        | Some x => 
            if ewp_of_ReW _ _ x ats then
              let h' := add x h in 
                let s' := remove x s in 
                  let ns :=  ReW_pdrv_set_filtered _ _ x h' atsig in 
                    ((h',union ns s'),Process')
            else
              ((h,s),TermFalse' x)
      end.

  End DerivativesGenerator.

  Section Cardinality_Properties.
    Variables r1 r2 : kat.

    Lemma ReW_in_PD_fst : forall x (s:set (ReW r1 r2)), 
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

    Definition ReW_to_set_re (s:set (ReW r1 r2)) : set (set kat * set kat) :=
      fold (fun x => add (@dp r1 r2 x)) s  {}%set.

    Instance add_dp_m : Proper (_eq ==> _eq ==> _eq) 
      (fun x : ReW r1 r2 => add (@dp r1 r2 x)).
    Proof.
      repeat red;intros.
      unfold _eq in H.
      simpl in H.
      unfold ReW_eq in H.
      unfold _eq in H.
      simpl in H.
      split;intros.
      abstract(apply add_iff in H1;destruct H1;
               [apply add_1;rewrite <- H;assumption|
                apply add_2;apply H0;auto]).
      apply add_iff in H1;destruct H1.
      apply add_1. rewrite H. assumption.
      apply add_2;apply H0;auto.
    Qed.

    Lemma add_pd_transpose :
      transpose _eq (fun x : ReW r1 r2 => add (@dp r1 r2 x)).
    Proof.
      repeat red;intros.
      split;intros;
      apply add_iff in H;
      destruct H;
        try (rewrite <- H).
      apply add_2;apply add_1;auto.
      apply add_iff in H;destruct H.
      rewrite <- H;apply add_1;auto.
      do 2 apply add_2;auto.
      apply add_2;apply add_1;auto.
      apply add_iff in H;destruct H.
      rewrite <- H;apply add_1;auto.
      do 2 apply add_2;auto.
    Qed.

    Hint Resolve add_pd_transpose : typeclass_instances.
    
    Lemma in_powerset_PDs : forall (s:set (ReW r1 r2)),
      (ReW_to_set_re s)[<=]cart_prod (powerset(PD(r1))) (powerset(PD(r2))).
    Proof.
      induction s using set_induction;intros.
      red;intros.
      unfold ReW_to_set_re in H0.
      rewrite fold_1b in H0;auto with typeclass_instances.
      inversion H0.
      red;intros.
      unfold ReW_to_set_re in H1.
      rewrite (@fold_2 (ReW r1 r2) _ _ _ s1 s2 x (set (set kat * set kat)) _eq _ {}%set)
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
      rewrite (@fold_2 (ReW r1 r2) _ _ _ s1 s2 x0 (set (set kat * set kat)) _eq _ {}%set)
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
    Variables r1 r2:kat.

    Definition MAX_fst := S (sylen r1).
    Definition MAX_snd := S (sylen r2).

    Require Import NArith.
    Require Import wf_extra.
   
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
    Variables r1 r2:kat.
    
    Lemma disj_h_s_inv : forall (h s : set (ReW r1 r2))(ats:set atom)(atsig : set (atom*Z)),
      inter h s === {} -> inter (fst (fst (StepFast' _ _ h s ats atsig)))
                          (snd (fst (StepFast' _ _ h s ats atsig))) === {}.
    Proof.
      intros.
      split;intros.
      apply inter_iff in H0.
      destruct H0 as [H1 H2].
      revert H1 H2.
      unfold StepFast';simpl in *.
      case_eq(choose s).
      intros r Hr.
      destruct(ewp_of_ReW _ _ r ats);simpl in *.
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

    Lemma tranpose_ewp_of_ReW_conj_fold :
      forall ats, transpose eq (fun x : ReW r1 r2 => andb (ewp_of_ReW r1 r2 x ats)).
    Proof.
      repeat red;intros.
      rewrite Bool.andb_assoc.
      rewrite (Bool.andb_comm (ewp_of_ReW r1 r2 x ats) (ewp_of_ReW r1 r2 y ats)).
      rewrite Bool.andb_assoc.
      reflexivity.
    Qed.
    
    Lemma ewp_of_Rew_set_h_inv : forall (h s : set (ReW r1 r2))(ats:set atom)
                                        (atsig : set (atom*Z)),
      inter h s === {} -> ewp_of_ReW_set _ _ h ats = true -> 
      ewp_of_ReW_set _ _ (fst (fst (StepFast' _ _ h s ats atsig))) ats = true.
    Proof.
      intros.
      case_eq(choose s);intros.
      case_eq(ewp_of_ReW _ _ r ats);intros.
      unfold StepFast'.
      rewrite H1,H2.
      simpl.
      unfold ewp_of_ReW_set.
      rewrite fold_add;auto with typeclass_instances.
      rewrite H2;simpl.
      exact H0.
      repeat red.
      intros.
      rewrite <- H3.
      destruct(ewp_of_ReW _ _ x ats).
      simpl.
      assumption.
      simpl.
      reflexivity.
      apply tranpose_ewp_of_ReW_conj_fold.
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
      
    Lemma DP_upd : forall (h s : set (ReW r1 r2))(ats:set atom)(atsig : set (atom*Z)),
      DP _ _ h s ats -> 
      DP _ _ (fst (fst (StepFast' _ _ h s ats atsig)))
             (snd (fst (StepFast' _ _ h s ats atsig))) ats.
    Proof.
      intros.
      destruct H.
      constructor.
      apply disj_h_s_inv with (atsig:=atsig)(ats:=ats) in H.
      exact H.
      apply ewp_of_Rew_set_h_inv;assumption.
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

    Lemma LLim_disj_h_s : forall (h s : set (ReW r1 r2))(ats:set atom)(atsig : set (atom*Z)),
      inter h s === {} -> snd (StepFast' _ _ h s ats atsig) = Process' _ _->
      LLim _ _ (fst (fst (StepFast' _ _ h s ats atsig))) h.
    Proof.
      intros h s ats sig D.
      case_eq(choose s);intros r Hr.
      case_eq(ewp_of_ReW _ _ r ats);simpl;intros.
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
    
    Lemma DP_wf : forall (h s : set (ReW r1 r2))(ats:set atom)(atsig : set (atom*Z)),
      DP _ _ h s ats -> snd (StepFast' _ _ h s ats atsig) = Process' _ _ ->
      LLim _ _ (fst (fst (StepFast' _ _ h s ats atsig))) h.
    Proof.
      intros.
      destruct H.
      apply LLim_disj_h_s. 
      exact H.
      exact H0.
    Qed.

  End DecreasingMeasures.

  Section Iterator.
    Variables r1 r2:kat.
    
    Inductive LastCases : Type := 
      Ok : set (ReW r1 r2) -> LastCases | NotOk : ReW r1 r2 -> LastCases.

    (** Below is the decision procedure we need to build in order to decide
        kat terms equivalence. It is in its general form. Further ahead we 
        reason about it with the proper arguments. *)

    (* begin show *)
    Function decide_re_ref'(h s:set (ReW r1 r2))
      (ats:set atom)(atsig:set (atom*Z))(D:DP _ _ h s ats){wf (LLim r1 r2) h}: LastCases :=
      let f := StepFast' _ _ h s ats atsig in 
        let next := snd f in
          let HistStack := (fst f) in
              match next  with
                | TermFalse' x => NotOk x
                | TermTrue' h  => Ok h(*(fst HistStack)*)
                | Process'  => decide_re_ref' (fst HistStack) (snd HistStack) 
                                              ats atsig (DP_upd _ _ h s ats atsig D)
             end.
    Proof.
      abstract(apply DP_wf).
      exact(guard r1 r2 100 (LLim_wf r1 r2)).
    Defined.
    (* end show *)

    Lemma decide_re_ref'_same_proof_arg :
      forall h s ats atsig D D',
        decide_re_ref' h s ats atsig D = decide_re_ref' h s ats atsig D'.
    Proof.
      intros.
      functional induction(decide_re_ref' h s ats atsig D);
        try now(rewrite decide_re_ref'_equation,e;auto).
      symmetry;rewrite decide_re_ref'_equation.
      rewrite e. rewrite <- IHl. reflexivity.
    Qed.

      

  End Iterator.

  Section ResultContainsOriginal.
    Variables r1 r2: kat.

    (*Require Import ProofIrrelevance.*)

    Lemma decide_re_ref'_1 : forall s h ats sig D,
      forall x , decide_re_ref' _ _ h s ats sig D = x -> 
        forall r s', StepFast' _ _ h s ats sig = (({r;h},s'),Process' r1 r2) ->
          forall D', decide_re_ref' _ _ {r;h} s' ats sig D' = x.
    Proof.
      intros.
      rewrite decide_re_ref'_equation in H.
      pattern (StepFast' _ _ h s ats sig) at 1 in H.
      rewrite H0 in H.
      (* Truque acelera a gravacao da prova. Caso use [simpl] a gravacao 
         da funcao nao sei se termina. *)
      assert(match snd ({r; h}, s',Process' _ _) with
               | Process' =>
                 decide_re_ref' _ _ (fst (fst (StepFast' _ _ h s ats sig)))
                 (snd (fst (StepFast' _ _ h s ats sig))) ats sig
                 (DP_upd _ _ h s ats sig D)
               | TermTrue' h => Ok _ _ h
               | TermFalse' x => NotOk _ _ x
             end = x -> (decide_re_ref' _ _ (fst (fst (StepFast' _ _ h s ats sig))) 
               (snd (fst (StepFast' _ _ h s ats sig))) ats sig
               (DP_upd _ _ h s ats sig D) = x)). 
      abstract (simpl;auto).
      generalize(H1 H).
      intro.
      clear H H1.
      revert H2.
      generalize(DP_upd _ _ h s ats sig D).
      generalize(D').
      rewrite H0.
      simpl.
      intros.
      rewrite <- H2.
      apply decide_re_ref'_same_proof_arg.
    Qed.

    Lemma in_first_ref : forall s h ats sig D x,
      decide_re_ref' _ _ h s ats sig D = Ok r1 r2 x -> h[<=]x.
    Proof.
      intros.
      functional induction (decide_re_ref' r1 r2 h s ats sig D).
      discriminate.
      injection H;intro;subst;clear H.
      revert e.
      unfold StepFast'.
      case_eq(choose s);intros r Hr.
      case_eq(ewp_of_ReW r1 r2 r ats);intro.
      discriminate.
      discriminate.
      simpl in Hr.
      injection Hr;intros.
      subst.
      intuition.
      generalize(IHl H);intro;clear IHl.
      transitivity (fst (fst (StepFast' r1 r2 h s ats atsig)));auto.
      revert e.
      unfold StepFast'.
      case_eq(choose s);intros r Hr.
      case_eq(ewp_of_ReW r1 r2 r ats);intro.
      simpl.
      intro.
      red;intros.
      apply add_2;auto.
      discriminate.
      discriminate.
    Qed.

    Instance andb_fold_ewp_of_ReW : forall ats,
      Proper (_eq ==> eq ==> eq)  (fun x0 : ReW r1 r2 => andb (ewp_of_ReW r1 r2 x0 ats)).
    Proof.
      repeat red.
      intros.
      rewrite H.
      subst.
      reflexivity.
    Qed.

    Lemma transp_andb_fold_ewp_of_ReW : 
      forall ats,
        transpose eq (fun x0 : ReW r1 r2 => andb (ewp_of_ReW r1 r2 x0 ats)).
    Proof.
      repeat red.
      intros.
      rewrite Bool.andb_assoc.
      rewrite (Bool.andb_comm (ewp_of_ReW r1 r2 x ats) (ewp_of_ReW r1 r2 y ats)).
      rewrite Bool.andb_assoc.
      reflexivity.
    Qed.

    Hint Resolve transp_andb_fold_ewp_of_ReW : typeclass_instances.

    Lemma in_first_step_fast' : forall s h ats sig D x r,
      decide_re_ref' r1 r2 h s ats sig D = Ok r1 r2 x -> choose s = Some r ->
      {r;h}[<=]x.
    Proof.
      intros.
      assert(DP r1 r2 {r; h} (r %dF[ {r; h}, sig ] ++ (remove r s)) ats).
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
      case_eq(ewp_of_ReW r1 r2 r ats);intro.
      unfold ewp_of_ReW_set.
      rewrite fold_add;eauto with typeclass_instances.
      rewrite H1.
      simpl.
      exact e0.
      intro.
      apply choose_1 in H0.
      assert(r \In inter h s).
      apply inter_iff;split;auto with typeclass_instances.
      apply e in H3.
      inversion H3.
      rewrite decide_re_ref'_equation in H.
      revert H.
      generalize(is_dpt r1 r2 h s ats e e0).
      unfold StepFast'.
      intro.
      generalize(DP_upd r1 r2 h s ats sig d).
      unfold StepFast'.
      rewrite H0,H1.
      discriminate.
      revert H.
      rewrite decide_re_ref'_equation.
      generalize(DP_upd r1 r2 h s ats sig D).
      unfold StepFast'.
      rewrite H0.
      case_eq(ewp_of_ReW r1 r2 r ats).
      intro.
      simpl.
      intros.
      apply in_first_ref in H2.
      assumption.
      simpl.
      discriminate.
    Qed.

    Lemma in_first_stepfast' : forall s h ats sig D x r,
      decide_re_ref' r1 r2 h s ats sig D = Ok r1 r2 x -> choose s = Some r ->
      {r;h}[<=]x.
    Proof.
      intros.
      assert(StepFast' r1 r2 h s ats sig = 
             (({r;h},r %dF[ {r;h}, sig ] ++ (remove r s)),Process' r1 r2)).
      unfold StepFast'.
      rewrite H0.
      case_eq(ewp_of_ReW r1 r2 r ats);intro.
      reflexivity.
      rewrite decide_re_ref'_equation in H.
      revert H.
      generalize(DP_upd r1 r2 h s ats sig D).
      unfold StepFast'.
      rewrite H0.
      rewrite H1.
      simpl.
      discriminate.
      assert(DP r1 r2 {r; h} (r %dF[ {r; h}, sig ] ++ (remove r s)) ats).
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
      case_eq(ewp_of_ReW r1 r2 r ats);intro.
      unfold ewp_of_ReW_set.
      rewrite fold_add;eauto with typeclass_instances.
      rewrite H2.
      simpl.
      exact e0.
      intro.
      apply choose_1 in H0.
      assert(r \In inter h s).
      apply inter_iff;split;auto with typeclass_instances.
      apply e in H4.
      inversion H4.
      unfold StepFast' in H1.
      rewrite H0,H2 in H1.
      discriminate.
      generalize(decide_re_ref'_1 _ _ _ _ _ _ H r _ H1 H2).
      intro.
      generalize(in_first_step_fast' _ _ _ _ _ _ r H H0);auto.
    Qed.

    (** Below, [ats] must be substituted by the set of all possible atoms generated
        from the tests in both [r1] and [r2]. *)

    Lemma decide_re_ref'_contains_orig_aux : forall ats sig D x r,
      decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set ats sig D = Ok r1 r2 x -> 
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
      generalize(in_first_step_fast' _ _ _ _ _ x r H H0).
      intro.
      apply H3.
      apply add_1.
      assumption.
    Qed.

    Lemma decide_re_ref'_contains_orig_hip : forall ats sig D x,
      decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set ats sig D = Ok r1 r2 x -> 
        exists r, choose {ReW_1st r1 r2}%set = Some r.
    Proof.
      intros.
      rewrite decide_re_ref'_equation in H.
      unfold StepFast' at 1 in H.
      case_eq(choose {ReW_1st r1 r2});intros.
      rewrite H0 in H.
      case_eq(ewp_of_ReW r1 r2 r ats);intro.
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

    Lemma decide_re_ref'_contains_orig : forall ats sig D x,
      decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set ats sig D = Ok r1 r2 x -> 
        ReW_1st r1 r2 \In x.
    Proof.
      intros.
      destruct (decide_re_ref'_contains_orig_hip ats sig D x). 
      assumption.
      exact(decide_re_ref'_contains_orig_aux ats sig D x x0 H H0). 
    Qed.

  End ResultContainsOriginal.

  Section IteratorInvariant.
    Variables r1 r2:kat.

    Global Instance not_in_set_add_m : 
      Proper (_eq ==> eq) (fun x : ReW r1 r2 => negb (x \in {r; h})).
    Proof.
      repeat red;intros.
      rewrite H.
      reflexivity.
    Qed.

    (** Invariant of [decide_re]. *)
    Definition invP'(h s:set (ReW r1 r2))(ats:set atom)(sig:set (atom*Z))(*(sig:set Z)*) :=
      forall x, x \In h ->
        forall a, a \In sig -> 
                  (*forall b, b \In ats -> *)
                  (ReW_pdrv r1 r2 x (fst a) (snd a)) \In (h ++ s).
    
    (** Invariant enriched with correctness criteria of [ewp_of_ReW]. *)
    Definition invP_final'(h s:set (ReW r1 r2))(ats:set atom)(sig:set (atom*Z)) :=
      (ReW_1st r1 r2) \In (h ++ s) /\
      (forall x, x \In (h++s) -> ewp_of_ReW r1 r2 x ats = true) /\ invP' h s ats sig.


    Global Instance add_pair_m :
      forall y:atom,
        Proper (_eq ==> Equal ==> Equal) (fun x1 : Z => add (y, x1)).
    Proof.
      repeat red.
      split;intros.
      apply add_iff in H1.
      destruct H1.
      rewrite <- H1.
      apply add_1.
      split;auto with typeclass_instances.
      apply add_2;auto with typeclass_instances.
      apply H0;auto.
      apply add_iff in H1.
      destruct H1.
      rewrite <- H1.
      apply add_1.
      split;auto with typeclass_instances.
      apply add_2;auto with typeclass_instances.
      apply H0;auto.
    Qed.      
    
    Lemma add_pair_transp :
      forall y:atom, 
        transpose Equal (fun x1 : Z => add (y, x1)).
    Proof.
      repeat red.
      split;intros.
      apply add_iff in H;destruct H.
      rewrite H.
      apply add_2;apply add_1;auto.
      apply add_iff in H;destruct H.
      rewrite H.
      apply add_1;reflexivity.
      apply add_2;apply add_2;auto.
      apply add_iff in H;destruct H.
      rewrite H.
      apply add_2;apply add_1;auto.
      apply add_iff in H;destruct H.
      rewrite H.
      apply add_1;reflexivity.
      apply add_2;apply add_2;auto.
    Qed.

    Hint Resolve add_pair_transp : typeclass_instances.

    Lemma set_sig_atom_set_same_atom :
      forall x y s,
        x === y ->
        set_sig_atom_set x s === set_sig_atom_set y s.
    Proof.
      induction s using set_induction;intros.
      unfold set_sig_atom_set.
      do 2 (rewrite fold_1b;auto).
      unfold set_sig_atom_set.
      rewrite fold_2;eauto with typeclass_instances.
      symmetry.
      rewrite fold_2;eauto with typeclass_instances.
      apply add_m;auto.
      apply ord_Eq_unique in H1.
      rewrite H1.
      reflexivity.
      apply ord_Eq_unique in H1.
      rewrite H1.
      reflexivity.
    Qed.

    Global Instance set_sig_atom_set_m :
             Proper(_eq ==> _eq ==> _eq) set_sig_atom_set.
    Proof.
      repeat red.
      intros x y H x0.
      revert x y H.
      induction x0 using set_induction;intros.
      split;intros.
      unfold set_sig_atom_set in H2.
      rewrite fold_1b in H2;auto.
      inv H2.
      assert(Empty y0).
      rewrite <- H1.
      apply H.
      unfold set_sig_atom_set in H2.
      rewrite fold_1b in H2;auto.
      inv H2.
      split;intros.
      unfold set_sig_atom_set in H3.
      rewrite (@fold_2 (Z) _ _ _ x0_1 x0_2 x (set (atom*Z)) _ _ {} (fun x : Z => add (x0, x))) in H3;eauto with typeclass_instances.
      simpl in H3.
      apply add_iff in H3.
      destruct H3.
      assert(SetProperties.Add x x0_1 y0).
      apply Add_Equal.
      rewrite <- H2.
      apply Add_Equal in H0.
      rewrite H0.
      reflexivity.
      unfold set_sig_atom_set.
      rewrite (@fold_2 (Z) _ _ _ x0_1 y0 x (set (atom*Z)) _ _ {} (fun x1 : Z => add (y, x1)));eauto with typeclass_instances.
      apply add_1.
      rewrite <- H3.
      split;eauto with typeclass_instances.
      assert(SetProperties.Add x x0_1 y0).
      apply Add_Equal.
      rewrite <- H2.
      apply Add_Equal in H0.
      rewrite H0.
      reflexivity.
      unfold set_sig_atom_set.
      rewrite (@fold_2 (Z) _ _ _ x0_1 y0 x (set (atom*Z)) _ _ {} (fun x1 : Z => add (y, x1)));eauto with typeclass_instances.
      apply add_2.
      unfold _eq in H1. simpl in H1.
      rewrite H1 in H3.
      assumption.
      
      assert(SetProperties.Add x x0_1 y0).
      apply Add_Equal.
      rewrite <- H2.
      apply Add_Equal in H0.
      rewrite H0.
      reflexivity.
      unfold set_sig_atom_set in H3.
      rewrite (@fold_2 (Z) _ _ _ x0_1 y0 x (set (atom*Z)) _ _ {} (fun x : Z => add (y, x))) in H3;eauto with typeclass_instances.
      simpl in H3.
      apply add_iff in H3.
      destruct H3.
      unfold set_sig_atom_set.
      rewrite (@fold_2 (Z) _ _ _ x0_1 x0_2 x (set (atom*Z)) _ _ {} (fun x1 : Z => add (x0, x1)));eauto with typeclass_instances.
      apply add_1.
      rewrite <- H3.
      split;eauto with typeclass_instances.
      unfold set_sig_atom_set.
      rewrite (@fold_2 (Z) _ _ _ x0_1 x0_2 x (set (atom*Z)) _ _ {} (fun x1 : Z => add (x0, x1)));eauto with typeclass_instances.
      apply add_2.
      repeat red in H1;simpl in H1.
      rewrite H1.
      assumption.
    Qed.

    Global Instance union_set_sig_atom_set_m :
             forall s,
               Proper (_eq ==> Equal ==> Equal)
                    (fun x0 : atom => union (set_sig_atom_set x0 s)).
    Proof.
      repeat red.
      split;intros.
      apply union_iff in H1.
      destruct H1.
      rewrite H in H1.
      apply union_2;auto.
      apply union_3.
      apply H0;auto.
      rewrite H.
      rewrite H0.
      assumption.
    Qed.

    Lemma union_set_sig_atom_set_transp :
      forall sig,
        transpose Equal (fun x0 : atom => union (set_sig_atom_set x0 sig)).
    Proof.
      repeat red.
      split;intros.
      apply union_iff in H;destruct H.
      apply union_3;apply union_2;auto.
      apply union_iff in H;destruct H.
      apply union_2;auto.
      (do 2 (apply union_3));auto.
      apply union_iff in H;destruct H.
      apply union_3;apply union_2;auto.
      apply union_iff in H;destruct H.
      apply union_2;auto.
      (do 2 (apply union_3));auto.
    Qed.

    Hint Resolve union_set_sig_atom_set_transp : typeclass_instances.

    Lemma set_sig_atom_set_first_elem_eq :
      forall sig a b,
       a \In sig -> (b, a) \In set_sig_atom_set b sig.
    Proof.
      induction sig using set_induction;intros.
      apply H in H0;elim H0.
      unfold set_sig_atom_set.
      rewrite fold_2;eauto with typeclass_instances.
      apply H0 in H1.
      destruct H1.
      apply add_1.
      rewrite H1.
      reflexivity.
      apply add_2.
      apply IHsig1;eauto.
    Qed.

    Lemma in_set_sig_atom_set_SyAt :
      forall ats sig a b,
        a \In sig ->
        b \In ats ->
        (b,a) \In set_sig_atom_set_SyAt ats sig.
    Proof.
      induction ats using set_induction;intros.
      apply H in H1.
      elim H1.
      unfold set_sig_atom_set_SyAt.
      rewrite fold_2;eauto with typeclass_instances.
      apply H0 in H2.
      destruct H2.
      rewrite H2.
      apply union_2.
      apply set_sig_atom_set_first_elem_eq;auto.
      apply union_3.
      apply IHats1;assumption.
    Qed.

    Lemma invP_inv' : forall h s (ats:set atom)(sig:set (atom*Z)), 
      invP' h s ats sig -> 
      invP' (fst (fst (StepFast' r1 r2 h s ats sig))) 
      (snd (fst (StepFast' r1 r2 h s ats sig))) ats sig. 
    Proof.
      intros *.
      case_eq(choose s);intros.
      unfold invP' in H0.
      unfold StepFast'.
      rewrite H.
      case_eq(ewp_of_ReW r1 r2 r ats);intros.
      simpl.
      unfold invP';intros.
      destruct(In_dec ((x %d[(fst a)]) (snd a)) h).
      apply union_2.
      apply add_2;auto.
      apply add_iff in H2;destruct H2.
      destruct(eq_dec ((x %d[fst a]) (snd a)) x).
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
      destruct(eq_dec ((x %d[fst a]) (snd a)) r).
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
      unfold invP'.
      unfold StepFast'.
      rewrite H.
      simpl.
      assumption.
    Qed.

    Lemma invP_decide_re_correct' : forall h s ats sig D x,
      invP' h s ats sig -> decide_re_ref' r1 r2 h s ats sig D = Ok r1 r2 x -> 
      invP' x {}%set ats sig.
    Proof.
      intros.
      functional induction (decide_re_ref' r1 r2 h s ats sig D).
      discriminate.
      case_eq(choose s);intros.
      unfold StepFast' in e.
      rewrite H1 in e.
      case_eq(ewp_of_ReW r1 r2 r ats);intros.
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

    (** Here also [ats] must be replaced. *)

    Definition mkDP_ini (ats:set atom) : DP r1 r2 ({}%set) ({ReW_1st r1 r2}%set) ats.
    Proof.
      abstract(constructor;
      split;intros;try abstract(inversion H);
      vm_compute;
      reflexivity).
    Defined.

    Lemma invP'_decide_re_initial_correct : 
      forall x ats s, 
        decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set ats s (mkDP_ini ats) = Ok r1 r2 x ->
        invP' x {}%set ats s.
    Proof.
      intros.
      eapply (invP_decide_re_correct' {} {ReW_1st r1 r2} ats s (mkDP_ini ats)).
      unfold invP'.
      intros.
      abstract(inversion H0).
      apply H.
    Qed.
    
  End IteratorInvariant.

  Section CorrectnessArgument.
    Variables r1 r2 : kat.

    (* ESTE TEM QUE SAIR DAQUI E IR PARA O dsr_dsl.v *)
    

    Lemma atsy_list_leibniz :
      forall x y : list AtSy,
        x === y -> x = y.
    Proof.
      induction x;intros.
      inv H.
      inv H.
      subst.
      inv H.
      subst.
      apply IHx in H7.
      subst.
      destruct a.
      destruct a'.
      simpl in H2.
      destruct H2.
      subst.
      reflexivity.
    Qed.

    Instance ewp_of_rep_ReW_wpdrv_flip_m : 
      Proper (_eq ==> flip eq ==> flip eq)
             (fun p : atom => andb (ewp_of_rep (ReW_wpdrv r1 r2 w0) p)).
    Proof.
      repeat red.
      intros.
      normalize_notations.
      inv H.
    Qed.
    
    Lemma ewp_of_rep_ReW_wpdrv_flip_transp :
      forall w0,
        transpose (flip eq) (fun p : atom => andb (ewp_of_rep (ReW_wpdrv r1 r2 w0) p)).
    Proof.
      repeat red.
      intros.
      rewrite Bool.andb_assoc.
      rewrite (Bool.andb_comm 
                   (ewp_of_rep (ReW_wpdrv r1 r2 w0) y) 
                   (ewp_of_rep (ReW_wpdrv r1 r2 w0) x)).
      simpl.
      rewrite Bool.andb_assoc.
      reflexivity.
    Qed.

    Hint Resolve ewp_of_rep_ReW_wpdrv_flip_transp : typeclass_instances.

    Lemma correct_aux : 
      forall w ats a,
        ewp_of_rep_at (ReW_wpdrv r1 r2 w) ats = true ->
        a \In ats ->
        ewp_set (r1 %dW w) a = ewp_set (r2 %dW w) a.
    Proof.
      induction ats using set_induction;intros.
      apply H in H1;elim H1.
      unfold ewp_of_rep_at in H1.
      rewrite fold_2 in H1;eauto with typeclass_instances.
      apply Bool.andb_true_iff in H1.
      destruct H1.
      unfold ewp_of_rep in H1.
      simpl in H1.
      apply H0 in H2.
      destruct H2.
      rewrite H2 in H1.
      unfold wpdrv_set in H1.
      fold (wpdrv r1 w0) in H1.
      fold (wpdrv r2 w0) in H1.
      apply Bool.eqb_prop in H1.
      assumption.
      apply IHats1;auto.
    Qed.

    Lemma correct_aux_aux : 
      forall w a,
        ewp_of_rep_at (ReW_wpdrv r1 r2 w) (smaller_ordsS (pow2 (ntests))) = true ->
        a \In (smaller_ordsS (pow2 ntests)) ->
        ewp_set (r1 %dW w) a = ewp_set (r2 %dW w) a.
    Proof.
      intros.
      eapply correct_aux.
      apply H.
      assumption.
    Qed.
    
    Print atom.

    Lemma invP_final_eq_lang' : 
      forall x,
        decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set 
         (smaller_ordsS (pow2 ntests)) 
         (set_sig_atom_set_SyAt (smaller_ordsS (pow2 ntests)) 
                                (ss r1 ++ ss r2)) 
         (mkDP_ini r1 r2 (smaller_ordsS (pow2 ntests))) = Ok r1 r2 x ->   
        invP_final' r1 r2 x {}%set 
                    (smaller_ordsS (pow2 ntests)) 
                    (set_sig_atom_set_SyAt (smaller_ordsS (pow2 ntests)) 
                                (ss r1 ++ ss r2)) -> gl_eq (kat2gl r1) (kat2gl r2).
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
      assert(forall x0 : ReW r1 r2, 
               x0 \In x ->
               ewp_of_ReW _ _ x0 (smaller_ordsS (pow2 ntests)) = true).
      intros.
      apply H2.
      apply union_2;auto.
      clear H2.
      assert(forall x0 : ReW r1 r2,
       x0 \In x ->
       forall a : atom * Z,
       a \In
       set_sig_atom_set_SyAt (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2) ->
       (x0 %d[ fst a ]) (snd a) \In x).
      intros.
      pose proof H3 x0 H2 a H4.
      apply union_iff in H5;destruct H5.
      assumption.
      abstract(inversion H5).
      clear H3.
      assert(forall w, (@>w) ∈ langSsy (ss r1 ++ ss r2) ->  ReW_wpdrv r1 r2 (@>w) \In x).
      induction w0.
      simpl.
      assert(ReW_wpdrv r1 r2 nil === ReW_1st r1 r2) by
      (vm_compute;split;intros;auto).
      intros.
      rewrite H3.
      assumption.
      simpl.
      rewrite ReW_wpdrv_step.
      intro.
      apply H2.
      apply IHw0.
      apply word_concat_sy_in_langSsy in H3.
      destruct H3.
      assumption.
      apply word_concat_sy_in_langSsy in H3;
         destruct H3;auto.      
      inversion_clear H4.
      apply  in_set_sig_atom_set_SyAt.
      assumption.
      apply all_in_smaller_ordsS.

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
      apply atsy_list_leibniz in H4.
      rewrite H4.
      reflexivity.
      intros.
      rewrite H5.
      apply H3.
      apply atsy_list_leibniz in H4.
      rewrite H4.
      assumption.

      assert(forall w, w ∈ langSsy (ss r1 ++ ss r2) -> ewp_of_ReW _ _ (ReW_wpdrv r1 r2 w) (smaller_ordsS (pow2 ntests)) = true).
      intros.
      apply H1.
      apply H4.
      assumption.
      assert(forall w a, w ∈ langSsy (ss r1 ++ ss r2) -> a \In (smaller_ordsS (pow2 ntests)) ->  ewp_set (wpdrv r1 w) a = ewp_set (wpdrv r2 w) a).
      intros.
      pose proof correct_aux.
      specialize H5 with w0.
      unfold ewp_of_ReW in H5.
      pose proof H8 w0 (smaller_ordsS (pow2 ntests)) a (H5 H6) H7.
      assumption.
      apply word_of_langSsy_decide_equiv_set.
      intros.
      apply H6.
      assumption.
      assumption.
    Qed.

    Definition equiv_re_ref_aux'(h s:set (ReW r1 r2))
      (ats:set atom)(sig:set (atom*Z))(D:DP r1 r2 h s ats) :=
      let H := decide_re_ref' r1 r2 h s ats sig D in
        match H with
          | Ok _ => true
          | _ => false
        end.

    Definition equiv_re_ref' (ats:set atom)(sig:set Z) :=
      equiv_re_ref_aux' {}%set {ReW_1st r1 r2}%set ats 
       (set_sig_atom_set_SyAt ats sig) (mkDP_ini r1 r2 ats).

    (** The final decision procedure. Still we have to change the input and build
        the set of pairs [(atom,symbol)] instead of feeding the decision procedure
        with the separated sets and buid them each time they are needed. *)                        
    Definition equivP := equiv_re_ref' (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2).

    Lemma decide_ref_subset_decide_re_all_c : forall h s ats sig D x,
      decide_re_ref' r1 r2 h s ats sig D = Ok r1 r2 x ->
      ewp_of_ReW_set r1 r2 x ats = true.
    Proof.
      intros.
      functional induction (decide_re_ref' r1 r2 h s ats sig D).
      abstract discriminate.
      injection H;intros.
      rewrite H0 in e.
      (*clear H H0 h0.*)
      revert e.
      unfold StepFast'.
      case_eq(choose s).
      intros r Hr.
      case_eq(ewp_of_ReW r1 r2 r ats);simpl;intros.
      abstract discriminate.
      abstract discriminate.
      simpl;intros.
      injection e;intros.
      destruct D.
      rewrite H2 in H4. (*;clear H H0.*)
      exact H4.
      exact(IHl H).
    Qed.

    Lemma correct_aux_1 : forall s ats sig,
      decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set ats (set_sig_atom_set_SyAt ats sig) (mkDP_ini r1 r2 ats) 
        = Ok r1 r2 s -> equiv_re_ref' ats sig = true.
    Proof.
      intros.
      unfold equiv_re_ref'.
      unfold equiv_re_ref_aux'.
      rewrite H.
      reflexivity.
    Qed.

    Lemma correct_aux_2 : forall s ats sig,
      decide_re_ref' r1 r2 {}%set {ReW_1st r1 r2}%set ats (set_sig_atom_set_SyAt ats sig)  (mkDP_ini r1 r2 ats) 
        = NotOk r1 r2 s -> equiv_re_ref' ats sig = false.
    Proof.
      intros.
      unfold equiv_re_ref'.
      unfold equiv_re_ref_aux'.
      rewrite H.
      reflexivity.
    Qed.
    
    Lemma decide_ref_subset_decide_re_not_ok : forall h s ats sig D x,
      decide_re_ref' r1 r2 h s ats sig D = NotOk r1 r2 x -> 
      ewp_of_ReW r1 r2 x ats = false.
    Proof.
      intros.
      functional induction (decide_re_ref' r1 r2 h s ats sig D).
      injection H;clear H;intros.
      subst.
      revert e.
      unfold StepFast'.
      case_eq(choose s).
      intros r Hr.
      case_eq(ewp_of_ReW r1 r2 r ats);intro.
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
    Variables r1 r2 : kat.

    Lemma equiv_re_true : 
      equiv_re_ref' r1 r2 (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2) = true -> gl_eq (kat2gl r1) (kat2gl r2).
    Proof.
      intro.
      case_eq(decide_re_ref' r1 r2 {} {ReW_1st r1 r2} (smaller_ordsS (pow2 ntests)) 
                             (set_sig_atom_set_SyAt (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2)) (mkDP_ini r1 r2 (smaller_ordsS (pow2 ntests)) )).
      intros s H1.
      eapply invP_final_eq_lang' with (x:=s). 
      exact H1.
      split.
      abstract(apply union_2;
      exact(decide_re_ref'_contains_orig r1 r2 (smaller_ordsS (pow2 ntests)) 
                             (set_sig_atom_set_SyAt (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2)) (mkDP_ini r1 r2 (smaller_ordsS (pow2 ntests))) s H1)).
      split;intros.
      abstract(apply decide_ref_subset_decide_re_all_c in H1;
      apply union_1 in H0;destruct H0;[
      exact(wit_all_in_ewp_of_ReW_set r1 r2 s (smaller_ordsS (pow2 ntests)) H1 x H0)|
      inversion H0]).
      abstract(apply invP'_decide_re_initial_correct in H1;
      exact H1).
  
      intros.
      apply correct_aux_2 in H0.
      rewrite H0 in H.
      abstract(discriminate).
    Qed.

    Lemma equiv_re_false : equiv_re_ref' r1 r2 (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2)  = false -> 
                           ~(gl_eq (kat2gl r1) (kat2gl r2)).
    Proof.
      intros.
      case_eq(decide_re_ref' r1 r2 {} {ReW_1st r1 r2} 
               (smaller_ordsS (pow2 ntests)) 
                             (set_sig_atom_set_SyAt (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2)) (mkDP_ini r1 r2 (smaller_ordsS (pow2 ntests))));
        intros.
      apply correct_aux_1 in H0.
      abstract(rewrite H0 in H;discriminate).
      apply decide_ref_subset_decide_re_not_ok in H0.
      apply  ewp_of_ReW_diff_wpdrvs_Srels in H0.
      exact H0.
    Qed.

  End EquivPCorrectness.
  
  Section EquivPCompleteness.
    Variables r1 r2:kat.

    Theorem equiv_re_complete_true : gl_eq (kat2gl r1) (kat2gl r2) -> 
      equiv_re_ref' r1 r2 (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2) = true.
    Proof.
      intros.
      case_eq(equiv_re_ref' r1 r2 (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2));intros.
      reflexivity.
      apply equiv_re_false in H0.
      contradiction.
    Qed.
  
    Lemma equiv_re_complete_false : ~(gl_eq (kat2gl r1) (kat2gl r2)) -> 
      equiv_re_ref' r1 r2 (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2) = false.
    Proof.
      intros.
      case_eq(equiv_re_ref' r1 r2 (smaller_ordsS (pow2 ntests)) (ss r1 ++ ss r2));intros.
      apply equiv_re_true in H0.
      contradiction.
      reflexivity.
    Qed.
    
  End EquivPCompleteness.

  (** * The automatic proof tactic [dec_equivP] *)
  Ltac re_inequiv :=
    apply equiv_re_false;vm_compute;
      first [ reflexivity | fail 2 "kat terms not inequivalent" ].

  Ltac re_equiv :=
    apply equiv_re_true;vm_compute;
      first [ reflexivity | fail 2 "kat terms are not equivalent" ].

  Ltac dec_re :=
    match goal with
      | |- gl_eq (kat2gl (?R1)) (kat2gl (?R2)) => re_equiv
      | |- ~(gl_eq (kat2gl (?R1))  (kat2gl (?R2))) => re_inequiv
      (* | |- re2rel (?R1) \\<= re2rel (?R2) =>  *)
      (*   unfold lleq;change (R1 \\+ R2) with (re2rel (R1 \+ R2)); *)
      (*     re_equiv *)
      | |- _  => fail 2 "Not a kat term (in-)equivalence equation."
    end.

End KATDec.