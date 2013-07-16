Require Import base.

Generalizable All Variables.

Section BasicOnes.

  Context `{X:OrderedType A}.

  Ltac set_induction s :=
    induction s using set_induction.

  Open Scope set_scope.

  Lemma empty_union_left :
    forall s,
      {} ++ s === s.
  Proof.
    intro s.
    set_induction s.
    split;intros.
    apply union_iff in H0.
    destruct H0.
    inversion H0.
    assumption.
    apply union_3;auto.

    apply Add_Equal in H0.
    rewrite H0.
    split;intros.
    apply union_iff in H1;destruct H1.
    inversion H1.
    assumption.
    apply union_3;auto.
  Qed.

  Lemma empty_union_right :
    forall s,
      s ++ {} === s.
  Proof.
    intro s.
    set_induction s.
    split;intros.
    apply union_iff in H0.
    destruct H0.
    assumption.
    inversion H0.
    apply union_2;auto.

    apply Add_Equal in H0.
    rewrite H0.
    split;intros.
    apply union_iff in H1;destruct H1.
    assumption.
    inversion H1.
    apply union_2;auto.
  Qed.

  Lemma neg_union : 
    forall s1 s2:set A,
    forall x:A,
      ~(x \In s1 ++ s2) -> ~(x \In s1) /\ ~(x \In s2).
  Proof.
    intro s1.
    set_induction s1.
    intros.
    split.
    intro.
    apply H in H1.
    elim H1.
    intro.
    apply  H0.
    apply union_3.
    assumption.

    intros.
    split.
    intro.
    apply H1.
    apply union_2;auto.
    intro.
    apply H1.
    apply union_3;auto.
  Qed.

  Lemma neg_subset_add :
    forall s2 s3 x,
      ~ {x; s2}[<=]s3 -> ~(x \In s3) \/ ~(s2[<=]s3).
  Proof.
    intro s2.
    set_induction s2.
    intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    left;intro.
    apply H0.
    red;intros.
    apply add_iff in H2;destruct H2.
    rewrite <- H2;auto.
    inversion H2.

    intros.
    apply Add_Equal in H0.
    rewrite H0 in H1.
    destruct(In_dec x0 s3).
    assert(~ {x; s2_1}[<=]s3).
    intro.
    eapply H1.
    red;intros.
    apply add_iff in H3;destruct H3.
    rewrite <- H3;auto.
    apply H2.
    assumption.
    apply IHs2_1 in H2.
    destruct H2.
    right.
    intro.
    rewrite H0 in H3.
    apply H1.
    red;intros.
    apply add_iff in H4.
    destruct H4.
    rewrite <- H4;auto.
    apply H3;auto.
    rewrite H0.
    right;intro.
    apply H1.
    red;intros.
    apply add_iff in H4.
    destruct H4.
    rewrite <- H4;auto.
    apply H3.
    assumption.
    left;auto.
  Qed.


  Lemma neg_subset :
    forall s1 s2 s3:set A,
      ~(s1++s2[<=]s3) -> 
      ~(s1[<=]s3) \/ ~(s2[<=]s3).
  Proof.
    intro s1.
    set_induction s1;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0 |- *.
    right.
    rewrite empty_union_left in H0.
    assumption.

    apply Add_Equal in H0.
    rewrite H0 in H1 |- *.
    rewrite union_add in H1.
    apply neg_subset_add in H1.
    destruct H1.
    left;intro.
    assert(x \In s3).
    apply H2.
    apply add_1.
    reflexivity.
    contradiction.
    apply IHs1_1 in H1.
    destruct H1.
    left;intro.
    assert(s1_1[<=]s3).
    red;intros.
    apply H2.
    apply add_2;auto.
    contradiction.
    right;auto.
  Qed.

End BasicOnes.

Section ExtraMaps.

  Local Open Scope set_scope.
  Context `{HA : OrderedType A, HB: OrderedType B}.
  Variable f : A -> B.

  Hypothesis f_proper_hip : Proper(_eq ==> _eq) f.

  Global Instance proper_f_add_map :
           Proper (_eq ==> Equal ==> Equal) (fun (x0 : A) (s : set B) => {f x0; s}).
  Proof.
    repeat red.
    split;intros.
    apply add_iff in H1;destruct H1.
    rewrite <- H1.
    apply add_1;auto.
    rewrite H.
    reflexivity.
    apply add_2.
    rewrite H0 in H1;auto.
    apply add_iff in H1;destruct H1.
    rewrite <- H1.
    apply add_1;auto.
    rewrite H;auto.
    apply add_2;apply H0;auto.
  Qed.

  Lemma f_add_map_transpose :
    transpose Equal (fun (x0 : A) (s : set B) => {f x0; s}).
  Proof.
    repeat red.
    split;intros.
    apply add_iff in H;destruct H.
    rewrite <- H;apply add_2;apply add_1;auto.
    apply add_iff in H;destruct H.
    rewrite H;apply add_1;auto.
    do 2 apply add_2.
    assumption.
    apply add_iff in H;destruct H.
    rewrite <- H;apply add_2;apply add_1;auto.
    apply add_iff in H;destruct H.
    rewrite H;apply add_1;auto.
    do 2 apply add_2.
    assumption.
  Qed.

  Hint Resolve f_add_map_transpose : typeclass_instances.

  Lemma map_In_aux : forall s a i, 
   a \In (fold (fun x s => add (f x) s) s i) <-> 
   a \In i \/ exists b, b \In s /\ (f b) === a.
  Proof.
    induction s as [ s EM | s1 s2 IHs1 x NI AD] using set_induction; intros.
    rewrite (fold_1 (s:=s)); firstorder.
    rewrite (fold_2 ); eauto with typeclass_instances.
    rewrite add_iff. rewrite IHs1. 
    assert (x \In s2) by (rewrite (AD x); auto).
    assert (Subset s1 s2) by (intros y Hy; rewrite (AD y); auto).
    intuition.
    right; exists x; auto.
    right; destruct H1 as (b & ? & ?); exists b; auto.
    destruct H2 as (b & H1 & H2); rewrite (AD b) in H1; destruct H1.
    left; eauto with typeclass_instances.
    rewrite H1.
    assumption.
    right; right; exists b; auto.
  Qed.

  Lemma map_cardinal_aux : 
    forall s i, 
      (forall x y, x \In s -> y \In s -> (f x) === (f y) -> x === y) ->
      (forall x, x \In s -> ~((f x) \In i)) -> 
      cardinal (fold (fun x s => add (f x) s) s i) = 
               cardinal i + cardinal s.
  Proof.
    induction s as [ s EM | s1 s2 IHs1 x NI AD] using set_induction; intros.
    rewrite (fold_1 (s:=s)), (cardinal_1 EM); auto with typeclass_instances.
    rewrite (fold_2 ); auto with typeclass_instances.
    2:apply NI.
    2:apply AD.
    assert (x \In s2) by (rewrite (AD x); auto).
    assert (Subset s1 s2) by (intros y Hy; rewrite (AD y); auto).
    rewrite add_cardinal_2, IHs1, (cardinal_2 NI AD); eauto.
    rewrite map_In_aux; red; destruct 1 as [ | (b & ? & ?) ].
    firstorder.
    rewrite <- (H b x) in NI; auto.
  Qed.
  
  Lemma map_cardinal : 
    forall s, 
      (forall x y, x \In s -> y \In s -> (f x) === (f y) -> x === y) ->
      cardinal (map f s) = cardinal s.
  Proof.
    Transparent map.
    intros; unfold map; rewrite map_cardinal_aux; auto with set.
    intros.
    intro.
    inversion H1.
  Qed.

End ExtraMaps.




 
