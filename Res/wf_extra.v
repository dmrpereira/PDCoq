Require Import Wellfounded Wf_nat Lexicographic_Product Relation_Operators.
Require Import base generic_set_theory.
Require Import NArith NArith.Nnat.

Section LIM_CARD.

  Variable A:Type.
  Context `{AOrd : OrderedType A}.
    
  Inductive lim_card (z:nat) : set A -> set A -> Prop :=
  | in_re_set : forall x y:set A, 
    z - (cardinal x) < z - (cardinal y) -> lim_card z x y.

  Definition lim_cardN (z:N) : relation (set A) :=
  fun x y:set A => nat_of_N z - (cardinal x) < nat_of_N z - (cardinal y).

  Theorem le_trans1 : forall n m p, n <= m -> m <= p -> n <= p.
  Proof.
    induction 2; auto.
  Defined.

  Theorem le_S_n1 : forall n m, S n <= S m -> n <= m.
  Proof.
    intros n m H; change (pred (S n) <= pred (S m)) in |- *.
    destruct H; simpl. 
    constructor.
    apply (le_trans1 _ (S n) _).
    constructor.
    constructor.
    exact H.
  Defined.

  Lemma lim_card_wf : forall z,  well_founded (lim_card z).
  Proof.
    unfold well_founded.
    intros.
    cut(forall n a, lt (z - (cardinal a)) n -> Acc (lim_card z) a).
    intros.
    eapply H with (S (z - (cardinal a))).
    unfold lt.
    constructor.
      
    induction n;intros.
    inversion H.
    constructor;intros.
    inversion_clear H0.
    apply IHn.
    unfold lt in H, H1.
    unfold lt.
    apply (@le_trans1 _ _ _ H1).
    apply le_S_n1 in H.
    exact H.
  Defined.

  Lemma lim_card_lim_cardN_inclusion :
    forall z, inclusion (set A) (lim_cardN z) (lim_card (nat_of_N z)).
  Proof.
    repeat red.
    intros.
    unfold lim_cardN in H.
    constructor.
    assumption.
  Qed.

  Lemma lim_cardN_wf : forall z, well_founded (lim_cardN z).
  Proof.
    intro z.
    red.
    eapply wf_incl.
    eapply lim_card_lim_cardN_inclusion.
    apply lim_card_wf.
  Qed.

  (* Definition dec_H (x y:set A) := *)
  (*   cardinal x < cardinal y. *)

  (* Lemma dec_H_wf : well_founded dec_H. *)
  (* Proof. *)
  (*   red. *)
  (*   intros. *)
  (*   apply Acc_inverse_image. *)
  (*   apply Wf_nat.lt_wf. *)
  (* Defined. *)
  
  Open Scope N_scope.

  Fixpoint pow2N(n:nat):N :=
    match n with
      | O => 1
      | S m => 2 * pow2N m
    end.

  Lemma pow2N_S : forall n,
    pow2N (S n) = 2*pow2N n.
  Proof.
    induction n.
    reflexivity.
    destruct n;auto with arith.
  Qed.

  Close  Scope N_scope.

  Lemma pow2N_S_nat : forall n,
    nat_of_N (pow2N (S n)) = 2*nat_of_N (pow2N n).
  Proof.
    induction n.
    reflexivity.
    rewrite pow2N_S.
    rewrite nat_of_Nmult.
    rewrite IHn.
    reflexivity.
  Qed.

  Fixpoint pow2(n:nat):nat :=
    match n with
      | O => 1
      | S m => 2 * pow2 m
    end.

  Lemma pow2_pow2N_equiv : forall n,
    nat_of_N (pow2N n) = pow2 n.
  Proof.
    induction n.
    simpl.
    reflexivity.
    rewrite pow2N_S_nat.
    rewrite IHn.
    simpl.
    omega.
  Qed.

  Lemma pow2_S : forall n, 
    pow2 (S n) = 2*pow2 n.
  Proof.
    induction n;simpl;omega.
  Qed.

  Lemma pow2_le : forall n m,
    n <= m -> pow2 n <= pow2 m.
  Proof.
    induction 1;simpl;try omega.
  Qed.

  Lemma add_plus_nat :
    forall x y,
      (S x)* y = y + x*y.
  Proof.
    induction x;simpl;intros.
    reflexivity.
    omega.
  Qed.

  (*Transparent cart_prod.*)

  Lemma cart_prod_add_right :
    forall x x1 s,
    cart_prod {x} {x1; s} === cart_prod {x} {x1} ++ cart_prod {x} s.
  Proof.
    split;intros.
    apply cart_prod_spec in H.
    destruct H.
    apply add_iff in H0.
    destruct H0.
    apply union_2.
    apply cart_prod_spec.
    split;auto with typeclass_instances.
    rewrite H0.
    apply singleton_2;auto.
    apply union_3.
    apply cart_prod_spec.
    split;auto.
    apply union_1 in H.
    destruct H;apply cart_prod_spec in H;apply cart_prod_spec;destruct H;split;auto.
    apply add_1.
    apply singleton_1 in H0.
    assumption.
    apply add_2;auto.
  Qed.       

  Corollary map_singleton : 
    forall x0 x,
      cart_prod {x0} {x} === singleton (pair x0 x).
  Proof.
    split;intros.
    apply cart_prod_spec in H;destruct H as [H1 H2];
    apply singleton_1 in H1;apply singleton_1 in H2.
    apply singleton_2.
    destruct a;simpl in *.
    constructor;auto.
    apply singleton_1 in H;destruct a;simpl in *.
    apply cart_prod_spec;simpl;split;apply singleton_2;
    inversion H;normalize_notations;auto.
  Qed.

  Lemma cardinal_cart_prod_singleton : 
    forall s2 x,
      cardinal (cart_prod {x} s2) = cardinal s2.
  Proof.
    induction s2 using set_induction;intros.
    cut(cart_prod {x} s2 === {}).
    abstract(intros;rewrite (@Equal_cardinal _ _ _ _ _ _ H0);symmetry;rewrite cardinal_fold;
             rewrite fold_1b;eauto).
    abstract(
        split;intros;[apply cart_prod_spec in H0;destruct H0;apply H in H1;elim H1|inversion H0]).

    cut(cart_prod {x0} s2_2 === cart_prod {x0} {x;s2_1}).
    intro;
    rewrite (@Equal_cardinal _ _ _ _ _ _ H1);
    pose proof cart_prod_add_right x0 x s2_1;
    rewrite (@Equal_cardinal _ _ _ _ _ _ H2);
    rewrite map_singleton;
    apply Add_Equal in H0;
    rewrite H0;
    apply Add_Equal in H0;
    rewrite union_cardinal_inter.
    assert(inter {(x0, x)} (cart_prod {x0} s2_1) === {}) by 
    abstract(split;intros;try (now (inversion H3));
    apply inter_iff in H3;destruct H3;apply cart_prod_spec in H4;
    destruct H4;
    apply singleton_1 in H3;
    apply singleton_1 in H4;
    destruct a ;simpl in *;inversion H3;subst;rewrite <- H11 in H5;
    contradiction).
    rewrite H3, singleton_cardinal,empty_cardinal.
    simpl.
    rewrite add_cardinal_2;eauto.
    apply Add_Equal in H0;apply cart_prod_m;eauto.
  Qed.

  Lemma cart_prod_add :
    forall x s1 s2, 
      cart_prod {x;s1} s2 === cart_prod {x} s2 ++ cart_prod s1 s2.
  Proof.
    split;intros.
    apply cart_prod_spec in H.
    destruct H.
    apply add_iff in H.
    destruct H.
    apply union_2.
    apply cart_prod_spec.
    split;auto.
    apply singleton_2.
    assumption.
    apply union_3.
    apply cart_prod_spec.
    split;auto.
    apply union_iff in H;destruct H.
    apply cart_prod_spec in H.
    apply cart_prod_spec.
    destruct H.
    split;auto.
    apply add_1.
    apply singleton_1 in H.
    assumption.
    apply cart_prod_spec in H.
    apply cart_prod_spec.
    destruct H.
    split;eauto.
    apply add_2;eauto.
  Qed.

  Lemma cart_prod_empty :
    forall s1 s2, s1 === {} -> cart_prod s1 s2 === {}.
  Proof.
    split;intros.
    apply cart_prod_spec in H0.
    destruct H0.
    apply H in H0.
    abstract(inversion H0).
    abstract(inversion H0).
  Qed.

  Lemma cart_prod_card : forall s1 s2,
    cardinal (cart_prod s1 s2) = cardinal s1 * cardinal s2.
  Proof.
    induction s1 using set_induction.
    intros.
    symmetry.
    rewrite cardinal_fold.
    rewrite fold_1b;auto.
    simpl.
    apply empty_is_empty_1 in H.
    pose proof cart_prod_empty s1 s2 H.
    symmetry.
    apply empty_is_empty_2 in H0.
    rewrite cardinal_fold.
    rewrite fold_1b;auto.
    intros.
    specialize IHs1_1 with s2.
    cut(cart_prod s1_2 s2 === cart_prod {x;s1_1} s2).
    intro.
    pose proof @Equal_cardinal _ _ _ _ _ _ H1.
    rewrite H2.
    rewrite cart_prod_add.
    pose proof H0.
    apply Add_Equal in H3.
    rewrite H3.
    pose proof @add_cardinal_2 _ _ _ _ s1_1 x H. 
    rewrite H4.
    rewrite add_plus_nat.
    rewrite <- IHs1_1.
    assert((inter (cart_prod {x} s2) (cart_prod s1_1 s2)) === {}).
    split;intros.
    apply inter_iff in H5.
    destruct H5.
    apply cart_prod_spec in H5.
    destruct H5.
    apply singleton_1 in H5.
    apply cart_prod_spec in H6.
    destruct H6.
    rewrite <- H5 in H6.
    contradiction.
    inversion H5.
    rewrite union_cardinal_inter.
    rewrite H5.
    rewrite empty_cardinal.
    rewrite IHs1_1.
    rewrite cardinal_cart_prod_singleton.
    rewrite <- minus_n_O;reflexivity.
    apply Add_Equal in H0.
    apply cart_prod_m;auto.
  Qed.

  Lemma powerset_empty :
    (powerset {}) === singleton (empty).
  Proof.
    split;intros.
    apply powerset_spec in H.
    apply singleton_2.
    split;intros.
    inv H0.
    apply H;auto.
    apply singleton_1 in H.
    apply powerset_spec.
    red;intros.
    apply H in H0.
    assumption.
  Qed.

  Lemma powerset_Empty :
    forall s,
      s === {} -> powerset s === singleton empty.
  Proof.
    intros.
    split;intros.
    apply powerset_spec in H0.
    rewrite H in H0.
    apply singleton_2.
    split;intros.
    inversion H1.
    apply H0 in H1.
    assumption.

    apply singleton_1 in H0.
    apply powerset_spec.
    red;intros.
    apply H.
    rewrite <- H0 in H1.
    assumption.
  Qed.

  Transparent powerset.

  Instance add_vals_m : 
    forall x, Proper (_eq ==> Equal ==> Equal) (fun y : set A => add {x; y}).
  Proof.
    repeat red.
    split;intros.
    apply add_iff in H1;destruct H1.
    rewrite <- H1.
    rewrite H.
    apply add_1;auto.
    rewrite H0 in H1.
    apply add_2;auto.
    apply add_iff in H1;destruct H1.
    rewrite <- H1.
    rewrite H.
    apply add_1;auto.
    rewrite H0.
    apply add_2;auto.
  Qed.

  Lemma add_vals_transp : 
    forall x, transpose Equal (fun y : set A => add {x; y}).
  Proof.
    repeat red.
    split;intros.
    apply add_iff in H;destruct H.
    rewrite <- H.
    apply add_2;apply add_1;auto.
    apply add_iff in H;destruct H.
    apply add_1;auto.
    do 2 apply add_2;auto.
    apply add_iff in H;destruct H.
    rewrite <- H.
    apply add_2;apply add_1;auto.
    apply add_iff in H;destruct H.
    rewrite <- H.
    apply add_1;auto.
    do 2 apply add_2;auto.
  Qed.

  Property subset_empty :
  forall s, 
    s[<=]{} -> s === {}.
  Proof.
    induction s using set_induction;intros.
    split;intros.
    apply H0;auto.
    inversion H1.
    split;intros.
    apply H0 in H2.
    destruct H2.
    apply H1.
    apply H0.
    left;auto.
    assert(a \In s2).
    apply H0.
    right;auto.
    apply H1 in H3.
    assumption.
    inversion H2.
  Qed.

  Lemma empty_in_powerset :
    forall s, 
      {} \In powerset s.
  Proof.
    intros.
    apply powerset_spec.
    red;intros.
    inv H.
  Qed.

  Lemma add_not_empty :
    forall x s,
      {} =/= {x;s}.
  Proof.
    intros;intro.
    destruct(H x).
    assert(x \In {x;s}).
    apply add_1;auto.
    apply H1 in H2.
    inversion H2.
  Qed.

  Instance powerset_add_m : forall x, 
    Proper (_eq ==> _eq) (fun y : set A => {x; y}).
  Proof.
    repeat red;split;intros;apply add_iff in H0;destruct H0.
    rewrite <- H0;apply add_1;auto.
    apply H in H0;apply add_2;auto.
    rewrite H0;apply add_1;auto.
    rewrite H;apply add_2;auto.
  Qed.

  Instance add_one_m : Proper (_eq ==> _eq ==> _eq) add_one.
  Proof.
    repeat red.
    intros.
    split;intros.
    apply add_one_spec in H1.
    apply add_one_spec.
    rewrite H0 in H1.
    destruct H1;auto.
    right.
    destruct H1.
    exists x1.
    rewrite H0 in H1.
    rewrite H in H1.
    assumption.
    apply add_one_spec in H1.
    apply add_one_spec.
    rewrite H0.
    destruct H1;auto.
    right.
    destruct H1.
    exists x1.
    rewrite H;auto.
    rewrite H0.
    assumption.
  Qed.


  Lemma transpose_add_one : transpose equiv add_one.
  Proof.
    red;intros.
    split;intros.
    apply add_one_spec in H.
    destruct H.
    apply add_one_spec in H.
    destruct H.
    apply add_one_spec.
    left;apply add_one_spec;auto.
    destruct H as [a' [H1 H2]].
    apply add_one_spec.
    right.
    exists a';split;auto.
    apply add_one_spec;auto.
    destruct H as [a' [H1 H2]].
    eapply add_one_spec in H1.
    destruct H1.
    apply add_one_spec.
    left.
    apply add_one_spec.
    right;exists a';auto.
    destruct H as [a'' [H3 H4]].
    assert(a[=]{y;{x;a''}}).
    split;intros.
    apply H2 in H.
    rewrite H4 in H.
    apply add_iff in H.
    destruct H.
    rewrite H.
    apply add_2;apply add_1;auto.
    apply add_iff in H.
    destruct H.
    rewrite H;apply add_1;auto.
    apply add_2;apply add_2;auto.
    apply add_iff in H;destruct H.
    rewrite H2,H4.
    rewrite <- H.
    apply add_2;apply add_1;auto.
    apply add_iff in H;destruct H.
    rewrite H2.
    rewrite <- H.
    apply add_1;auto.
    rewrite H2,H4.
    apply add_2;apply add_2;auto.
    apply add_one_spec.
    right.
    exists {x;a''}.
    split;auto.
    apply add_one_spec.
    right.
    exists a'';split;auto.
    reflexivity.
    apply add_one_spec in H.
    destruct H.
    apply add_one_spec in H.
    destruct H.
    apply add_one_spec.
    left;apply add_one_spec;auto.
    destruct H as [a' [H1 H2]].
    apply add_one_spec.
    right.
    exists a';split;auto.
    apply add_one_spec;auto.
    destruct H as [a' [H1 H2]].
    eapply add_one_spec in H1.
    destruct H1.
    apply add_one_spec.
    left.
    apply add_one_spec.
    right;exists a';auto.
    destruct H as [a'' [H3 H4]].
    assert(a[=]{x;{y;a''}}).
    split;intros.
    apply H2 in H.
    rewrite H4 in H.
    apply add_iff in H.
    destruct H.
    rewrite H.
    apply add_2;apply add_1;auto.
    apply add_iff in H.
    destruct H.
    rewrite H;apply add_1;auto.
    apply add_2;apply add_2;auto.
    apply add_iff in H;destruct H.
    rewrite H2,H4.
    rewrite <- H.
    apply add_2;apply add_1;auto.
    apply add_iff in H;destruct H.
    rewrite H2.
    rewrite <- H.
    apply add_1;auto.
    rewrite H2,H4.
    apply add_2;apply add_2;auto.
    apply add_one_spec.
    right.
    exists {y;a''}.
    split;auto.
    apply add_one_spec.
    right.
    exists a'';split;auto.
    reflexivity.
  Qed.

  Lemma powerset_step :
    forall s2 s1 x,
      ~x \In s1 ->
      Add x s1 s2 ->
      powerset s2 === powerset s1 ++ map (fun y => add x y) (powerset s1).
  Proof.
    intros.
    unfold powerset.
    rewrite (@fold_2 A AOrd _ _ s1 s2 x);auto with typeclass_instances.
    split;intros.
    apply add_one_spec in H1.
    destruct H1.
    apply union_2;auto.
    apply union_3.
    apply map_spec;auto with typeclass_instances.
    apply union_iff in H1;destruct H1.
    apply add_one_spec.
    left;auto.
    apply add_one_spec.
    apply map_iff in H1;auto with typeclass_instances.
    unfold equiv;auto with typeclass_instances.
    apply transpose_add_one.
  Qed.

  Lemma map_add : forall s s' x,
                    s' \In (map (fun y : set A => {x; y}) s) <->
                      x \In s' /\ (s' \In s \/ (remove x s') \In  s).
  Proof.
    intros.
    split;intros.
    apply map_iff in H;auto with typeclass_instances.
    destruct H.
    destruct H.
    split.
    rewrite H0.
    apply add_1;auto.
    destruct(In_dec x x0).
    rewrite add_equal in H0;auto.
    left.
    rewrite H0.
    assumption.
    right.
    rewrite H0.
    pose proof @remove_add _ _ _ _ x0 x n.
    rewrite H1.
    assumption.

    destruct H.
    destruct H0.
    apply map_iff;auto with typeclass_instances.
    exists s'.
    split.
    assumption.
    rewrite add_equal;auto.
    apply map_iff;auto with typeclass_instances.
    exists (remove x s').
    split;auto.
    split;intros.
    destruct(eq_dec x a).
    rewrite <- H2.
    apply add_1;auto.
    apply add_2.
    apply remove_iff.
    split;auto.
    apply add_iff in H1.
    destruct H1.
    rewrite <- H1;auto.
    apply remove_iff in H1.
    destruct H1;auto.
  Qed.
 
  Transparent map.

  Lemma powerset_cardinal : forall s,
    cardinal (powerset s) = pow2 (cardinal s).
  Proof.
    induction s using set_induction;intros.
   
    symmetry ; rewrite cardinal_fold.
    rewrite fold_1b;auto.
    simpl.
    pose proof powerset_empty.
    apply Equal_cardinal in H0.
    assert(powerset s === powerset {}).
    apply empty_is_empty_1 in H.
    split;intros.
    apply powerset_spec.
    apply powerset_spec in H1.
    red;intros.
    apply H1 in H2.
    apply H in H2.
    assumption.
    apply powerset_spec in H1.
    apply powerset_spec.
    rewrite <- H in H1.
    assumption.
    apply Equal_cardinal in H1.
    rewrite H1.
    rewrite H0.
    vm_compute.
    reflexivity.

    pose proof powerset_step _ _ _ H H0.
    rewrite H1.
    rewrite union_cardinal.
    rewrite map_cardinal;auto with typeclass_instances.
    rewrite IHs1.
    rewrite (cardinal_2 H H0).
    simpl;auto with arith.
    intros u v.
    rewrite 2 powerset_spec.
    red;red;intros.
    simpl.
    red.
    intro.
    red.
    generalize (H4 a) (H2 a) (H3 a).
    set_iff.
    clear H2 H3 H4.
    intuition;auto with sets. 
    rewrite <- H7 in H9;apply H in H9;elim H9.
    rewrite <- H7 in H9;apply H in H9;elim H9.
    rewrite <- H8 in H9;apply H in H9;elim H9.    
    rewrite <- H8 in H9;apply H in H9;elim H9.
    intros u (X,Y).
    apply powerset_spec in X.
    rewrite map_add in Y.
    destruct Y as (Y,_).
    apply X in Y.
    contradiction.
  Qed.

  (* Definition of the well_founded relation *)
  (*Definition lex (MAX:nat) := (lexprod (set A) (fun _:set A => set A)
    (lim_card MAX) (fun _:set A => dec_H)). 


  Lemma lex_wf : forall M:nat, well_founded (lex M).
  Proof.
    intro.
    apply wf_lexprod.
    apply lim_card_wf.
    intro.
    apply dec_H_wf.
  Defined.*)

End LIM_CARD.


