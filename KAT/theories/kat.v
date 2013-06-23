Require Export kat_alph atoms gs gl.

Module KAT(X:KAT_Alph).

  Import X.
  Module Export M := GL(X).

  (** * Syntax of KAT terms *)
  
  Inductive kat : Type :=
  | kats : Z-> kat
  | katb : test -> kat
  | katu : kat -> kat -> kat
  | katc : kat -> kat -> kat
  | katst : kat -> kat.

  Notation "[ b ]?" := (katb b).
  Notation "` x" := (kats x)(at level 10).
  Notation "x + y" := (katu x y).
  Notation "x * y" := (katc x y).
  Notation "x #" := (katst x)(at level 11).

  Coercion katb : test >-> kat.

  Inductive kat_eq : kat -> kat -> Prop :=
    kat_eq_kats : forall x1 y1 : Z, x1 === y1 -> kat_eq (` x1) (` y1)
  | kat_eq_katb : forall x1 y1 : test,
                  x1 === y1 -> kat_eq ([x1]?) ([y1]?)
  | kat_eq_katu : forall x1 y1 x2 y2 : kat,
                  kat_eq x1 y1 -> kat_eq x2 y2 -> kat_eq (x1 + x2) (y1 + y2)
  | kat_eq_katc : forall x1 y1 x2 y2 : kat,
                  kat_eq x1 y1 -> kat_eq x2 y2 -> kat_eq (x1 * x2) (y1 * y2)
  | kat_eq_katst : forall x1 y1 : kat, kat_eq x1 y1 -> kat_eq (x1 #) (y1 #).

  (** [kat] as an ordered type *)

  Proposition kat_eq_leibniz:
    forall x y:kat, kat_eq x y -> x = y.
  Proof.
    induction 1;intros;try (subst;auto).
    - inv H.
    - apply leibniz_test in H; rewrite H;auto.
  Qed.

  Lemma kat_eq_inj_args :
    forall x₁ x₂ y₁ y₂, kat_eq (katc x₁ y₁) (katc x₂ y₂) ->
                        x₁ = x₂ /\ y₁ = y₂.
  Proof.
    intros. apply kat_eq_leibniz in H;injection H;auto.
  Qed.

  Global Instance test_eq_refl : Reflexive kat_eq.
  Proof.
    repeat red;intros;induction x;try constructor;auto.
  Qed.

  Global Instance test_eq_symm : Symmetric kat_eq.
  Proof.
    repeat red.
    induction 1;try reflexivity.
    - constructor;auto. 
    - constructor;auto.
    - constructor;auto.
    - constructor;auto.
    - constructor;auto.
  Qed.

  Global Instance test_eq_trans : Transitive kat_eq.
  Proof.
    repeat red.
    induction x;intros.
    - inv H.
    - apply kat_eq_leibniz in H.  rewrite H. assumption. 
    - inv H;subst. inv H0;subst. constructor;eauto.
    - inv H;subst. inv H0;subst. constructor;eauto.
    - inv H;subst;inv H0;subst. constructor;eauto.
  Qed.

  Global Instance test_eq_Equiv : Equivalence test_eq.
  Proof.
    constructor;autotc.
  Qed.
 
  Inductive kat_lt : kat -> kat -> Prop :=
    kat_lt_kats_1 : forall x1 y1 : Z, x1 <<< y1 -> kat_lt (`x1) (`y1)
  | kat_lt_kats_katb : forall (x1 : Z) (y1 : test), kat_lt (`x1) ([y1]?)
  | kat_lt_kats_katu : forall (x1 : Z) (y1 y2 : kat),
                       kat_lt (`x1) (y1 + y2)
  | kat_lt_kats_katc : forall (x1 : Z) (y1 y2 : kat),
                       kat_lt (`x1) (y1 * y2)
  | kat_lt_kats_katst : forall (x1 : Z) (y1 : kat), kat_lt (`x1) (y1 #)
  | kat_lt_katb_1 : forall x1 y1 : test,
                    x1 <<< y1 -> kat_lt ([x1]?) ([y1]?)
  | kat_lt_katb_katu : forall (x1 : test) (y1 y2 : kat),
                       kat_lt ([x1]?) (y1 + y2)
  | kat_lt_katb_katc : forall (x1 : test) (y1 y2 : kat),
                       kat_lt ([x1]?) (y1 * y2)
  | kat_lt_katb_katst : forall (x1 : test) (y1 : kat),
                        kat_lt ([x1]?) (y1 #)
  | kat_lt_katu_1 : forall x1 y1 x2 y2 : kat,
                    kat_lt x1 y1 -> kat_lt (x1 + x2) (y1 + y2)
  | kat_lt_katu_2 : forall x1 y1 x2 y2 : kat,
                    kat_eq x1 y1 ->
                    kat_lt x2 y2 -> kat_lt (x1 + x2) (y1 + y2)
  | kat_lt_katu_katc : forall x1 x2 y1 y2 : kat, kat_lt (x1 + x2) (y1 * y2)
  | kat_lt_katu_katst : forall x1 x2 y1 : kat, kat_lt (x1 + x2) (y1 #)
  | kat_lt_katc_1 : forall x1 y1 x2 y2 : kat,
                    kat_lt x1 y1 -> kat_lt (x1 * x2) (y1 * y2)
  | kat_lt_katc_2 : forall x1 y1 x2 y2 : kat,
                    kat_eq x1 y1 ->
                    kat_lt x2 y2 -> kat_lt (x1 * x2) (y1 * y2)
  | kat_lt_katc_katst : forall x1 x2 y1 : kat, kat_lt (x1 * x2) (y1 #)
  | kat_lt_katst_1 : forall x1 y1 : kat, kat_lt x1 y1 -> kat_lt (x1 #) (y1 #).

  Global Instance kat_lt_trans : Transitive kat_lt.
  Proof.
    repeat red.
    induction x;intros.
    - inv H;subst;try (inv H0;subst;try (now constructor)). 
      constructor. order.
    - inv H;subst;try (inv H0;subst;try (now constructor)). 
      constructor. order.
    - inv H;subst. 
      + inv H0;subst;try (now constructor). 
        * constructor. eapply IHx1;eauto.
        * apply kat_eq_leibniz in H3;subst. constructor;auto.
      + apply kat_eq_leibniz in H3;subst. inv H0;try (now constructor). subst.
        apply kat_eq_leibniz in H3;subst. apply kat_lt_katu_2. reflexivity. order. 
      + inv H0;subst;now constructor.
      + inv H0;subst;now constructor.
    - inv H;subst;try (now constructor).
      + inv H0;subst.
        * constructor;order.
        * apply kat_eq_leibniz in H3;subst. constructor;auto.
        * constructor.
      + apply kat_eq_leibniz in H3;subst. inv H0;subst.
        * constructor;auto.
        * apply kat_eq_leibniz in H3. subst. apply kat_lt_katc_2. reflexivity. order.
        * constructor.
      + inv H0. constructor.
    - inv H;subst. inv H0;subst. constructor;order.
  Qed.

  Global Instance kat_lt_string : StrictOrder kat_lt eq.
  Proof.
    constructor;autotc.
    induction 1;intro;try discriminate;try (now inv H0). 
    - inv H0. subst. order.
    - inv H0. subst. order.
  Qed.

  Fixpoint kat_cmp (x y : kat) : comparison :=
    match x with
      | `x1 =>
        match y with
          | `y1 => compare x1 y1
          | katb _ => Lt
          | _ + _ => Lt
          | _ * _ => Lt
          | _ # => Lt
        end
      | katb x1 =>
        match y with
          | `_ => Gt
          | katb y1 => compare x1 y1
          | _ + _ => Lt
          | _ * _ => Lt
          | _ # => Lt
        end
      | x1 + x2 =>
        match y with
          | ` _ => Gt
          | katb _ => Gt
          | y1 + y2 =>
            match kat_cmp x1 y1 with
              | Eq => kat_cmp x2 y2
              | Lt => Lt
              | Gt => Gt
            end
          | _ * _ => Lt
          | _ # => Lt
        end
      | x1 * x2 =>
        match y with
          | ` _ => Gt
          | katb _ => Gt
          | _ + _ => Gt
          | y1 * y2 =>
            match kat_cmp x1 y1 with
              | Eq => kat_cmp x2 y2
              | Lt => Lt
              | Gt => Gt
            end
          | _ # => Lt
        end
      | x1 # =>
        match y with
          | ` _ => Gt
          | katb _ => Gt
          | _ + _ => Gt
          | _ * _ => Gt
          | y1 # => kat_cmp x1 y1
        end
    end.
  
  (* begin hide *)
  Functional Scheme kat_cmp_ind := Induction for kat_cmp Sort Prop.
  Functional Scheme kat_cmp_rec := Induction for kat_cmp Sort Set.
  (* end hide *)

  Lemma kat_cmp_eq : 
    forall x y, kat_cmp x y = Eq -> x = y.
  Proof.
    intros.
    functional induction (kat_cmp x y);try discriminate.
    - apply compare_2 in H. inv H.
    - apply compare_2 in H. inv H.
    - apply IHc in e1; apply IHc0 in H. subst. auto.
    - apply IHc in e1; apply IHc0 in H. subst. auto.
    - apply IHc in H. subst. auto.
  Qed.

  Lemma kat_cmp_lt : 
    forall x y, kat_cmp x y = Lt -> kat_lt x y.
  Proof.
    intros.
    functional induction (kat_cmp x y);try discriminate;try (now constructor).
    - constructor. apply compare_1 in H. auto.
    - apply kat_lt_katu_2. apply kat_cmp_eq in e1. subst. reflexivity. apply IHc0;auto. 
    - constructor;eauto.
    - apply kat_cmp_eq in e1. subst. apply kat_lt_katc_2. reflexivity. eauto.
    - constructor;eauto.
    - constructor;eauto.
  Qed.

  Lemma kat_cmp_gt : 
    forall x y, kat_cmp x y = Gt -> kat_lt y x.
  Proof.
    intros.
    functional induction (kat_cmp x y);try discriminate;try (now constructor).
    - constructor. apply compare_3 in H. auto.
    - apply compare_3 in H. constructor. assumption. 
    - apply kat_lt_katu_2. apply kat_cmp_eq in e1. subst. reflexivity. apply IHc0;auto. 
    - constructor;eauto.
    - apply kat_cmp_eq in e1. subst. apply kat_lt_katc_2. reflexivity. eauto.
    - constructor;eauto.
    - constructor;eauto.
  Qed.
  
  Global Instance katOrd : UsualOrderedType kat :=
  {
    SOT_lt := kat_lt ; SOT_cmp := kat_cmp
  }.
  Proof.
    intros.
    case_eq(kat_cmp x y);intros;constructor.
    - apply kat_cmp_eq;auto.
    - apply kat_cmp_lt;auto.
    - apply kat_cmp_gt;auto.
  Defined.

  (** The guarded language of a kat term [t]. *)

  Fixpoint kat2gl(t:kat) : gl :=
    match t with
      | kats x => gl_sy x
      | katb b => gl_atom b
      | katu t1 t2 => gl_union (kat2gl t1) (kat2gl t2)
      | katc t1 t2 => gl_conc (kat2gl t1) (kat2gl t2)
      | katst t1 => gl_star (kat2gl t1)
    end.

  Coercion kat2gl : kat >-> gl.

  Instance kat2gl_m : Proper(_eq ==> gl_eq) kat2gl.
  Proof.
    repeat red.
    intros.
    inv H.
    split;red;auto.
  Qed.

  (** * Results on sets of KAT expressions. Includes special concatenation to
        be used in partial derivatives of KAT terms. *)

  Open Scope set_scope.

  Definition fold_conc := 
    fun s r => (map (fun x => katc x r)) s.

  Global Transparent map.

  Instance right_prod :
    forall x0,
      Proper (_eq ==> _eq) (fun x2 : kat => katc x2 x0).
  Proof.
    intros.
    unfold Proper.
    red.
    intros.
    
    repeat red;intros.
    f_equal.
    simpl. inv H.
  Qed.

  Instance fold_conc_proper :
    forall x0,
      Proper (_eq ==> Equal ==> Equal)
             (fun (a : kat) (acc : set kat) => {katc a x0; acc}).
  Proof.
    repeat red;split;intros.
    inv H.
    subst.
    apply add_iff in H1.
    destruct H1.
    apply add_1;auto.
    rewrite <- H0.
    apply add_2;auto.
    inv H.
    subst.
    normalize_notations.
    apply add_iff in H1.
    destruct H1.
    apply add_1;auto.
    apply add_2;rewrite H0;auto.
  Qed.

  Lemma fold_conc_transpose :forall x0,
    transpose Equal (fun (a : kat) (acc : set kat) => {katc a x0; acc}).
  Proof.
    unfold transpose;
    split;intros;
    apply add_iff in H;
    destruct H;
      (try now (apply add_2;
        apply add_1;
          symmetry;auto));
    apply add_iff in H;
    destruct H;
      (try now (apply add_1;symmetry;auto));
      now (do 2 apply add_2;auto).
  Qed.

  Global Instance fold_conc_m : Proper (Equal ==> _eq ==> Equal) fold_conc.
  Proof.
    do 3 red;unfold fold_conc.
    induction x using set_induction;intros.
    unfold map.
    assert(Empty y).
    rewrite <- H0;assumption.
    rewrite fold_1b;auto.
    rewrite fold_1b;auto.
    reflexivity.
    unfold map.
    rewrite (@fold_2 kat _ _ _ x1 x2 x3
              _ _ Equal_ST _ _
              (fold_conc_proper x) (fold_conc_transpose x) H H0).
    assert(SetProperties.Add x3 x1 y).
    apply Add_Equal.
    apply Add_Equal in H0.
    rewrite <- H0;symmetry;auto.
    rewrite (@fold_2 kat _ _ _ x1 y x3
              _ _ Equal_ST _ _
              (fold_conc_proper y0) (fold_conc_transpose y0) H H3).
    apply add_m.
    normalize_notations.
    inv H2.
    unfold map in IHx1.
    eapply IHx1.
    reflexivity.
    assumption.
  Qed.

  Lemma fold_conc_empty : forall r:kat, 
    fold_conc {} r === {}.
  Proof. 
    unfold fold_conc.
    vm_compute;auto.
  Qed.
  
  Lemma fold_conc_singleton : 
    forall x r, 
      (fold_conc (singleton x) r) === singleton (katc x r).
  Proof. 
    intros.
    vm_compute;auto. 
  Qed.

  Instance fold_conc_proper_equal : forall r, Proper (_eq ==> Equal ==> Equal)
    (fun (a : kat) (acc : set kat) => {katc a r; acc}).
  Proof.
    repeat red;split;intros;
    apply add_iff in H1;
    destruct H1.
    rewrite <- H1.
    apply add_1.
    normalize_notations.
    inv H;subst.
    apply add_2.
    rewrite <- H0;auto.
    
    rewrite <- H1.
    apply add_1.
    inv H;subst.
    apply add_2.
    rewrite H0;auto.
  Qed.
  
  Lemma fold_conc_trans_equal : forall r, 
    transpose Equal (fun (a : kat) (acc : set kat) => {katc a r; acc}).
  Proof.
    repeat red;intros.
    split;intros;auto with typeclass_instances sets.
    apply add_iff in H.
    destruct H.
    apply add_2.
    apply add_1.
    assumption.
    apply add_iff in H.
    destruct H.
    apply add_1;auto.
    apply add_2.
    apply add_2;auto.
    apply add_iff in H.
    destruct H.
    apply add_2;apply add_1;auto.
    apply add_iff in H.
    destruct H.
    apply add_1;auto.
    do 2 apply add_2.
    assumption.
  Qed.
  
  (* Introduction of element in dsr/dsl *)
  Lemma elem_conc_in_fold_conc : forall s x r, 
    x \In s -> (katc x r) \In (fold_conc s r).
  Proof.
    induction s using set_induction.
    intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    inversion H0.
    intros.
    unfold fold_conc.
    eapply map_spec;auto with typeclass_instances.
    exists x0.
    split;auto.
  Qed.

 Lemma elem_conc_fold_conc_in : forall s x r, 
    (katc x r) \In (fold_conc s r) -> x \In s.
  Proof.
    induction s using set_induction.
    intros.
    unfold fold_conc,map in H0;rewrite fold_1b in H0;
      auto.
    inversion H0.

    intros.
    unfold fold_conc,map in H1.
    generalize(@fold_2 kat _ _ _ s1 s2 x 
              _ _ Equal_ST {}%set  _
              (fold_conc_proper _) (fold_conc_transpose r) H H0).
    intro.
    rewrite H2 in H1.
    clear H2.
    apply add_iff in H1.
    destruct H1.
    inversion H1.
    subst.
    apply H0;auto.
    eapply IHs1 in H1.
    apply H0;auto.
  Qed.

  Lemma elem_conc_nin_dsr : forall s x r, 
    ~(x \In s) -> ~((katc x r) \In (fold_conc s r)).
  Proof.
    induction s using set_induction;intros.
    intro.
    eapply elem_conc_fold_conc_in in H1.
    contradiction.
    apply IHs1 with (r:=r) in H.
    intro.
    apply H1.
    apply elem_conc_fold_conc_in in H2.
    contradiction.
  Qed.

  Lemma elem_conc_dsr_nin : forall s x r,
    ~(katc x r) \In (fold_conc s r) ->
    ~x \In s.
  Proof.
    induction s using set_induction;intros.
    intro;apply H0.
    apply empty_is_empty_1 in H.
    rewrite H in H1.
    inversion H1.
    intro.
    apply H1.
    apply elem_conc_in_fold_conc.
    assumption.
  Qed.

   Lemma elem_conc_in_ex : forall s x r,
    x \In (fold_conc s r) -> exists y, y \In s /\ x === katc y r.
  Proof.
    intros.
    apply map_spec in H;auto with typeclass_instances.
  Qed.

   Lemma elem_conc_nin_ex : forall s x r,
    ~x \In (fold_conc s r) -> ~exists y, y \In s /\ x === katc y r.
  Proof.
    induction s using set_induction;intros.
    intro.
    destruct H1 as [y [H11 H12]].
    rewrite H12 in H0.
    apply H0.
    apply elem_conc_in_fold_conc.
    assumption.
    intro.
    destruct H2 as [y [H11 H12]].
    rewrite H12 in H1.
    apply H1.
    apply elem_conc_dsr_nin with (r:=r) in H1.
    contradiction.
  Qed.

  Lemma elem_conc_ex_nin : forall s x r,
    ~x \In s -> ~exists y, (katc y r) \In (fold_conc s r) /\ x === y.
  Proof.
    induction s using set_induction;intros.
    apply elem_conc_nin_dsr with (r:=r) in H0.
    intro.
    destruct H1 as [y [H11 H12]].
    unfold fold_conc in H11.
    eapply map_2 in H11;auto with typeclass_instances.
    destruct  H11.
    destruct H1.
    apply empty_is_empty_1 in H.
    rewrite H in H1.
    inversion H1.
    
    
    apply elem_conc_nin_dsr with (r:=r) in H1.
    intro.
    destruct H2 as [y [H11 H12]].
    apply H1;revert H11.
    apply In_m;try reflexivity.
    normalize_notations.
    inv H12;subst.
  Qed.

  Lemma fold_conc_add : forall s r x x0,
    x \In (fold_conc (add x0 s) r) -> x \In (add (katc x0 r) (fold_conc s r)).
  Proof.
    induction s using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0 |- *.
    rewrite fold_conc_empty.
    rewrite <- singleton_equal_add in H0 |- *.
    rewrite fold_conc_singleton in H0.
    assumption.
    apply  elem_conc_in_ex in H1.
    destruct H1 as [y [H11 H12]].
    
    generalize(@fold_2 kat _ _ _ s1 s2 x 
      _ _ Equal_ST {}%set  _
        (fold_conc_proper _) (fold_conc_transpose r) H H0).
    intro.
    unfold fold_conc,map.
    rewrite H1.
    
    apply add_iff in H11.
    rewrite H12.
    destruct H11.
    apply add_1.
    inv H2;subst;auto.
    
    apply add_2.
    
    apply elem_conc_in_fold_conc with (r:=r) in H2.
    unfold fold_conc,map in H2.
    rewrite H1 in H2.
    assumption.
  Qed.

  Lemma fold_add_conc : forall s r x x0,
    x \In (add (katc x0 r)  (fold_conc s r)) -> x \In (fold_conc (add x0 s) r).
  Proof.
    induction s using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0 |- *.
    rewrite fold_conc_empty in H0.
    rewrite <- singleton_equal_add in H0 |- *.
    rewrite fold_conc_singleton.
    assumption.
    apply add_iff in H1.
    generalize(@fold_2 kat _ _ _ s1 s2 x 
      _ _ Equal_ST {}%set  _
        (fold_conc_proper _) (fold_conc_transpose r) H H0).
    intro.
    destruct H1.
    rewrite <- H1.
    apply elem_conc_in_fold_conc.
    apply add_1.
    reflexivity.
    unfold fold_conc,map in H1.
    apply H2 in H1.
    clear H2.
    apply IHs1 in H1.
    apply elem_conc_in_ex with (r:=r) in H1.
    destruct H1 as [y [H11 H12]].
    rewrite H12.
    apply elem_conc_in_fold_conc with (r:=r).
    apply add_iff in H11.
    destruct H11.
    rewrite <- H1.
    apply add_2.
    apply H0;auto.
    apply add_2.
    apply H0;auto.
  Qed.

   Lemma fold_conc_add_eq : forall s r x, 
    (fold_conc (add x s) r) === (add (katc x r) (fold_conc s r)).
  Proof.
    intros.
    split;intros.
    apply fold_conc_add;auto.
    apply fold_add_conc;auto.
  Qed.

  Lemma fold_conc_union : forall x y r a,
    a \In (fold_conc (x++y) r) -> a \In ((fold_conc x r)++(fold_conc y r)).
  Proof.
    induction x using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0 |- *.
    rewrite fold_conc_empty.
    apply union_3.
    rewrite empty_union_1 in H0;auto.
    vm_compute.
    intros.
    inversion x1.

    apply Add_Equal in H0.
    rewrite H0 in H1.
    rewrite union_add in H1.
    apply fold_conc_add in H1.
    rewrite H0.
    apply add_iff in H1.
    destruct H1.
    apply union_2.
    apply fold_add_conc.
    rewrite <- H1.
    apply add_1.
    constructor;auto.
    normalize_notations;order.
    normalize_notations;order.
    apply IHx1 in H1.
    apply union_iff in H1.
    destruct H1.
    apply union_2.
    apply fold_add_conc.
    apply add_2;auto.
    apply union_3.
    assumption.
  Qed.

   Lemma fold_union_conc : forall x y r a,
    a \In ((fold_conc x r)++(fold_conc y r)) -> a \In (fold_conc (x++y) r).
  Proof.
    induction x using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0 |- *.
    rewrite fold_conc_empty in H0.
    rewrite empty_union_1 in H0.
    vm_compute;assumption.
    vm_compute;intros.
    inversion x1.

    apply Add_Equal in H0.
    rewrite H0.
    rewrite union_add.
    apply fold_add_conc.
    apply union_iff in H1.
    rewrite H0 in H1.
    destruct H1.
    apply fold_conc_add in H1.
    apply add_iff in H1.
    destruct H1.
    rewrite <- H1.
    apply add_1.
    constructor;normalize_notations;auto.

    apply add_2.
    apply IHx1.
    apply union_2.
    assumption.

    apply add_2.
    apply IHx1.
    apply union_3.
    assumption.
  Qed.

  Lemma fold_conc_card : forall s r,
    cardinal (fold_conc s r) = cardinal s.
  Proof.
    induction s using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H.
    rewrite fold_conc_empty.
    reflexivity.

    generalize(@fold_2 kat _ _ _ s1 s2 x 
      _ _ Equal_ST {}%set  _
        (fold_conc_proper _) (fold_conc_transpose r) H H0);intro.
    unfold fold_conc,map.
    rewrite H1.
    apply Add_Equal in H0.
    rewrite H0.
    rewrite add_cardinal_2.
    rewrite add_cardinal_2;try assumption.
    unfold fold_conc,map in IHs1.
    rewrite IHs1.
    abstract omega.
    apply elem_conc_nin_dsr with (r:=r) in H.
    assumption.
  Qed.

  Definition dsr (s:set kat)(r:kat): set kat := 
    match r with
      | katb ba0 => {}%set
      | katb ba1 => s
      | _ => fold_conc s r
    end.

   Notation "x [.] y" := (dsr x y)(at level 60).

   (*Hint Unfold dsr.*)

   (* Their functional inductive principles *)
   Functional Scheme dsr_ind := Induction for dsr Sort Prop.
   Functional Scheme dsr_rec := Induction for dsr Sort Set.

   Lemma dsr_re0 : forall s, (s [.] (katb ba0))==={}%set.
   Proof.
     intro;simpl;reflexivity.
   Qed.
    
   Lemma dsr_empty : forall r, ({}[.]r)==={}%set.
   Proof.
     induction r;simpl;
     try now(rewrite fold_conc_empty;reflexivity).
     destruct t;
       first [reflexivity | rewrite fold_conc_empty].
   Qed.

  Definition Not_0_1 (r:kat) := ~r === (katb ba0) /\ ~r === (katb ba1).
  Hint Unfold Not_0_1.

  Lemma dsr_singleton : forall x r, Not_0_1 r ->
    ({x}%set [.] r)=== {katc x  r}%set.
  Proof.
    induction r;simpl;intros;
    try (rewrite fold_conc_singleton);auto.
    destruct t;
      try rewrite fold_conc_singleton;auto.
    destruct H.
    elim H;auto.
    destruct H.
    elim H0;auto.
  Qed.

  Add Morphism dsr : dsr_mor.
  Proof.
    unfold dsr.
    intros.
    inv H0;subst. clear H0.
    induction y0.
    apply fold_conc_m. auto.
    reflexivity.
    destruct t;try (apply fold_conc_m);auto.
    reflexivity.
    apply fold_conc_m;auto.
    apply fold_conc_m;auto.
    apply fold_conc_m;auto.
  Qed.

  Lemma dsr_cases : forall s r,
    (s[.]r)==={}%set \/ (s[.]r)===s \/ (Not_0_1 r /\ (s[.]r)===(fold_conc s r)).
  Proof.
    destruct r.
    - right;right.
      split;auto.
      red;split;intro;
      inversion H.
    - case_eq t;intros;auto;
      try (right;right;split;auto);
      try now(red;split;intro;apply leibniz_kat in H;
              discriminate).
      red;split;intro. inv H0. inv H0.
      red;split;intro. inv H0. inv H0.
      red;split;intro. inv H0. inv H0.
      red;split;intro. inv H0. inv H0.
    - right;right. split.
      red;split;intro. inv H. inv H.
      unfold dsr;auto.
    - right;right;split;red;split;intro.
      inv H. inv H. unfold dsr in H. auto.
      unfold dsr;auto.
    - right;right;split;red;split;intro.
      inv H. inv H. unfold dsr in H. auto.
      unfold dsr;auto.
  Qed.
  
  Lemma elem_conc_dsr_in : forall s x r,
    Not_0_1 r -> x \In s -> (katc x r) \In (s[.]r).
  Proof.
    induction r;intros;try (unfold Not_0_1 in H;intuition);
      unfold dsr;
      try (now (apply elem_conc_in_fold_conc;
          assumption)).
    destruct t.
    elim H1;auto.
    elim H2;auto.
    apply elem_conc_in_fold_conc;assumption.
    apply elem_conc_in_fold_conc;assumption.
    apply elem_conc_in_fold_conc;assumption.
    apply elem_conc_in_fold_conc;assumption.
  Qed.

  Lemma elem_conc_in_dsr : forall s x r,
    Not_0_1 r -> (katc x r) \In (s[.]r) -> x \In s.
  Proof.
    induction r;intros;try (unfold Not_0_1 in H;intuition).
    eapply elem_conc_fold_conc_in in H0;assumption.
    destruct t.
    simpl in H0.
    inversion H0.
    elim H2;auto.
    eapply elem_conc_fold_conc_in in H0;assumption.
    eapply elem_conc_fold_conc_in in H0;assumption.
    eapply elem_conc_fold_conc_in in H0;assumption.
    eapply elem_conc_fold_conc_in in H0;assumption.
    eapply elem_conc_fold_conc_in in H0;assumption.
    eapply elem_conc_fold_conc_in in H0;assumption.
    eapply elem_conc_fold_conc_in in H0;assumption.
  Qed.

  Lemma dsr_add : forall s x r,
    Not_0_1 r -> (({x;s})[.]r)===(add (katc x r) (s[.]r)).
  Proof.
    induction s using set_induction;intros.
    split;intro;
      apply empty_is_empty_1 in H;
        rewrite H in H1;
          rewrite H.
    rewrite dsr_empty.
    rewrite <- singleton_equal_add in H1 |- *.
    rewrite dsr_singleton in H1;
      assumption.
    rewrite dsr_empty in H1.
    rewrite <- singleton_equal_add in H1 |- *.
    rewrite dsr_singleton;
      assumption.
    functional induction (dsr s2 r);simpl.
    split;intro.
    apply fold_conc_add in H2.
    assumption.
    apply fold_add_conc in H2.
    assumption.
    destruct H1.
    elim H1;auto.
    destruct H1.
    elim H2;auto.
    split;intro.
    apply fold_conc_add in H2.
    assumption.
    apply fold_add_conc in H2.
    assumption.
    split;intro.
    apply Add_Equal in H0.
    apply fold_conc_add.
    assumption.
    apply add_iff in H2.
    destruct H2.
    rewrite <- H2.
    apply elem_conc_in_fold_conc.
    apply add_1;auto.
    apply fold_add_conc.
    apply add_2;
      auto.
    split;intro.
    apply fold_conc_add in H2.
    assumption.
    apply fold_add_conc.
    assumption.
    split;intros.
    apply fold_conc_add in H2.
    assumption.
    apply fold_add_conc in H2.
    assumption.
    split;intros.
    apply fold_conc_add in H2.
    assumption.
    apply fold_add_conc in H2.
    assumption.
    split;intros.
    apply fold_conc_add in H2.
    assumption.
    apply fold_add_conc in H2.
    assumption.
    split;intros.
    apply fold_conc_add in H2.
    assumption.
    apply fold_add_conc in H2.
    assumption.
  Qed.

  Lemma dsr_empty_res : forall s r, Empty (s[.]r) -> Empty s \/ r === ba0.
  Proof.
    induction s using set_induction;intros.
    left;auto.
    apply Add_Equal in H0.
    rewrite H0 in H1 |- *.
    apply empty_is_empty_1 in H1.
    destruct(eq_dec r ba0);auto.
    destruct(eq_dec r ba1);auto.
    apply empty_is_empty_2 in H1.
    elim (H1 (katc x r));auto.
    rewrite H3 in H1.
    simpl in H1.
    elim (H1 x).
    apply add_1.
    reflexivity.

    left.
    apply empty_is_empty_2 in H1.
    elim H1 with (a:=(katc x r)).
    apply elem_conc_dsr_in.
    red;auto.
    apply add_1;auto.
  Qed.

  Lemma dsr_union : forall s x r,
    ((x++s)[.]r)===((x[.]r)++(s[.]r)).
  Proof.
    induction x using set_induction;intros.
    split;intro.
    apply empty_is_empty_1 in H.
    rewrite H.
    rewrite H in H0.
    rewrite dsr_empty.
    apply union_3.
    rewrite empty_union_1 in H0;auto.
    vm_compute.
    intros.
    inversion x1.
    apply union_iff in H0.
    destruct H0.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    apply dsr_empty in H0.
    inversion H0.
    generalize H;intro Hx;apply empty_is_empty_1 in H.
    rewrite H.
    rewrite empty_union_1;auto.
    vm_compute;intros.
    inversion x1.
    
    functional induction (dsr x2 r).
    simpl.
    split;intros.
    apply fold_conc_union in H1.
    assumption.
    apply fold_union_conc.
    assumption.

    simpl;rewrite empty_union_1;auto.
    red;intros;intro;inversion H1.
    
    simpl;reflexivity.

    simpl;split;intros;
    [apply fold_conc_union in H1|apply fold_union_conc];
    assumption.

    simpl;split;intros;
    [apply fold_conc_union in H1|apply fold_union_conc];
    assumption.
    
    simpl;split;intros;
    [apply fold_conc_union in H1|apply fold_union_conc];
    assumption.

    simpl;split;intros;
    [apply fold_conc_union in H1|apply fold_union_conc];
    assumption.

    simpl;split;intros;
    [apply fold_conc_union in H1|apply fold_union_conc];
    assumption.

    simpl;split;intros;
    [apply fold_conc_union in H1|apply fold_union_conc];
    assumption.

    simpl;split;intros;
    [apply fold_conc_union in H1|apply fold_union_conc];
    assumption.
  Qed.

  Lemma dsr_not_empty : forall s (r:kat), 
    ~Empty s -> r =/= ba0 -> ~Empty (s[.]r).
  Proof.
    intros.
    intro.
    apply dsr_empty_res in H1.
    destruct H1;
    contradiction.
  Qed.

  (** Some counter-example based lemmas *)
  Lemma in_dsr_re0 : forall s, 
    ~exists x, x \In (s[.]ba0).
  Proof.
    intros s H.
    destruct H.
    rewrite dsr_re0 in H.
    inversion H.
  Qed.

  Lemma in_dsr_re_sy : forall s a x, 
    x \In (s[.]kats a) -> 
    exists y, x === katc y (kats a) /\ y \In s.
  Proof.
    intros.
    simpl in H.
    apply elem_conc_in_ex in H.
    destruct H as [y [H11 H12] ].
    exists y.
    intuition.
  Qed.

   Lemma in_dsr_re_union : forall s x r1 r2,
    x \In (s[.](katu r1 r2)) -> 
    exists y, x === katc y (katu r1 r2) /\ y \In s.
  Proof.
    induction s using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    rewrite dsr_empty in H0.
    inversion H0.

    generalize H0;intro H3;apply Add_Equal in H0.
    rewrite H0 in H1.
    rewrite dsr_add in H1.
    apply add_iff in H1.
    destruct H1.
    exists x.
    rewrite H1.
    split.
    reflexivity.
    rewrite H0.
    apply add_1;reflexivity.

    apply IHs1 in H1.
    destruct H1 as [y [H11 H12]].
    exists y.
    split;auto.
    rewrite H0;apply add_2.
    assumption.

    unfold Not_0_1.
    intuition;
      inversion H2.
  Qed.

  Lemma in_dsr_re_conc : forall s x r1 r2,
    x \In (s[.](katc r1 r2)) -> 
    exists y, x === katc y (katc r1 r2) /\ y \In s.
  Proof.
    induction s using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    rewrite dsr_empty in H0.
    inversion H0.
    generalize H1;intro H3;apply Add_Equal in H0.
    rewrite H0 in H1.
    rewrite dsr_add in H1.
    apply add_iff in H1.
    destruct H1.
    exists x.
    rewrite H1.
    split;try reflexivity.
    rewrite H0;apply add_1;reflexivity.

    apply IHs1 in H1.
    destruct H1 as [y [H11 H12]].
    exists y.
    split;auto.
    rewrite H0;apply add_2;auto.

    unfold Not_0_1.
    intuition;
      inversion H2.
  Qed.

  Lemma in_dsr_re_star : forall s x r,
    x \In (s[.](katst r)) -> 
    exists y, x === katc y (katst r) /\ y \In s.
  Proof.
    induction s using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H0.
    rewrite dsr_empty in H0.
    inversion H0.
    generalize H1;intro H3;apply Add_Equal in H0.
    rewrite H0 in H1.
    rewrite dsr_add in H1.
    apply add_iff in H1.
    destruct H1.
    exists x.
    rewrite H1.
    split;auto.
    rewrite H0.
    apply add_1;reflexivity.

    apply IHs1 in H1.
    destruct H1 as [y [H11 H12]].
    exists y.
    split;auto.
    rewrite H0;apply add_2;auto.

    unfold Not_0_1.
    intuition;
      inversion H2.
  Qed.

  Lemma in_dsr : forall s r x,
                   Not_0_1 r -> x \In (s[.]r) -> 
                   exists y', y' \In s /\ x === katc y' r.
  Proof.
    induction s using set_induction;intros.
    apply empty_is_empty_1 in H.
    rewrite H in H1.
    rewrite dsr_empty in H1.
    inversion H1.
    apply Add_Equal in H0.
    rewrite H0 in H2.
    rewrite dsr_add in H2;auto.
    apply add_iff in H2.
    destruct H2.
    exists x.
    rewrite H2.
    split;auto.
    rewrite H0;apply add_1;auto.

    apply (IHs1 _ _ H1) in H2.
    do 2 destruct H2.
    exists x1.
    split;auto.
    rewrite H0;apply add_2;auto.
  Qed.

  (** dsr cardinality *)

  Theorem dsr_cardinal : forall s r,  (cardinal (s[.]r)) <= (cardinal s).
  Proof.
    intros s r;
      generalize(fold_conc_card s r);
        revert r.
    induction r;simpl;intro H.
    rewrite H.
    abstract omega.
    destruct t.
    rewrite cardinal_1.
    omega.
    red;intros;intro.
    inversion H0.
    omega.
    rewrite H;omega.
    rewrite H;omega.
    rewrite H;omega.
    rewrite H;omega.
    rewrite H;omega.
    rewrite H;omega.
    rewrite H;omega.
  Qed.  

  Inductive SkatL : set kat -> gl :=
    | in_skat_lang : 
      forall s w r, 
        r \In s -> In _ (kat2gl r) w -> In _ (SkatL s) w.

  Notation "L[ s ]" := (SkatL s)(at level 0).

  Hint Constructors SkatL : gl_hints.
 
  Instance SkatL_m : Proper(_eq ==> gl_eq) SkatL.
  Proof.
    repeat red.
    induction x using set_induction;gl_goal.
    inv H1.
    subst.
    apply H0 in H2.
    econstructor.
    apply H2.
    assumption.
    inv H1.
    subst.
    econstructor.
    apply H0.
    apply H2.
    assumption.
    inv H2.
    subst.
    econstructor.
    apply H1.
    apply H3.
    assumption.
    inv H2.
    subst.
    econstructor.
    apply H1.
    apply H3.
    assumption.
  Qed.
  
  Instance kat2gl_m_eq : Proper (_eq ==> gl_eq) (fun a => kat2gl a).
  Proof.
    repeat red.
    split;red;intros;inv H.
  Qed.
  
  Lemma In_SkatL_elem : 
    forall (s:set kat) (w:gstring),
      In _ (SkatL s) w  -> exists r, r \In s /\ In _ (kat2gl r) w.
  Proof.
    induction s using set_induction;intros.
    inversion_clear H0.
    exists r;auto.
    inversion_clear H1.
    apply Add_Equal in H0.
    rewrite H0 in H2.
    apply add_iff in H2.
    destruct H2.
    subst.
    exists r;split;auto.
    rewrite H0.
    rewrite H1.
    apply add_1.
    reflexivity.
    exists r;split.
    rewrite H0.
    apply add_2;auto.
    assumption.
  Qed.
  
  Lemma In_kat2gl_in_SkatL : 
    forall w (r:kat),
      In _ (kat2gl r) w -> forall s, r \In s -> In _ (SkatL s) w.
  Proof.
    intros w r H s.
    induction s using set_induction;intros.
    econstructor.
    apply H1.
    assumption.
    econstructor.
    apply H2.
    assumption.
  Qed.
  
  Lemma SkatL_empty : gl_emp == L[{}].
  Proof.
    gl_goal.
    inv H.
    inv H.
    inv H0.
  Qed.
  
  Lemma SkatL_singleton : 
    forall x:kat,
      L[{x}%set] == x.
  Proof.
    gl_goal.
    inversion_clear H.
    apply singleton_1 in H0.
    apply kat2gl_m_eq in H0.
    apply H0 in H1.
    assumption.
    
    econstructor.
    apply singleton_2.
    reflexivity.
    assumption.
  Qed.
  
  Lemma SkatL_union : 
    forall x y:set kat, 
      L[x ++ y] == gl_union L[x] L[y].
  Proof.
    gl_goal.
    inversion_clear H.
    apply union_iff in H0.
    destruct H0.
    constructor 1.
    econstructor.
    apply H.
    assumption.
    constructor 2;econstructor;auto.
    apply H;assumption.
    assumption.
    destruct H.
    destruct H.
    econstructor.
    apply union_2.
    apply H.
    assumption.
    destruct H.
    econstructor.
    apply union_3.
    apply H.
    assumption.
  Qed.
  
  Lemma SkatL_add : 
    forall a x,
      L[{a;x}] == gl_union L[{a}%set] L[x].
  Proof.
    induction x using set_induction;intros.
    gl_goal.
    inversion_clear H0.
    apply add_iff in H1.
    destruct H1.
    subst.
    constructor.
    eapply SkatL_singleton.
    apply kat2gl_m_eq in H0.
    apply H0.
    assumption.
    elim (H r).
    assumption.
    destruct H0.
    apply SkatL_singleton in H0.
    constructor 1 with (r:=a).
    apply add_1;apply singleton_1;apply singleton_2;reflexivity.
    assumption.
    inversion_clear H0.
    econstructor 1 with (r:=r).
    apply add_2;assumption.
    assumption.
    apply Add_Equal in H0.
    rewrite H0.
    gl_goal.
    inversion_clear H1.
    apply add_iff in H2.
    destruct H2.
    constructor.
    eapply SkatL_singleton.
    apply kat2gl_m_eq in H1.
    apply H1.
    assumption.
    constructor 2.
    apply add_iff in H1.
    destruct H1.
    constructor 1 with r.
    rewrite <- H1.
    apply add_1;apply singleton_1;apply singleton_2;reflexivity.
    assumption.
    econstructor 1 with r.
    apply add_2.
    assumption.
    assumption.
    destruct H1.
    constructor 1 with (r:=a).
    inversion_clear H1.
    apply add_1.
    reflexivity.
    apply SkatL_singleton in H1.
    assumption.
    destruct H1.
    econstructor 1 with (r:=r).
    apply add_2;auto.
    assumption.
  Qed.

  Lemma  SkatL_fconc : 
    forall s r, 
      L[(fold_conc s r)%set] == gl_conc (L[s]) r.
  Proof.
    gl_goal.
    inversion_clear H.
    apply elem_conc_in_ex in H0.
    destruct H0.
    destruct H.
    apply kat2gl_m_eq in H0.
    apply H0 in H1.
    simpl in H1.
    inversion_clear H1.
    constructor.
    econstructor 1 with (r:=x0);auto.
    assumption.
    
    inversion_clear H.
    destruct H0.
    apply elem_conc_in_fold_conc with (r:=r) in H.
    econstructor.
    apply H.
    simpl.
    constructor;auto.
  Qed.

  Lemma SkatL_dsr : 
    forall s r, 
      L[dsr s r] == gl_conc L[s] r.
  Proof.
    gl_goal.
    inversion_clear H.
    destruct(eq_dec r (katb (ba0))).
    rewrite H in H0.
    simpl in H0.
    inversion H0.
    destruct(eq_dec r (katb (ba1))).
    rewrite H2 in H0;simpl in H0.
    apply kat2gl_m_eq in H2.
    assert( compatible x (gs_end (last x))).
    red.
    simpl.
    reflexivity.
    rewrite (fusion_prod_same_last x H3).
    constructor.
    econstructor.
    apply H0.
    assumption.
    apply H2;simpl.
    constructor.
    reflexivity.
    eapply conc_gl_atom_true_left.
    apply in_dsr in H0;auto.
    destruct H0.
    destruct H0.
    generalize H3;intro.
    apply kat2gl_m_eq in H4.
    apply H4 in H1.
    assert( compatible x (gs_end (last x))).
    red.
    simpl.
    reflexivity.
    rewrite (fusion_prod_same_last x H5).
    constructor.
    simpl in H1.
    inversion_clear H1.
    constructor;auto.
    econstructor.
    apply H0.
    assumption.
    constructor.
    reflexivity.

    inversion_clear H.
    inversion_clear H0.
    destruct(eq_dec r (katb ba0)).
    apply kat2gl_m_eq in H0.
    apply H0 in H1;inversion H1.
    inv H1.
    destruct(eq_dec r (katb ba1)).
    generalize H3;intros.
    apply kat2gl_m_eq in H4.
    apply H4 in H1.
    simpl in H1.
    eapply conc_gl_atom_true_left.
    constructor;auto.
    econstructor 1 with (r:=r0).
    rewrite H3.
    simpl.
    assumption.
    assumption.
    econstructor.
    apply elem_conc_dsr_in;auto.
    apply H.
    simpl;constructor;auto.
  Qed.
  
End KAT.
