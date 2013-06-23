Require Import pdrvs.

Fixpoint ss(x:re) :=
  match x with
    | re0 => {}
    | re1 => {}
    | re_sy a => {a}
    | re_union z t => union (ss z) (ss t)
    | re_conc z t => union (ss z) (ss t)
    | re_star z => ss z
  end.

Instance ss_m : Proper(_eq ==> _eq) ss.
Proof.
  repeat red;
  intros x y H;
  intro a;
  split;intros;
  destruct(re_sy_dec x y);
  subst;auto;
  apply re_leibniz in H;
  contradiction.
Qed.

Inductive langSsy : set Z -> language :=
| nil_in_ss : 
    forall r,
      nil ∈ langSsy r
| sy_in_ss_conc :
    forall s x,
      x \In s -> forall w, w ∈ langSsy s ->
                           (x::w) ∈ langSsy s.

Lemma langSsy_empty_set :
  forall w, w <> [] ->
            ~(w ∈ langSsy {}).
Proof.
  induction w.
  intro.
  elim H;auto.
  intros.
  intro.
  inversion_clear H0.
  inversion H1.
Qed.

Lemma langSsy_nil : 
  forall s, [] ∈ langSsy s.
Proof.
  constructor.
Qed.

Lemma langSsy_one_sy_word :
  forall s x,
    x \In s -> [x] ∈ langSsy s.
Proof.
  induction s using set_induction.
  intros.
  apply H in H0.
  elim H0.
  
  intros.
  constructor.
  assumption.
  constructor.
Qed.

Lemma one_sy_word_in_langSsy :
  forall s a,
    [a] ∈ langSsy s -> exists t, t \In s /\ t === a.
Proof.
  induction s using set_induction.
  intros.
  inversion_clear H0.
  apply H in H1.
  elim H1.
  
  intros.
  inversion_clear H1.
  pose proof H2.
  apply H0 in H1.
  destruct H1.
  exists a.
  split;auto.
  exists a.
  split;auto.
Qed.


Lemma word_cons_in_elem_langSsy :
  forall a w s,
    (a :: w) ∈  langSsy s -> a \In s /\ w ∈ langSsy s.
Proof.
  intros.
  inversion_clear H.
  split;auto.
Qed.

Lemma in_langSsy_word_cons :
  forall a w s,
    a \In s -> w ∈ langSsy s -> (a :: w) ∈  langSsy s.
Proof.
  induction w;intros.
  constructor;auto.
  apply word_cons_in_elem_langSsy in H0.
  destruct H0.
  constructor;auto.
  constructor;auto.
Qed.

Lemma word_in_set_all_sy_in_langSsy :
  forall s w,
    w ∈  langSsy s -> 
    forall a, List.In a w -> exists t, t \In s /\ t === a.
Proof.
  induction w;simpl;intros.
  elim H0.
  apply word_cons_in_elem_langSsy in H.
  destruct H.
  destruct H0.
  subst.
  exists a0;split;auto.
  destruct (IHw H1 a0 H0) as [t [H5 H6]].
  exists t;split;auto.
Qed.

Lemma word_concat_sy_in_langSsy :
  forall w a r1 r2,
    (w ++ [a])%list ∈  langSsy (ss r1 ++ ss r2) ->
    w ∈ langSsy (ss r1 ++ ss r2) /\ 
    [a] ∈ langSsy (ss r1 ++ ss r2).
Proof.
  induction w;simpl;intros.
  split;auto.
  constructor.
  apply word_cons_in_elem_langSsy in H.
  destruct H.
  split.
  constructor.
  assumption.
  apply IHw in H0.
  destruct H0.
  assumption.
  apply IHw in H0.
  destruct H0.
  assumption.
Qed.

Add Morphism langSsy : langSsy_m.
Proof.
  split_eq;
  revert x0 H0;
  induction x0;intros;
  constructor;
  inversion_clear H0;
  (try now (apply H;auto)||auto).
Qed.

Lemma in_union_ss_Ssy_l :
  forall w s1,
    w ∈ langSsy s1 ->
    forall s2, 
      w ∈ langSsy (s1 ++ s2).
Proof.
  induction w;intros.
  constructor.
  apply word_cons_in_elem_langSsy in H.
  destruct H.
  apply in_langSsy_word_cons.
  apply union_2;auto.
  apply IHw.
  assumption.
Qed.

Lemma in_union_ss_Ssy_r :
  forall w s1,
    w ∈ langSsy s1 ->
    forall s2, 
      w ∈ langSsy (s2 ++ s1).
Proof.
  induction w;intros.
  constructor.
  apply word_cons_in_elem_langSsy in H.
  destruct H.
  apply in_langSsy_word_cons.
  apply union_3;auto.
  apply IHw.
  assumption.
Qed.

Lemma not_in_langSsy_union :
  forall s1 s2 a,
    ~ [a] ∈  langSsy (s1 ++ s2) ->
    ~ [a] ∈ langSsy s1 /\ ~[a] ∈ langSsy s2.
Proof.
  intros;split;intro;
  apply H.
  apply in_union_ss_Ssy_l;auto.
  apply in_union_ss_Ssy_r;auto.
Qed.

Lemma concat_in_langSsy :
  forall w1 s1,  
    w1 ∈  langSsy s1 ->
    forall w2 s2, 
      w2 ∈  langSsy s2 ->
      (w1 ++ w2)%list ∈  langSsy (s1 ++ s2).
Proof.
  induction w1;intros.
  simpl.
  apply in_union_ss_Ssy_r;auto.
  rewrite <- app_comm_cons.
  apply in_langSsy_word_cons.
  apply word_cons_in_elem_langSsy in H.
  destruct H.
  apply union_2;auto.
  apply word_cons_in_elem_langSsy in H;destruct H.
  apply IHw1;auto.
Qed.

Lemma in_teste :
  forall r w,
    w ∈ (re2rel r) -> w ∈ langSsy (ss r).
Proof.
  induction r;simpl;intros.
  
  inversion_clear H.
  
  inversion_clear H.
  constructor.

  inversion_clear H.
  constructor;auto.
  apply singleton_2.
  symmetry;auto.
  constructor.

  inversion_clear H.
  apply in_union_ss_Ssy_l.
  apply IHr1;auto.
  apply in_union_ss_Ssy_r.
  apply IHr2;auto.

  inversion_clear H.
  clear w.
  apply IHr1 in H0.
  apply IHr2 in H1.
  apply concat_in_langSsy;auto.

  inversion_clear H.
  revert n w H0.
  induction n.
  intros.
  simpl in *.
  inversion_clear H0.
  constructor.
  
  simpl.
  intros.
  inversion_clear H0.
  apply IHn in H1.
  apply IHr in H.
  revert w1 w2 H H1.
  induction w1.
  simpl;auto.
  intros.
  apply word_cons_in_elem_langSsy in H.
  simpl.
  destruct H.
  constructor.
  assumption.
  apply IHw1;auto.
Qed.    

Lemma sy_not_in_langSsy_pdrv_empty :
  forall r a,
    ~[a] ∈ langSsy (ss r) ->
    pdrv r a === {}.
Proof.
  induction r;simpl;intros;auto.

  case_eq(compare z a);intros.
  apply compare_2 in H0.
  rewrite H0 in H.
  elim H.
  constructor.
  apply singleton_2;auto.
  constructor.
  reflexivity.
  reflexivity.

  apply not_in_langSsy_union in H.
  destruct H;auto.
  apply IHr1 in H.
  apply IHr2 in H0.
  rewrite H,H0.
  vm_compute.
  split;auto.

  apply not_in_langSsy_union in H.
  destruct H.
  apply IHr1 in H.
  apply IHr2 in H0.
  case_eq(ε(r1));intros.
  rewrite H,H0.
  rewrite dsr_empty.
  unfold c_c_of_re.
  vm_compute;split;auto.

  rewrite H.
  rewrite dsr_empty.
  reflexivity.

  apply IHr in H.
  rewrite H.
  vm_compute.
  split;auto.
Qed.
    
Lemma word_not_in_langSsy_pdrv_empty :
  forall w a r,
    ~[a] ∈ langSsy (ss r) ->
    wpdrv r (a::w) === {}.
Proof.
  induction w.
  intros.
  apply sy_not_in_langSsy_pdrv_empty in H.
  unfold wpdrv.
  simpl.
  rewrite pdrv_set_singleton.
  rewrite H.
  reflexivity.

  intros.
  apply sy_not_in_langSsy_pdrv_empty in H.
  unfold wpdrv.
  simpl.
  rewrite pdrv_iw_app.
  simpl.
  rewrite pdrv_set_singleton.
  rewrite H.
  rewrite pdrv_iw_empty.
  reflexivity.
Qed.

Lemma word_of_langSsy_decide_equiv :
  forall r1 r2,
    (forall w, w ∈ langSsy ((ss r1)++(ss r2)) ->
               c_of_re_set(wpdrv r1 w) = c_of_re_set(wpdrv r2 w)) ->
    r1 ∼ r2.
Proof.
  intros.
  split;red;intros.
  pose proof H0.
  apply in_teste in H1.
  assert(x ∈ langSsy (ss r1 ++ ss r2)).
  apply in_union_ss_Ssy_l;auto.
  apply H in H2.
  apply word_in_pdrv in H0.
  apply word_in_pdrv_true.
  rewrite <- H2.
  rewrite H0.
  reflexivity.
  pose proof H0.
  apply in_teste in H0.
  assert(x ∈ langSsy (ss r1 ++ ss r2)).
  apply in_union_ss_Ssy_r;auto.
  apply H in H2.
  apply word_in_pdrv in H1.
  apply word_in_pdrv_true.
  rewrite H2.
  rewrite H1.
  reflexivity.
Qed.

Definition ss_set(s:set re) :=
  fold (fun x => union (ss x)) s {}.

Instance f_union_ss_m :
  Proper (_eq ==> _eq ==> _eq) (fun x : re => union (ss x)).
Proof.
  repeat red;intros.
  split;intros.
  rewrite H in H1.
  rewrite H0 in H1.
  auto.
  rewrite H,H0;auto.
Qed.

Lemma f_union_ss_trans : transpose _eq (fun x : re => union (ss x)).
Proof.
  repeat red;intros.
  split;intros.
  apply union_1 in H.
  destruct H.
  apply union_3;apply union_2;auto.
  apply union_1 in H;destruct H.
  apply union_2;auto.
  do 2 apply union_3;auto.
  apply union_1 in H.
  destruct H.
  apply union_3;apply union_2;auto.
  apply union_1 in H;destruct H.
  apply union_2;auto.
  do 2 apply union_3;auto.
Qed.

Hint Resolve f_union_ss_trans : typeclass_instances.


Instance ss_set_m : Proper(equiv ==> equiv) ss_set.
Proof.
  repeat red.
  induction x using set_induction;intros.
  split;intros.
  unfold ss_set in H1.
  rewrite fold_1b in H1;auto.
  inversion H1.
  rewrite H0 in H.
  unfold ss_set in H1.
  rewrite fold_1b in H1;auto;inversion H1.

  split;intros.
  unfold ss_set in H2.
  pose proof @fold_2 re _ _ _ x1 x2 x3 (set Z) _eq _ (@empty Z _ _) 
       (fun x : re => union (ss x)) f_union_ss_m f_union_ss_trans.
  pose proof @fold_2 re _ _ _ x1 y x3 (set Z) _eq _ (@empty Z _ _) 
       (fun x : re => union (ss x)) f_union_ss_m f_union_ss_trans.
  assert(Add x3 x1 y).
  apply Add_Equal in H0.
  apply Add_Equal.
  rewrite <- H1.
  assumption.
  rewrite (H3 H H0) in H2.
  rewrite (H4 H H5).
  clear H4 H5.
  simpl in H2.
  apply union_iff in H2.
  destruct H2.
  apply union_2;auto.
  apply union_3;auto.

  unfold ss_set in H2.
  pose proof @fold_2 re _ _ _ x1 x2 x3 (set Z) _eq _ (@empty Z _ _) 
       (fun x : re => union (ss x)) f_union_ss_m f_union_ss_trans.
  pose proof @fold_2 re _ _ _ x1 y x3 (set Z) _eq _ (@empty Z _ _) 
       (fun x : re => union (ss x)) f_union_ss_m f_union_ss_trans.
  assert(Add x3 x1 y).
  apply Add_Equal in H0.
  apply Add_Equal.
  rewrite <- H1.
  assumption.
  rewrite (H4 H H5) in H2.
  rewrite (H3 H H0).
  clear H4 H5.
  simpl in H2.
  apply union_iff in H2.
  destruct H2.
  apply union_2;auto.
  apply union_3;auto.
Qed.

Lemma ss_set_empty :
  ss_set {} === {}.
Proof.
  unfold ss_set.
  vm_compute;split;auto.
Qed.

Lemma ss_set_singleton :
  forall a, ss_set {a} === ss a.
Proof.
  intro.
  assert(Equal {a} {a;{}}).
  split;intros.
  apply add_1.
  apply singleton_1 in H.
  assumption.
  apply add_iff in H.
  destruct H.
  rewrite H.
  apply singleton_2;auto.
  inversion H.
  rewrite H.
  unfold ss_set.
  rewrite fold_2;eauto with typeclass_instances.
  rewrite fold_1b.
  split;intros.
  apply union_iff in H0.
  destruct H0;auto.
  inversion H0.
  apply union_2;auto.
  vm_compute.
  intros.
  inversion x0.
  intro.
  inversion H0.
Qed.

Lemma ss_set_add :
  forall s a, 
    ss_set {a;s} === ss_set {a} ++ ss_set s.
Proof.
  induction s using set_induction;intros.
  unfold ss_set at 1.
  assert(~a \In s).
  intro.
  apply H in H0;elim H0.
  rewrite(@fold_add re _ _ _ (set Z) equiv _ 
                    (fun x : re => union (ss x)) _ f_union_ss_trans {} _ _ H0).
  rewrite ss_set_singleton.
  reflexivity.
  
  (*specialize IHs1 with a.*)
  apply Add_Equal in H0.
  rewrite H0.
  rewrite add_add.
  case_eq(eq_dec a x);intros;clear H1.
  rewrite e.
  rewrite add_equal.
  rewrite IHs1.
  symmetry.
  rewrite <- union_assoc.
  assert((ss_set {x})[<=](ss_set {x})).
  red;intros;auto.
  apply union_subset_equal in H1.
  rewrite H1.
  reflexivity.
  apply add_1;auto.
  unfold ss_set at 1.
  rewrite fold_add;auto with typeclass_instances.
  fold (ss_set {a;s1}).
  do 2 rewrite IHs1.
  repeat rewrite ss_set_singleton.
  rewrite <- union_assoc.
  rewrite (union_sym (ss x) (ss a)).
  rewrite union_assoc;reflexivity.
  unfold equiv;auto with typeclass_instances.
  intro.
  apply add_iff in H1.
  destruct H1.
  contradiction.
  contradiction.
Qed.

Require Import generic_set_theory.

Lemma ss_set_union :
  forall s1 s2,
    ss_set (s1 ++ s2) === ss_set s1 ++ ss_set s2.
Proof.
  induction s1 using set_induction;intros.
  transitivity (ss_set s2).
  apply empty_is_empty_1 in H.
  rewrite H.
  rewrite empty_union_left.
  reflexivity.
  apply empty_is_empty_1 in H.
  rewrite H.
  rewrite ss_set_empty.
  rewrite empty_union_left.
  reflexivity.
  
  apply Add_Equal in H0.
  rewrite H0.
  apply Add_Equal in H0.
  rewrite union_add.
  do  2 rewrite ss_set_add.
  rewrite IHs1_1.
  rewrite union_assoc.
  reflexivity.
Qed.



