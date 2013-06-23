Add LoadPath "." as PDCoq.
Require Export re_sets generic_set_theory.

Open Scope set_scope.

Definition fold_conc :=
  fun (s:set re)(r:re) => (map (fun x => x · r)) s.

(*Transparent map.*)

Instance right_prod :  forall x0, Proper (_eq ==> _eq) (fun x2 : re => x2 · x0).
Proof.
  repeat red;intros;econstructor;autotc;reflexivity.
Qed.

Instance fold_conc_proper : forall x0, Proper (_eq ==> Equal ==> Equal)
  (fun (a : re) (acc : set re) => {a · x0; acc}).
Proof.
  repeat red;split_eq;normalize_notations;
  [rewrite H0 in H1 |rewrite <- H0 in H1];apply add_iff in H1;destruct H1;
    try (now (apply add_2;autotc));
  rewrite <- H1;apply add_1;constructor;autotc;order.
Qed.

Lemma fold_conc_transpose :forall x0,
  transpose Equal (fun (a : re) (acc : set re) => {a · x0; acc}).
Proof.
  unfold transpose;split_eq;
  apply add_iff in H;destruct H;
    (try now (apply add_2;apply add_1;symmetry;auto));
  apply add_iff in H;destruct H;
      (try now (apply add_1;symmetry;auto));
      now (do 2 apply add_2;auto).
Qed.

(*Definition re_ord_arg_1 := (@SetAVLInstance.SetAVL_FSet re re_ord).
Definition re_ord_arg_2 := (@SetAVLInstance.SetAVL_FSetSpecs re re_ord).*)

Add Morphism fold_conc : fold_conc_m.
Proof.
  unfold fold_conc;induction x using set_induction;intros.
  Transparent map.
  unfold map.
  normalize_notations.
  assert(Empty y) by (rewrite <- H0;auto).
  rewrite fold_1b;auto;rewrite fold_1b;auto.
  unfold map.

  rewrite (@fold_2 re re_ord _ _ x1 x2 x3 _ _ Equal_ST _ _ 
    (fold_conc_proper x0) (fold_conc_transpose x0) H H0).
  normalize_notations.
  assert(Add x3 x1 y).
  apply Add_Equal.
  apply Add_Equal in H0.
  rewrite <- H0;symmetry;auto.
  rewrite (@fold_2 re re_ord _ _ x1 y x3 
    _ _ Equal_ST _ _ 
    (fold_conc_proper y0) (fold_conc_transpose y0) H H3).
  apply add_m.
  normalize_notations.
  constructor;auto.
  normalize_notations.
  reflexivity.
  unfold map in IHx1.
  eapply IHx1.
  reflexivity.
  assumption.
Qed.
  
Infix "▸" := fold_conc(at level 60).

(** Main properties of the map concatenation function defined above *)

Open Scope set_scope.

Lemma fold_conc_empty : 
  forall r:re, {} ▸ r === {}.
Proof. 
  unfold fold_conc;vm_compute;auto.
Qed.

Lemma fold_conc_singleton : 
  forall x r, 
    (singleton x) ▸ r === singleton (x · r).
Proof. 
  intros;vm_compute;auto. 
Qed.
  
Hint Resolve 
  fold_conc_empty 
  fold_conc_singleton : res.

Instance fold_conc_proper_equal : forall r, Proper (_eq ==> Equal ==> Equal)
  (fun (a : re) (acc : set re) => {a · r; acc}).
Proof.
  repeat red;split;intros;normalize_notations.
  (rewrite H0 in H1;revert H1;apply add_m;normalize_notations;autotc;
    constructor;normalize_notations;autotc).
  (rewrite <- H0 in H1;revert H1;apply add_m;normalize_notations;autotc;
    constructor;normalize_notations;autotc).
Qed.

Lemma fold_conc_trans_equal : forall r, 
  transpose Equal (fun (a : re) (acc : set re) => {a · r; acc}).
Proof.
  repeat red;split_eq;apply add_iff in H;destruct H.
  apply add_2;apply add_1;auto.
  apply add_iff in H;destruct H.
  apply add_1;auto.
  do 2 apply add_2;auto.
  apply add_2;apply add_1;auto.
  apply add_iff in H;destruct H.
  apply add_1;auto.
  do 2 apply add_2;auto.
Qed.
  
(** Introduction of element in dsr/dsl *)

Lemma elem_conc_in_fold_conc : forall s x r, 
  x \In s -> (x · r) \In (s ▸ r).
Proof.
  induction s using set_induction;intros.
  apply H in H0;elim H0.
  unfold fold_conc;eapply map_spec;autotc;exists x0;autotc.
Qed.
  
(** Elimination rule for elements of fold_conc *)

Lemma elem_conc_fold_conc_in : forall s x r, 
  (x · r) \In (fold_conc s r) -> x \In s.
Proof.
  induction s using set_induction.
  intros.
  unfold fold_conc,map in H0;rewrite fold_1b in H0;
    auto.
  inversion H0.
  
  intros.
  unfold fold_conc,map in H1.
  generalize(@fold_2 re _ _ _ s1 s2 x 
    _ _ Equal_ST {}%set  _
      (fold_conc_proper _) (fold_conc_transpose r) H H0).
  intro.
  rewrite H2 in H1.
  clear H2.
  apply add_iff in H1.
  destruct H1.
  inversion_clear H1.
  normalize_notations.
  apply H0;auto.
  apply IHs1 in H1.
  apply H0;auto.
Qed.

Lemma elem_conc_nin_dsr : forall s x r, 
  ~(x \In s) -> ~((x · r) \In (fold_conc s r)).
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
  ~(x · r) \In (fold_conc s r) ->
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
  x \In (fold_conc s r) -> exists y, y \In s /\ x === y · r.
Proof.
  intros.
  apply map_spec in H;auto with typeclass_instances.
Qed.
  
Lemma elem_conc_nin_ex : forall s x r,
  ~x \In (fold_conc s r) -> ~exists y, y \In s /\ x === y · r.
Proof.
  induction s using set_induction;intros.
  intro.
  destruct H1 as [y [H11 H12]].
  Typeclasses Transparent re_ord.
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
  Typeclasses Opaque re_ord.
Qed.
  
Lemma elem_conc_ex_nin : forall s x r,
  ~x \In s -> ~exists y, (y · r) \In (fold_conc s r) /\ x === y.
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
  constructor;auto.
  normalize_notations.
  reflexivity.
Qed.

Lemma fold_conc_add : forall s r x x0,
  x \In (fold_conc (add x0 s) r) -> x \In (add (x0 · r) (fold_conc s r)).
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
  
  generalize(@fold_2 re _ _ _ s1 s2 x 
    _ _ Equal_ST {}%set  _
      (fold_conc_proper _) (fold_conc_transpose r) H H0).
  intro.
  unfold fold_conc,map.
  rewrite H1.
  
  apply add_iff in H11.
  Typeclasses Transparent re_ord.
  rewrite H12.
  destruct H11.
  apply add_1.
  constructor;auto.
  normalize_notations;reflexivity.
  
  apply add_2.
  
  apply elem_conc_in_fold_conc with (r:=r) in H2.
  unfold fold_conc,map in H2.
  rewrite H1 in H2.
  assumption.
  Typeclasses Opaque re_ord.
Qed.

Lemma fold_add_conc : forall s r x x0,
  x \In (add (x0 · r)  (fold_conc s r)) -> x \In (fold_conc (add x0 s) r).
Proof.
  induction s using set_induction;intros.
  apply empty_is_empty_1 in H.
  rewrite H in H0 |- *.
  rewrite fold_conc_empty in H0.
  rewrite <- singleton_equal_add in H0 |- *.
  rewrite fold_conc_singleton.
  assumption.
  apply add_iff in H1.
  generalize(@fold_2 re _ _ _ s1 s2 x 
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
  Typeclasses Transparent re_ord.
  rewrite H12.
  apply elem_conc_in_fold_conc with (r:=r).
  apply add_iff in H11.
  destruct H11.
  rewrite <- H1.
  apply add_2.
  apply H0;auto.
  apply add_2.
  apply H0;auto.
  Typeclasses Opaque re_ord.
Qed.
    
Lemma fold_conc_add_eq : forall s r x, 
  (fold_conc (add x s) r) === (add (x · r) (fold_conc s r)).
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
  normalize_notations.
  reflexivity.
  normalize_notations.
  reflexivity.
  
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
  rewrite empty_union_1 in H0;autotc.
  
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

Notation "# s" := (cardinal s)(at level 0).
    
Lemma fold_conc_card : forall s r,
  #(fold_conc s r) = #s.
Proof.
  induction s using set_induction;intros.
  apply empty_is_empty_1 in H.
  rewrite H.
  rewrite fold_conc_empty.
  reflexivity.
  
  generalize(@fold_2 re _ _ _ s1 s2 x 
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
    
Hint Resolve 
  fold_conc_empty 
  fold_conc_singleton 
  elem_conc_fold_conc_in
  elem_conc_in_ex 
  fold_conc_singleton
  fold_conc_empty
  fold_add_conc
  fold_conc_add
  fold_conc_union
  fold_union_conc
  fold_conc_card : res.
  
(** * Implementation of [dsr] and [dsl] *)
  
(** Map for prefixing regular expressions *)

Definition dsr (s:set re)(r:re): set re := 
  match r with
    | 0 => {}%set
    | 1 => s
    | _ => s ▸ r
  end.

Notation "x ⊙ y" := (dsr x y)(at level 60).
Hint Unfold dsr.

(* Their functional inductive principles *)
Functional Scheme dsr_ind := Induction for dsr Sort Prop.
Functional Scheme dsr_rec := Induction for dsr Sort Set.

Lemma dsr_re0 : forall s, (s ⊙ 0)==={}%set.
Proof.
  intro;simpl;reflexivity.
Qed.
    
Lemma dsr_empty : forall r, ({}⊙r)==={}%set.
Proof.
  induction r;simpl;first [reflexivity | rewrite fold_conc_empty].
Qed.

Definition Not_0_1 (r:re) := ~r === 0 /\ ~r === 1.
Hint Unfold Not_0_1.

Lemma map_singleton :
  forall t x,
    map (fun x0 : re => x0 · t) {x} === {x· t}%set.
Proof.
  split_eq.
  apply map_spec in H;autotc.
  destruct H as [a0 [H1 H2]]. rewrite H2. apply singleton_1 in H1.
  apply singleton_2. constructor;autotc. reflexivity.
  apply map_spec;autotc.
  exists x;split.
  apply singleton_2;autotc.
  apply singleton_1 in H;autotc.
Qed.

Lemma dsr_singleton : forall x r, Not_0_1 r ->
  ({x}%set ⊙ r)=== {x · r}%set.
Proof.
  induction r;simpl;
    unfold Not_0_1;intros;unfold fold_conc.
  intuition. intuition. rewrite map_singleton;auto.
  rewrite map_singleton;auto.
  rewrite map_singleton;auto.
  rewrite map_singleton;auto.
Qed.

Hint Resolve dsr_singleton dsr_empty dsr_re0 : res.
Hint Unfold dsr.

Add Morphism dsr : dsr_mor.
Proof.
  intros.
  normalize_notations.
  unfold dsr.
  destruct H0;auto;normalize_notations.
  rewrite H0.
  rewrite H.
  reflexivity.
  apply fold_conc_m;auto with typeclass_instances.
  normalize_notations.
  constructor;normalize_notations;auto.
  apply fold_conc_m;normalize_notations;auto.
  constructor;normalize_notations;auto.
  rewrite H.
  apply fold_conc_m;auto with typeclass_instances;
    normalize_notations;auto.
  constructor;auto.
Qed.

Hint Resolve dsr_mor: res.

(** Case analysis over [dsr] and [dsl] *)

Lemma dsr_cases : forall s r,
  (s⊙r)==={}%set \/ (s⊙r)===s \/ (Not_0_1 r /\ (s⊙r)===(fold_conc s r)).
Proof.
  induction r;simpl;auto;
    do 2 right;unfold Not_0_1;do 2 try split;unfold not;
      try match goal with 
            | [ |- ?X === ?Y -> False ] => intro H;inversion H
          end;auto.
Qed.
  
Hint Resolve dsr_cases : res.

(* Introduction of element in dsr *)

Lemma elem_conc_dsr_in : forall s x r,
  Not_0_1 r -> x \In s -> (x · r) \In (s⊙r).
Proof.
  induction r;intros;try (unfold Not_0_1 in H);unfold dsr;
  try (now(apply elem_conc_in_fold_conc;auto)).
  destruct H. elim H;autotc.
  destruct H;elim H1;autotc.
Qed.
    
Lemma elem_conc_in_dsr : forall s x r,
  Not_0_1 r -> (x · r) \In (s⊙r) -> x \In s.
Proof.
  induction r;intros;try (unfold Not_0_1 in H);
  try (now(eapply elem_conc_fold_conc_in in H0;assumption)).
  inv H0.
  destruct H. elim H1;autotc.
Qed.

Hint Resolve 
    elem_conc_dsr_in 
    elem_conc_in_dsr : res.
  
Lemma dsr_add : forall s x r,
  Not_0_1 r -> (({x;s})⊙r)===(add (x·r) (s⊙r)).
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
  unfold Not_0_1 in *;intuition.
  unfold Not_0_1 in *;intuition.
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
Qed.

(** Emptyness of dsr and dsl implies emptyness of the set, or that the regular
   expressions considered is 0 *)

Lemma dsr_empty_res : forall s r, Empty (s⊙r) -> Empty s \/ r === 0.
Proof.
  induction s using set_induction;intros.
  left;auto.
  apply Add_Equal in H0.
  rewrite H0 in H1 |- *.
  apply empty_is_empty_1 in H1.
  destruct(eq_dec r 0);auto.
  destruct(eq_dec r 1);auto.
  apply empty_is_empty_2 in H1.
  elim (H1 (x·r));auto with res.
  Typeclasses Transparent re_ord.
  rewrite H3 in H1.
  simpl in H1.
  elim (H1 x).
  apply add_1.
  reflexivity.
  
  left.
  apply empty_is_empty_2 in H1.
  elim H1 with (a:=(x·r)).
  apply elem_conc_dsr_in.
  red;auto.
  apply add_1;auto.
  Typeclasses Opaque re_ord.
Qed.

Hint Resolve  dsr_empty_res : res.
  
Lemma dsr_union : forall s x r,
  ((x++s)⊙r)===((x⊙r)++(s⊙r)).
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
  absinv x1.
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
  absinv x1.
  
  functional induction (dsr x2 r);simpl.
  rewrite empty_union_1.
  reflexivity.
  vm_compute;intros.
  inversion x0.
  reflexivity.
  split;intro.
  apply fold_conc_union in H1.
  assumption.
  apply union_iff in H1.
  apply fold_union_conc.
  destruct H1.
  apply union_2.
  assumption.
  apply union_3;assumption.
  split;intros.
  apply fold_conc_union in H1.
  assumption.
  apply fold_union_conc.
  assumption.
  split;intro.
  apply fold_conc_union in H1.
  assumption.
  apply fold_union_conc.
  assumption.
  split;intro.
  apply fold_conc_union in H1.
  assumption.
  apply fold_union_conc.
  assumption.
Qed.

Lemma dsr_not_empty : forall s r, 
  ~Empty s -> r =/= 0 -> ~Empty (s⊙r).
Proof.
  intros.
  intro.
  apply dsr_empty_res in H1.
  destruct H1;contradiction.
Qed.

Hint Resolve 
    dsr_add 
    dsr_union 
    dsr_not_empty : res.
    
(** Some counter-example based lemmas *)

Lemma in_dsr_re0 : forall s, 
  ~exists x, x \In (s⊙0).
Proof.
  intros s H.
  destruct H.
  rewrite dsr_re0 in H.
  inversion H.
Qed.

Lemma in_dsr_re_sy : forall s a x, 
  x \In (s⊙\!a) -> 
  exists y, x === y·\!a /\ y \In s.
Proof.
  intros.
  simpl in H.
  apply elem_conc_in_ex in H.
  destruct H as [y [H11 H12] ].
  exists y.
  intuition.
Qed.

Lemma in_dsr_re_union : forall s x r1 r2,
  x \In (s⊙(r1 + r2)) -> 
  exists y, x === y · (r1 + r2) /\ y \In s.
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
  Typeclasses Transparent re_ord.
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
  split;intro;inv H2.
  Typeclasses Opaque re_ord.
Qed.
  
Lemma in_dsr_re_conc : forall s x r1 r2,
  x \In (s⊙(r1 · r2)) -> 
  exists y, x === y · (r1 · r2) /\ y \In s.
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
  Typeclasses Transparent re_ord.
  rewrite H1.
  split;try reflexivity.
  rewrite H0;apply add_1;reflexivity.
  
  apply IHs1 in H1.
  destruct H1 as [y [H11 H12]].
  exists y.
  split;auto.
  rewrite H0;apply add_2;auto.
  
  unfold Not_0_1.
  split;intro;inv H2.
  Typeclasses Opaque re_ord.
Qed.
  
Lemma in_dsr_re_star : forall s x r,
  x \In (s⊙(r⋆)) -> 
  exists y, x === y · (r⋆) /\ y \In s.
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
  Typeclasses Transparent re_ord.
  rewrite H1.
  split;auto.
  rewrite H0.
  apply add_1;reflexivity.
  
  apply IHs1 in H1.
  destruct H1 as [y [H11 H12]].
  exists y.
  split;auto.
  rewrite H0;apply add_2;auto.
  
  unfold Not_0_1;split;intro;inv H2.
  Typeclasses Opaque re_ord.
Qed.
  
Lemma in_dsr : forall s r x,
  Not_0_1 r -> x \In (s⊙r) -> 
  exists y', y' \In s /\ x === y' · r.
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
  Typeclasses Transparent re_ord.
  rewrite H2.
  split;auto.
  rewrite H0;apply add_1;auto.

  apply (IHs1 _ _ H1) in H2.
  do 2 destruct H2.
  exists x1.
  split;auto.
  rewrite H0;apply add_2;auto.
  Typeclasses Opaque re_ord.
Qed.

Hint Resolve 
  in_dsr_re0 
  in_dsr_re_sy 
  in_dsr_re_union 
  in_dsr_re_conc 
  in_dsr_re_star
  in_dsr : res.

(** dsr cardinality *)

Theorem dsr_cardinal : forall s r,  (cardinal (s⊙r)) <= (cardinal s).
Proof.
  intros s r;
    generalize(fold_conc_card s r);
      revert r.
  induction r;simpl;try (now(omega));intro H.
  rewrite cardinal_1;autotc.
  omega.
Qed.

Hint Resolve dsr_cardinal : res.

(*Infix "=L=" := leq(at level 45).*)

(** Simple properties of a language of a sets of regular expressions *)
Lemma LangOfFSet_empty : (L[{}%set]) ∼ ∅.
Proof.
  split_eq.
  inversion_clear H.
  inversion H0.
  inversion H.
Qed.

Lemma LangOfFSet_singleton : forall r, L[{r}%set] ∼ r.
Proof.
  split_eq.
  inversion_clear H.
  apply singleton_1 in H0.
  apply re2rel_m_eq in H0.
  apply H0 in H1;auto.
  econstructor 1 with (r:=r).
  apply singleton_2.
  reflexivity.
  assumption.
Qed.

Lemma LangOfFSet_union : forall r1 r2:set re, 
  L[r1++r2] ∼ (L[r1] ∪ L[r2]).
Proof.
  split_eq.
  inversion_clear H.
  apply union_1 in H0.
  destruct H0.
  left.
  econstructor 1 with r;auto.
  right.
  econstructor 1 with r;auto.
  destruct H.
  inversion_clear H.
  econstructor 1 with r;auto.
  apply union_2;auto.
  inversion_clear H.
  econstructor 1 with r;auto.
  apply union_3;auto.
Qed.

(** * Language of finite concatenation maps dsr and dsl *)
Lemma LangOfFSet_fconc : forall s r, 
  (L[s ▸r]) ∼ (L[s] • r).
Proof.
  split_eq.
  inversion_clear H.
  apply elem_conc_in_ex in H0.
  destruct H0.
  destruct H.
  apply re2rel_m_eq in H0.
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

Lemma LangOfFset_dsr : 
  forall s r, 
    L[s⊙r] ∼ (L[s] • r).
Proof.
  split_eq.
  inversion_clear H.
  destruct(eq_dec r 0).
  Typeclasses Transparent re_ord.
  rewrite H in H0.
  simpl in H0.
  inversion H0.
  destruct(eq_dec r 1).
  rewrite H2 in H0;simpl in H0.
  apply re2rel_m_eq in H2.
  replace x with (app x nil)%list;auto.
  constructor.
  econstructor.
  apply H0.
  assumption.
  apply H2;simpl.
  constructor.
  rewrite app_nil_end.
  reflexivity.
  apply in_dsr in H0;auto.
  eapply conc_l_neutral_right.
  
  destruct H0.
  destruct H0.
  generalize H3;intro.
  apply re2rel_m_eq in H4.
  apply H4 in H1.
  replace x with (app x nil)%list;auto.
  constructor.
  simpl in H1.
  inversion_clear H1.
  constructor;auto.
  econstructor.
  apply H0.
  assumption.
  constructor.
  rewrite app_nil_end;auto.
  
  inversion_clear H.
  inversion_clear H0.
  destruct(eq_dec r 0).
  apply re2rel_m_eq in H0.
  apply H0 in H1;inversion H1.
  destruct(eq_dec r 1).
  generalize H3;intros.
  apply re2rel_m_eq in H4.
  apply H4 in H1.
  simpl in H1.
  eapply conc_l_neutral_right.
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
  Typeclasses Opaque re_ord.
Qed.

