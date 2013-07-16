Require Export dsr_dsl ilist.

Lemma sy_dec : forall x y:Z, {x===y}+{x=/=y}.
Proof.
  intros;case_eq(compare x y);intros.
  left.
  apply compare_2 in H;auto.
  apply compare_1 in H;apply lt_not_eq in H;auto.
  apply compare_3 in H;apply gt_not_eq in H;auto.
Qed.

Fixpoint pdrv (r:re)(s:Z) :=
  match r with
    | 0 => {}%set
    | 1 => {}%set
    | re_sy s' => match compare s' s with | Eq => {1}%set | _ => {}%set end
    | x + y => (pdrv x s)++(pdrv y s)
    | x · y => match ε(x) with
                  | false => dsr (pdrv x s) y 
                  | true => (dsr (pdrv x s) y)++(pdrv y s)
                end
    | x⋆  => dsr (pdrv x s) (x⋆)
  end.
Notation "∂( r , s )" := (pdrv r s)(at level 60).

Add Parametric Morphism : pdrv 
  with signature _eq ==> _eq ==> _eq as pdrv_m.
Proof.
  induction 1;
    intros;simpl;try reflexivity.
  rewrite H.
  normalize_notations.
  rewrite H0.
  destruct(compare y1 y0);auto;normalize_notations;
    generalize(IHre_eq1 _ _ H1);
      generalize(IHre_eq2 _ _ H1);intros H12 H13;
        rewrite H12,H13;reflexivity.
  normalize_notations.
  generalize(IHre_eq1 _ _ H1);
    generalize(IHre_eq2 _ _ H1);intros;
      normalize_notations.
  rewrite H3,H2;reflexivity.
  normalize_notations.
  Typeclasses Transparent re_ord.
  rewrite H.
  case(ε(y1)).
  specialize IHre_eq1 with x0 y0.
  rewrite (IHre_eq1 H1).
  specialize IHre_eq2 with x0 y0.
  rewrite (IHre_eq2 H1).
  rewrite H0.
  reflexivity.
  apply IHre_eq1 in H1.
  rewrite H1.
  rewrite H0.
  reflexivity.
  specialize IHre_eq with x0 y0.
  normalize_notations.
  rewrite (IHre_eq H0).
  apply fold_conc_m;auto.
  reflexivity.
  normalize_notations.
  constructor;auto.
  Typeclasses Opaque re_ord.
Qed.

(** Partial derivation of a set of regular expressions *)
Definition pdrv_set (sre:set re)(s:Z) :=
  fold (fun x => union (∂(x,s))) sre {}%set.
Notation "∂S( x , y )" := (pdrv_set x y)(at level 60).

Instance pdrv_set_proper : 
  forall s, Proper(_eq ==> _eq ==> _eq) (fun x0 => union (∂(x0,s))).
Proof.
  Typeclasses Transparent re_ord.
  repeat red;split;intros;
    normalize_notations;
    [rewrite H0,H in H1|
      rewrite H0,H];auto.
  Typeclasses Opaque re_ord.
Qed.  

Lemma pdrv_set_transpose : forall s, 
  transpose Equal (fun x0 => union (∂(x0,s))).
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
  
Add Morphism pdrv_set : pdrv_set_m.
Proof.
  induction x using set_induction;intros.
  unfold pdrv_set.
  rewrite fold_1b;auto.
  rewrite H0 in H.
  rewrite fold_1b;auto.
  reflexivity.
  unfold pdrv_set.
  normalize_notations.
    (*rewrite H1.*)
  generalize(@fold_2 re _ _ _ x1 x2 x3 
    _ _ Equal_ST {}%set (fun x : re => union (∂(x,y0)))
      (pdrv_set_proper y0) (pdrv_set_transpose y0) H H0);intros.
  rewrite H2.
  assert(Add x3 x1 y).
  apply Add_Equal.
  apply Add_Equal in H0.
  rewrite <- H1.
  rewrite H0.
  reflexivity.
  generalize(@fold_2 re _ _ _ x1 y x3 
    _ _ Equal_ST {}%set (fun x : re => union (∂(x,y0)))
      (pdrv_set_proper y0) (pdrv_set_transpose y0) H H4);intros.
  intros.
  rewrite H5,H3;reflexivity.
Qed.

Lemma pdrv_set_singleton : forall r a, 
  (∂S({r}%set,a))===(∂(r,a)).
Proof.
  intros.
  unfold pdrv_set.
  assert(~r \In {}) by (intro Hr;inv Hr).
  assert(Add r {} {r}) by (apply Add_Equal;vm_compute;auto).
  rewrite ((@fold_2 re _ _ _ {}%set {r}%set r 
    _ _ Equal_ST {}%set (fun x : re => union (∂(x,a)))
      (pdrv_set_proper a) (pdrv_set_transpose a)) H H0);intros.
  rewrite fold_1b;autotc.
  rewrite empty_union_2;autotc.
Qed.

Lemma pdrv_set_empty : forall a,
  ∂S({},a)==={}.
Proof.
  intros;unfold pdrv_set;rewrite fold_1b;autotc.
Qed.
  
Lemma In_pdrv_set : forall s x a,
  x \In ∂S(s,a) -> exists y, y \In s /\ x \In ∂(y,a).
Proof.
  induction s using set_induction;intros.
  unfold pdrv_set in H0;rewrite fold_1b in H0;autotc;inv H0.
  unfold pdrv_set in H1;
    rewrite (@fold_2 re _ _ _ s1 s2 x _ _ Equal_ST {}%set _
      (pdrv_set_proper a) (pdrv_set_transpose a) H H0) in H1.
  simpl in H1;apply union_iff in  H1;destruct H1.
  exists x;split;autotc;apply H0;eauto.
  apply IHs1 in H1;destruct H1 as [y [H1 H2]].
  exists y;split;autotc;apply H0;auto.
Qed.

Lemma In_pdrv_in_pdrv_set : forall s x y a,
    y \In ∂(x,a) -> x \In s -> y \In ∂S(s,a).
Proof.
  induction s using set_induction;intros.
  elim (H x);auto.
  rewrite (@fold_2 re _ _ _ s1 s2 x _ _ Equal_ST {}%set _
      (pdrv_set_proper a) (pdrv_set_transpose a) H H0). 
  apply H0 in H2;destruct H2.
  rewrite H2;apply union_2;auto.
  apply union_3;apply (IHs1 _ _ _ H1 H2).  
Qed.

(** Monotonicity of the set derivative w.r.t. a symbol [a] *)
Lemma pdrv_contained : 
  forall x y a,
    x[<=]y -> ∂S(x,a)[<=]∂S(y,a).
Proof.
  induction x using set_induction;intros.
  red;intros;unfold pdrv_set in H1;rewrite fold_1b in H1;autotc;inv H1. 
  
  red;intros;unfold pdrv_set in H2.
  apply((@fold_2 re _ _ _ x1 x2 x3 
    _ _ Equal_ST {}%set (fun x : re => union (∂(x,a))))) in H2;autotc.
  apply union_iff in H2;destruct H2.
  eapply In_pdrv_in_pdrv_set;eauto;apply H1;apply H0;auto.
  apply IHx1.
  red;intros;apply H1;apply H0;auto.
  apply H2.
Qed.
  
Hint Resolve 
  pdrv_set_singleton 
  pdrv_set_empty 
  In_pdrv_set 
  In_pdrv_in_pdrv_set : lgs.
  
(** Operations on sets of partial derivatives *)
Lemma pdrv_set_add : 
  forall s x a,
    ∂S((add x s),a) === (∂(x,a)++∂S(s,a)).
Proof.
  induction s using set_induction;intros.
  generalize H;intro H1;apply empty_is_empty_1 in H1.
  rewrite H1.
  rewrite pdrv_set_empty;auto with sets.
  
  apply Add_Equal in H0;split;intros.
  rewrite H0 in H1;apply In_pdrv_set in H1;do 2 destruct H1.
  apply add_iff in H1;destruct H1.
  rewrite H1;apply union_2;auto.

  apply add_iff in H1;destruct H1;apply union_3.
  rewrite H0;apply IHs1;apply union_2;rewrite H1;autotc.
  eapply In_pdrv_in_pdrv_set with x1;autotc. 
  apply Add_Equal in H0;apply H0;autotc.

  apply union_1 in H1;destruct H1.
  eapply In_pdrv_in_pdrv_set;eauto;apply add_1;autotc.
    
  apply In_pdrv_set in H1;do 2 destruct H1.
  eapply In_pdrv_in_pdrv_set;eauto;apply add_2;autotc.
Qed.
  
Lemma pdrv_set_union : forall s1 s2 a,
  ∂S(s1++s2,a)===∂S(s1,a)++∂S(s2,a).
Proof.
  induction s1 using set_induction;intros.
  apply empty_is_empty_1 in H;rewrite H, pdrv_set_empty, empty_union_1, empty_union_1;autotc.
  
  split_eq. 
  apply In_pdrv_set in H1;do 2 destruct H1;apply union_1 in H1;destruct H1.
  apply Add_Equal in H0;rewrite H0, add_union_singleton in H1;apply union_1 in H1;destruct H1.
  apply singleton_1 in H1;rewrite H0, pdrv_set_add;do 2 apply union_2;rewrite H1;auto.
  
  rewrite H0, pdrv_set_add;apply union_2;apply union_3;
    apply (In_pdrv_in_pdrv_set _ _ _ _ H2 H1).

  apply union_3. eapply In_pdrv_in_pdrv_set;eauto.
  apply Add_Equal in H0;rewrite H0,union_add,pdrv_set_add.
  rewrite H0, pdrv_set_add in H1.
  rewrite IHs1_1;autotc.
  apply union_iff in H1;destruct H1.
  apply union_iff in H1;destruct H1.
  apply union_2;auto.
  apply union_3;apply union_2;auto.
  do 2 apply union_3;auto.
Qed.




(** * Correctness of partial derivative *)

Section PdrvCorrectAux_Conc.
  Variables (r1 r2 : re) (a:Z).
  Hypothesis (IHr1 : forall a : Z, L[∂(r1, a)] ∼ r1 %Lq a)
             (IHr2 : forall a : Z, L[∂(r2, a)] ∼ r2 %Lq a).
  
  Lemma pdrv_correct_conc_aux_1 :
    ε(r1) = false -> L[(∂(r1, a)) ⊙ r2] ∼ r1 • r2 %Lq a.
  Proof.
    intro e;rewrite LangOfFset_dsr.
    pose proof (not_eps_not_in_l _ e).
    rewrite (LQ_conc_aux_1 (re2rel r1) r2 a H).
    rewrite IHr1;autotc.
  Qed.

  Lemma pdrv_correct_conc_aux_2 :
    ε(r1) = true -> L[((∂(r1, a)) ⊙ r2) ++ ∂(r2, a)] ∼ r1 • r2 %Lq a.
  Proof.
    intro e;pose proof (null_eps_in_l _ e);rewrite SreL_union;clear e.
    rewrite (LQ_conc_aux_2 (re2rel r1) r2 a H), IHr2.
    apply union_l_m;autotc.
    rewrite LangOfFset_dsr,IHr1;autotc.
  Qed.

End PdrvCorrectAux_Conc.

Lemma pdrv_correct_aux_star : 
  forall (r : re)(a:Z),
    L[∂(r, a)] ∼ r %Lq a ->  L[(∂(r, a)) ▸ r ⋆] ∼ r ∗ %Lq a.
Proof.
  intros;rewrite LangOfFSet_fconc;rewrite H;split_eq.
  inv H0;inversion H0;inversion H4;subst;constructor;simpl in H5;invc H5;
    constructor 1 with (S n);simpl;rewrite app_comm_cons;constructor;auto.
  invc H0;inv H1;revert n H0;induction n;simpl;intros;inv H0.
  destruct(c_of_re_dec r);[apply not_eps_not_in_l in e|apply null_eps_in_l in e].
  destruct (not_null_in_lconc _ _ _ _ _ _ H3 H4 H2 e);subst;rewrite <- app_comm_cons in H2;
    injection H2;intros;subst;constructor;[constructor|constructor 1 with n];auto.
  destruct(eq_dec w1 []).
  inv H5;simpl in H2;rewrite <- H2 in IHn;apply IHn;auto.
  destruct (not_null_in_lconc_2 _ _ _ _ _ _ H3 H4 H2 H5);subst;rewrite <- app_comm_cons in H2;
    injection H2;intros;subst;constructor;[constructor|constructor 1 with n];auto.
Qed.

Lemma pdrv_correct : forall r a, L[∂(r,a)] ∼ r %Lq a.
Proof.
  induction r;simpl;intros;auto with lgs.
 
  rewrite LangOfFSet_empty,LQ_EmptyL;autotc.

  rewrite LangOfFSet_empty,LQ_EpsL;autotc.

  case_eq(compare z a);intros;
    [apply compare_2 in H|apply compare_1 in H|apply compare_3 in H].
  rewrite (LQ_SyL_eq _ _ H),LangOfFSet_singleton;reflexivity.
  apply lt_not_eq in H;rewrite (LQ_SyL_neq _ _ H), LangOfFSet_empty;reflexivity.
  apply lt_not_eq in H;symmetry in H;rewrite (LQ_SyL_neq _ _ H),LangOfFSet_empty;reflexivity.

  rewrite LQ_union,LangOfFSet_union,IHr1,IHr2;reflexivity.

  destruct(c_of_re_dec r1);rewrite e;
    [apply pdrv_correct_conc_aux_1|apply pdrv_correct_conc_aux_2];autotc.

  apply pdrv_correct_aux_star;autotc.
Qed.
  
(** subset of s that accepts the word given as argument *)

Lemma In_SreL_elem : 
  forall (s:set re) (w:word),
    w ∈ L[s] -> exists r:re, r \In s /\ w ∈ (re2rel r).
Proof.
  induction s using set_induction;intros;[invc H0;exists r;auto|
    invc H1;apply H0 in H2;destruct H2;exists r;split;auto;apply H0;auto].
Qed.

Lemma LangOfPdrvSet : 
  forall s a, L[∂S(s,a)] ∼ L[s] %Lq a.
Proof.
  induction s using set_induction;simpl;intros.
  apply empty_is_empty_1 in H;rewrite H,pdrv_set_empty,<-SreL_empty;simpl;rewrite LQ_EmptyL;auto.
  apply Add_Equal in H0;rewrite H0,add_union_singleton,pdrv_set_union,SreL_union,SreL_union,
                           pdrv_set_singleton,pdrv_correct,SreL_singleton,IHs1,LQ_union;autotc.
Qed.

Lemma SL_dsr_re0 : 
  forall s, L[s⊙0] ∼ L[{}%set].
Proof.
  intro;simpl;autotc.
Qed.

Hint Rewrite SL_dsr_re0 : lset.

Lemma LQw_single : 
  forall (r:re) a, r %Lqw (a::nil) ∼ r %Lq a.
Proof.
  intros;split_eq;inversion_clear H;constructor;autotc.
Qed.

  (** Partial derivatives were extended to words and defined by [pdrv_iw]. This function accepts an [re] and a term of type [iword]
     to calculate such derivatives. Note that, altought in the classical definition, the derivation contains as argument a simple word,
     we had to first wrap such words into the type [iword], which are lists defined from right-to-left, to smooth the encoding and proofs
     we needed. *)

Require Import ilist.

Reserved Notation "∂⌝( x , y )" (at level 60).
Fixpoint pdrv_iw (sre:set re)(w:ilist) : set re :=
  match w with
    | inil => sre
    | icons xs x => ∂S(∂⌝(sre,xs),x)
  end
  where "∂⌝( x , y )" := (pdrv_iw x y).

Functional Scheme pdrv_iw_ind := Induction for pdrv_iw Sort Prop.
Functional Scheme pdrv_iw_rec := Induction for pdrv_iw Sort Set.

(** Simple/base properties *)
Lemma pdrv_iw_sy_icons : forall w r s,
  ∂⌝(s,(w <:: r)) === ∂S(∂⌝(s,w),r).
Proof.
  simpl;auto.
Qed.

Lemma pdrv_iw_sy_nil : forall s,
  ∂⌝(s,<[])===s.
Proof.
  auto.
Qed.

Lemma pdrv_iw_empty : forall w,
  ∂⌝({},w)==={}%set.
Proof.
  induction w;simpl;autotc;rewrite IHw, pdrv_set_empty;autotc.
Qed.

Add Morphism pdrv_iw : pdrv_iw_m.
Proof.
  intros;leibniz H0;subst;revert y0 x y H.
  induction y0;simpl;intros;autotc;rewrite (IHy0 _ _ H);reflexivity.
Qed.

(** wprdv expansion by concatenation of two words *)
Lemma pdrv_iw_app : 
  forall w w' s, ∂⌝(s,(w <++ w')) === ∂⌝(∂⌝(s,w),w').
Proof.
  induction w';simpl;intros;autotc;rewrite IHw';reflexivity.
Qed.

Lemma pdrv_iw_union : 
  forall w s1 s2, ∂⌝(s1++s2,w) === (∂⌝(s1,w)++∂⌝(s2,w)).
Proof.
  induction w;simpl;autotc;intros;rewrite IHw,<- pdrv_set_union;reflexivity.
Qed.

(** Existance of elements *)

Lemma in_pdrv_iw_pdrv : 
  forall s w x, x \In ∂⌝(s,w) -> exists y, y \In s /\ x \In ∂⌝({y}%set,w).
Proof.
  induction s using set_induction;simpl;intros.
  rewrite (empty_is_empty_1 H), pdrv_iw_empty in H0;inv H0.

  apply Add_Equal in H0;rewrite H0,add_union_singleton,pdrv_iw_union in H1;eapply union_1 in H1.
  destruct H1.
  exists x;split;auto.
  rewrite H0;apply add_1;reflexivity.
  apply IHs1 in H1;destruct H1 as [y [H2 H3]];exists y;split;autotc;rewrite H0;apply add_2;auto.
Qed.

Lemma iw_pdrv_in_pdrv : 
  forall w s x y, y \In s ->  x \In ∂⌝({y}%set,w) -> x \In ∂⌝(s,w).
Proof.
  induction w ;simpl;intros.
  apply singleton_1 in H0;rewrite <- H0;autotc.
  apply In_pdrv_set in H0;destruct H0 as [x0 [H1 H2]];apply IHw with (x:=x0) in H;auto;
    eapply In_pdrv_in_pdrv_set;eauto.
Qed.

Lemma pdrv_set_comp : 
  forall s x a0 a1, x \In ∂S(∂S(s,a1),a0) -> x \In ∂⌝(s,((<[]<::a1)<::a0)).
Proof.
  autotc.
Qed.

(** Finally, the definition [wpdrv] uses [pdrv_iw] but first transforms an [ilist] into its corresponding [word] type. *)

Definition wpdrv (r:re)(w:list Z) :=
  ∂⌝({r}%set,list_to_ilist w).
Notation "∂w( x , y )" := (wpdrv x y)(at level 60).

  (** Derivation of a single regular expression by a word *)
Definition wpdrv_set (s:set re)(w:list Z) := ∂⌝(s,<@ w).

Notation "∂wS( x , y )" := (wpdrv_set x y)(at level 60).

Add Morphism wpdrv with signature _eq ==> _eq ==> Equal as wpdrv_m.
Proof.
  induction 2;unfold wpdrv;simpl.
  rewrite H;reflexivity.
  do 2 rewrite pdrv_iw_app.
  apply pdrv_iw_m;unfold wpdrv;normalize_notations;autotc;[|rewrite H1];autotc.
  apply pdrv_iw_m;normalize_notations. 
  apply singleton_m;auto. 
  rewrite H0;auto.
Qed.

Add Morphism wpdrv_set with signature Equal ==> _eq ==> Equal as wpdrv_set_m.
Proof.
  unfold wpdrv_set;intros;normalize_notations;rewrite H,H0;autotc.
Qed.

Add Morphism wpdrv_set with signature Subset ++> _eq  ++> Subset 
  as wpdrv_set_subset.
Proof.
  induction 2;simpl;unfold wpdrv_set in *;simpl;autotc.
  red;intros;normalize_notations.
  apply in_pdrv_iw_pdrv in H2;destruct H2 as [a1 [H3 H4]].
  eapply iw_pdrv_in_pdrv;eauto;rewrite H0,H1 in H4;auto.
Qed.

Lemma wpdrv_nil : forall r, 
  ∂w(r,[])==={r}%set.
Proof.
  autotc.
Qed.

Lemma wpdrv_set_nil : forall s,
  ∂wS(s,[])===s.
Proof.
  autotc.
Qed.

Lemma wpdrv_set_singleton : forall s w,
  ∂wS({s}%set,w) === ∂w(s,w).
Proof.
  induction w;simpl;[rewrite wpdrv_set_nil,wpdrv_nil|];autotc.
Qed.

Lemma wpdrv_set_empty : forall w,
  ∂wS({},w)==={}%set.
Proof.
  intros;unfold wpdrv_set;simpl;rewrite pdrv_iw_empty;reflexivity.
Qed.

Lemma wpdrv_sy_nil : forall r x,
  ∂w(r,[x])===∂S({r}%set,x).
Proof.
  autotc.
Qed.

Lemma wpdrv_set_app : forall s w1 w2, 
  ∂wS(s,w1++w2) === ∂wS(∂wS(s,w1),w2).
Proof.
  induction w1;simpl;intros;autotc.
  unfold wpdrv_set in *;simpl;repeat rewrite pdrv_iw_app.
  rewrite IlistFromListConc,pdrv_iw_app;autotc.
Qed.

Lemma wpdrv_corr : forall w r, 
  L[∂⌝(r,w)] ∼ L[r] %Lqw (@>w).
Proof.
  induction w;simpl;intros;autotc.
  rewrite LQw_nil;autotc.
  rewrite LangOfPdrvSet, IHw,LQw_split,LQw_sy_LQ_eq;autotc.
Qed.

Lemma wpdrv_correct : forall w r, L[∂w(r,w)] ∼ r %Lqw w.
Proof.
  intros;unfold wpdrv;rewrite wpdrv_corr,SreL_singleton,ListFromIlist;autotc. 
Qed.

Lemma word_in_pdrv : forall w (r:re), 
  w ∈ (re2rel r) -> εs(∂w(r,w)) = true.
Proof.
  intros;apply w_in_Lang_eq_nil_in_LQw in H;apply wpdrv_correct in H;auto with res.
Qed. 

Lemma word_in_pdrv_true : forall w (r:re), 
  εs(∂w(r,w)) = true ->  w ∈ (re2rel r).
Proof.
  intros;apply nil_in_LQw_eq_w_in_lang;eapply wpdrv_correct;auto with res.
Qed.

Lemma word_not_in_pdrv : forall w (r:re), 
  ~w ∈ (re2rel r) -> εs(∂w(r,w)) = false.
Proof.
  intros;apply not_true_is_false;intro;apply H;apply word_in_pdrv_true;auto.
Qed.

Lemma word_not_in_pdrv_true : forall w (r:re), 
  εs(∂w(r,w)) = false ->  ~w ∈ (re2rel r).
Proof.
  intros w r H H1;apply  word_in_pdrv in H1;congruence.
Qed.

(** %\subsubsection{Mirkin's construction and finiteness of partial derivatives}% 
   Formalization of support *)
  
Fixpoint PI (r:re) : set re :=
  match r with
    | 0    => {}
    | 1    => {}
    | re_sy _ => {1}
    | x + y  => (PI x)++(PI y)
    | x · y  => ((PI x)⊙y)++(PI y)
    | x⋆   => (PI x)⊙(x⋆)
  end.

Functional Scheme PI_ind := Induction for PI Sort Prop.
Functional Scheme PI_rec := Induction for PI Sort Set.

Add Morphism PI : PI_m.
Proof.
  intros;apply re_leibniz in H;subst;reflexivity.
Qed.

Lemma in_pdrv_0 : ~exists y, y \In (PI 0).
Proof.
  intro H;destruct H as [y Nin];inv Nin.
Qed.

Lemma in_pdrv_1 : ~exists y, y \In (PI 1).
Proof.
  intro H;destruct H as [y Nin];inv Nin.
Qed.

Lemma in_pdrv_sy : forall y s, y \In (PI (re_sy s)) -> y === 1.
Proof.
  intros;apply singleton_1 in H;autotc.
Qed.
  
Lemma in_pdrv_union : 
  forall x y z, 
    x \In (PI (y + z)) -> x \In (PI y) \/ x \In (PI z).
Proof.
  intros;apply union_1 in H;autotc.
Qed.

Lemma in_pdrv_conc : 
  forall x y z, 
    Not_0_1 z -> x \In (PI (y · z)) -> x \In (PI z) \/ exists y', x === y' · z /\ y' \In (PI y).
Proof.
  intros;simpl in H0;apply union_iff in H0;destruct H0;auto;
  apply in_dsr in H0;auto;destruct H0 as [y' [H11 H12]];right;exists y';intuition.
Qed.

Lemma in_pdrv_star : 
  forall x y, 
    x \In (PI (y⋆)) -> exists y', x === y' · (y⋆) /\ y' \In (PI y).
Proof.
  intros;simpl in H;apply in_dsr_re_star in H;destruct H as [y' [H11 H12]];exists y';autotc.
Qed.

(** Transitivity of the PI function *)

Typeclasses Transparent re_ord.

Lemma PI_trans : forall x y, 
  y \In (PI x) -> forall z, z \In (PI y) -> z \In (PI x).
Proof.
  induction x;simpl;intros;try (now(inv H)).
  apply singleton_1 in H;rewrite <- H in H0;simpl in H0;inv H0.
  apply union_1 in H;destruct H;[apply union_2|apply union_3];eauto.
  destruct (dsr_cases (PI x1) x2).
  rewrite H1 in H;apply union_iff in H;destruct H;[inversion H|apply union_3;eapply IHx2;eauto].
  destruct H1. 
  rewrite H1 in H |- *;apply union_iff in H;destruct H;
    [apply union_2;eapply IHx1|apply union_3;eapply IHx2];eauto.
  destruct H1.
  apply union_1 in H;destruct H.
  apply (in_dsr (PI x1) x2 y) in H;auto;destruct H as [t [H3 H4]].
  rewrite H4 in H0;simpl in H0;apply union_1 in H0;destruct H0;autotc.
  apply union_2.
  destruct (in_dsr _ _ _ H1 H) as [z1 [H5 H6]];rewrite H6,H2.
  apply elem_conc_in_fold_conc;eauto.
  apply union_3;auto.
  apply union_3;eauto.
    (* kleene's star *)
  apply elem_conc_in_ex in H;destruct H as [t [H1 H2]].
  rewrite H2 in H0;simpl in H0;apply union_1 in H0;destruct H0.
  apply elem_conc_in_ex in H;destruct H as [x0 [H3 H4]];rewrite H4.
  apply elem_conc_in_fold_conc;eauto.
  assumption.
Qed.
  
Definition PD(r:re) := {r}%set++(PI r).

Global Instance PD_m : Proper(_eq ==> _eq) PD.
Proof.
  repeat red;split_eq;unfold PD in *;apply union_iff in H0;destruct H0;(rewrite H||rewrite <- H);
    try (now (apply union_2;auto));try now(apply union_3;auto).
Qed. 

Lemma PI_upper_bound : forall r, #(PI r) <= |<r>|.
Proof.
  induction r;simpl;auto.
  rewrite union_cardinal_inter;abstract omega.
  rewrite union_cardinal_inter;pose proof (dsr_cardinal (PI r1) r2) as H1;abstract omega.
  rewrite fold_conc_card;assumption.
Qed.
  
Theorem PD_upper_bound : forall r, #(PD r) <= (S |<r>|).
Proof.
  unfold PD;intros;pose proof PI_upper_bound r as H1.
  rewrite union_cardinal_inter, singleton_cardinal;abstract omega.
Qed.

Theorem all_pdrv_in_PI : forall x r, ∂(x,r)[<=](PI x).
Proof.
  induction x;unfold Subset;simpl;intros;try (now(inv H)).
  
  revert H;case_eq(compare z r);intros;(assumption||inversion H0).
  
  apply union_1 in H;destruct H;[apply union_2;apply (IHx1 r)|apply union_3;apply (IHx2 r)];auto.

  destruct(c_of_re_dec x1);rewrite e in H;unfold Subset;intros.
  apply union_2;unfold Subset in IHx1,IHx2.
  destruct (dsr_cases (pdrv x1 r) x2) as [H1 | [H1 | H1]];
    [rewrite H1 in H|rewrite H1 in H|];try now(inv H).
    
  destruct(eq_dec x2 0) as [H2 | H2]. 
  rewrite H2 in H1;simpl in H1;rewrite <- H1 in H;inv H.
  destruct(eq_dec x2 1) as [H3|H3];try rewrite H3 in H1 |- *.
  simpl in *;eauto.
  rewrite <- H1 in H;eapply in_dsr in H;auto;destruct H.
  destruct H;rewrite H0;apply elem_conc_dsr_in;eauto.
  destruct H1.
  apply in_dsr in H;auto;destruct H.
  destruct H. rewrite H2;apply elem_conc_dsr_in;eauto.
  apply union_1 in H;destruct H.
  apply union_2;destruct(eq_dec x2 0).
  rewrite H0 in H;simpl in H;inversion H.
  destruct(eq_dec x2 1);try rewrite H1 in H |- *;simpl in *.
  apply (IHx1 _ _ H).
  apply in_dsr in H;auto;destruct H.
  destruct H;rewrite H2.
  apply elem_conc_dsr_in;eauto;apply (IHx1 _ _ H).
  apply union_3;apply (IHx2 _ _ H).
    
  apply elem_conc_in_ex with (r:=re_star x) in H.
  destruct H as [y [H11 H12]];rewrite H12;apply elem_conc_in_fold_conc;apply IHx with (r:=r);auto.
Qed.
  
  
Lemma PD_trans : 
  forall x y, y \In (PD x) -> forall z, z \In (PD y) -> z \In (PD x).
Proof.
  intros;unfold PD in *;apply union_1 in H0;destruct H0.
  apply singleton_1 in H0;subst;auto;rewrite <- H0;auto.
  apply union_1 in H;destruct H;[apply singleton_1 in H;rewrite H|];auto.
  apply union_3;auto.
  apply union_3;eapply PI_trans;eauto.
Qed.
  
Lemma all_PI_in_PD : forall r x, 
  x \In (PI r) -> x \In (PD r).
Proof.
  intros;unfold PD;apply union_3;auto.
Qed.

(** * Partial derivatives w.r.t words belong to PD *)

Lemma all_wpdrv_in_PD :
  forall w x r, x \In (∂⌝({r}%set,w)) -> x \In PD(r).
Proof.
  induction w.
  simpl;unfold PD;intros;apply union_2;auto.
  simpl;intros;eapply In_pdrv_set in H;do 2 destruct H.
  apply IHw in H;unfold PD in *|- *.
  apply union_1 in H;destruct H.
  apply singleton_1 in H;apply all_pdrv_in_PI in H0;apply union_3;apply(PI_m _ _ H) in H0;auto.
  apply all_pdrv_in_PI in H0;apply union_3;eapply PI_trans;eauto.
Qed.

Require Import SetConstructs.

Definition PIPow(r1 r2:re) := cart_prod (powerset(PI(r1))) (powerset (PI(r2))).
Definition PDPow(r1 r2:re) := cart_prod (powerset(PD(r1))) (powerset (PD(r2))).

Lemma all_pdrv_pairs_in_PIPow : forall r1 r2 a b, 
  (∂(r1,a),∂(r2,b)) \In PIPow r1 r2.
Proof.
  intros;unfold PIPow;apply cart_prod_1;apply powerset_spec;apply all_pdrv_in_PI.
Qed.
  
Lemma all_pdrv_pairs_in_PDPow : forall r1 r2 a b, 
  (∂w(r1,a),∂w(r2,b)) \In PDPow r1 r2.
Proof.
  intros;unfold PDPow;apply cart_prod_1;apply powerset_spec;unfold wpdrv;red;intros;
    apply all_wpdrv_in_PD in H;auto.
Qed.
 

Add Morphism PDPow : PDPow_m.
Proof.
  intros;apply cart_prod_m;normalize_notations;apply powerset_m;autotc.
  normalize_notations. apply PD_m. rewrite H;autotc. rewrite H0;autotc.
Qed.

Typeclasses Opaque re_ord.

