Require Export base.
Require Export ZArith.

(** * Right-to-left defined lists *)

Inductive ilist : Type :=
| inil  : ilist 
| icons : ilist -> Z -> ilist.

Delimit Scope ilist_scope with ilist.
Open Scope ilist_scope.

Notation "<[]" := inil.
Notation "<[ x ]" := (icons <[] x).
Infix "<::" := icons (at level 60, right associativity).

(** * Characterization of [ilist] as an instance of [OrderedType] *)

Inductive ilist_eq : ilist -> ilist -> Prop :=
| ilist_eq_nil : ilist_eq <[] <[]
| ilist_eq_icons :
    forall a a' l l', _eq a a' -> ilist_eq l l' ->
                      ilist_eq (icons l a) (icons l' a').

Lemma ilist_eq_leibniz : forall x y,
                           ilist_eq x y -> x = y.
Proof.
  induction 1.
  reflexivity.
  rewrite IHilist_eq.
  rewrite H.
  reflexivity.
Qed.

Ltac leibniz H :=
  apply ilist_eq_leibniz in H.

Ltac leibniz_all :=
  repeat (match goal with
            | [H: _eq _ _ |- _ ] => leibniz H
            | [H: _ === _ |- _ ] => leibniz H
            | _ => idtac
          end).

Hint Constructors ilist_eq : ilist_scope .

Program Instance ilist_Equivalence `(Equivalence Z _eq) :
  Equivalence (ilist_eq).
Next Obligation.
  red.
  induction x;auto with ilist_scope.
Qed.
Next Obligation.
  red.
  induction 1;auto with ilist_scope.
Qed.
Next Obligation.
  red.
  induction x;destruct y;intros;auto.
  inversion H0.
  inversion H0.
  inversion_clear H0.
  inversion_clear H1;normalize_notations.
  constructor;auto.
  rewrite H2;auto.
  eapply IHx with y;auto.
Qed.

Typeclasses Opaque ilist_Equivalence.

Inductive ilist_lt : ilist -> ilist -> Prop :=
| ilist_lt_inil :
    forall a l, ilist_lt inil (icons l a)
| ilist_lt_icons_1 :
    forall a a' l l', _lt a a' -> ilist_lt (icons l a) (icons l' a')
| list_lt_cons_2 :
    forall a a' l l', _eq a a' -> ilist_lt l l' ->
                      ilist_lt (icons l a) (icons l' a').

Hint Constructors ilist_lt : ilist_scope.

Program Instance ilist_StrictOrder :
  OrderedType.StrictOrder ilist_lt ilist_eq.
Next Obligation.
  red.
  induction x;destruct y;intros;auto with ilist_scope.
  inversion_clear H0;auto with ilist_scope.
  inversion_clear H.
  inversion_clear H.
  inversion_clear H0.
  constructor;auto with typeclass_instances.
  normalize_notations.
  etransitivity;eauto.
  constructor 2;auto.
  normalize_notations.
  rewrite H in H1;auto.
  inversion_clear H0.
  constructor 2;normalize_notations.
  rewrite <- H1 in H.
  assumption.
  normalize_notations.
  constructor 3;auto.
  rewrite H1.
  assumption.
  eapply IHx.
  apply H2.
  assumption.
Qed.
Next Obligation.
  revert x y H.
  induction 1.
  intro.
  inversion H.
  intro.
  inversion H0.
  subst.
  normalize_notations.
  rewrite H4 in H.
  order.
  intro.
  apply IHilist_lt.
  inversion_clear H1;auto.
Qed.
  
Program Instance ilist_UsualStrictOrder :
  OrderedType.StrictOrder (@ilist_lt ) (@Logic.eq _).
Next Obligation. (* irreflexivity *)
  intro E; inversion E; subst; clear E.
  revert y H; induction y; intro H; inversion H; subst; auto; order.
Qed.

Fixpoint ilist_compare (x y : ilist) :=
  match x, y with
    | <[], <[] => Eq
    | <[], _<::_ => Lt
    | _<::_, <[] => Gt
    | l<::a, l'<::a' =>
      match a =?= a' with
        | Eq => ilist_compare l l'
        | Lt => Lt
        | Gt => Gt
      end
  end.

Program Instance ilist_OrderedType: OrderedType (ilist) := 
  {
    _eq := ilist_eq ;
    _lt := ilist_lt;
    _cmp := ilist_compare;
    OT_Equivalence := ilist_Equivalence _;
    OT_StrictOrder := ilist_StrictOrder 
  }.
Next Obligation.
  revert y; induction x; destruct y; simpl; try (do 2 constructor).
  destruct (compare_dec z z0); try do 2 constructor; auto.
  destruct (IHx y); constructor.
  constructor 3; auto.
  constructor 2; auto.
  constructor 3; auto; symmetry; auto.
Qed.

Program Instance ilist_UsualOrderedType :
  UsualOrderedType ilist := {
                             SOT_lt := ilist_lt (*_lt Logic.eq ;*);
                             SOT_cmp := ilist_compare;
                             SOT_StrictOrder := ilist_UsualStrictOrder
                           }.
Next Obligation.
  revert y; induction x; destruct y; simpl; try (do 2 constructor).
  destruct (compare_dec z z0); try do 2 constructor; auto.
  destruct (IHx y); constructor.
  constructor 3; auto.
  congruence.
  constructor 3; auto; symmetry; auto.
Qed.

Typeclasses Opaque ilist_OrderedType ilist_UsualOrderedType.

Program Instance icons_proper : Proper (_eq ==> _eq ==> _eq) icons.
Next Obligation.
  repeat red.
  intros;constructor;auto with ilist_scope typeclass_instances.
Qed.

Reserved Notation "x <++ y" (at level 60,right associativity).
Fixpoint ilist_app (a b:ilist){struct b} : ilist :=
  match b with
    | <[] => a 
    | x<::y => (a <++ x)<::y
  end
    where "x <++ y" := (ilist_app x y).

Instance ilist_app_proper : Proper (_eq ==> _eq ==> _eq) ilist_app.
Proof.
  repeat red.
  induction 2.
  normalize_notations;auto with typeclass_instances.
  constructor;auto.
Qed.

Lemma ilist_ilist_nil_app : forall l, l === <[] <++ l.
Proof.
  induction l;simpl;auto.
  constructor;auto.
Qed.

Lemma ilist_ilist_app_inil : forall l,  <[] <++ l === l.
Proof.
  induction l;simpl;auto.
  constructor;auto.
Qed.
  
Lemma ilist_inil_split : forall l1 l2, 
                           <[] === l1 <++ l2 -> l1 === <[] /\ l2 === <[].
Proof.
  induction l1;destruct l2;split;intros;simpl in *;auto.
  inversion_clear H.
  inversion H.
  inversion H.
Qed.

Lemma ilist_neq_ilist_icons : forall l a,
                                ~(l === l<::a).
Proof.
  induction l;simpl;intros;intro.
  inversion H.
  inversion_clear H.
  specialize IHl with a.
  normalize_notations.
  rewrite H0 in H1.
  contradiction.
Qed.

Lemma ilist_not_inil_ex : forall l,
                            l =/= <[] -> exists a,exists l', l === l'<::a.
Proof.
  induction l;intros.
  elim H;auto.
  exists z.
  exists l;auto.
Qed.

Hint Resolve 
     ilist_ilist_nil_app
     ilist_ilist_app_inil
     ilist_inil_split 
     ilist_neq_ilist_icons 
     ilist_not_inil_ex : ilist_scope.

Lemma ilist_ilist_app_assoc : forall w1 w2 w3, 
                                w1 <++ (w2 <++ w3) === (w1 <++ w2) <++ w3.
Proof.
  induction w3;simpl;auto.
  constructor;auto.
Qed.

Lemma ilist_icons_ilist_app_2 : forall u u0 a, 
                                  (u <++ u0)<::a === u <++ (u0 <::a).
Proof.
  induction u0;simpl;intros;auto.
Qed.

Lemma ilist_icons_ilist_app : forall x y w, 
                                (x<::y) <++ w === x <++ ((<[]<::y) <++ w).
Proof.
  induction x;
  intros;simpl;auto with ilist_scope.
  destruct w;simpl;auto with ilist_scope.
  constructor;auto.
  normalize_notations.
  rewrite ilist_ilist_app_assoc.
  simpl.
  reflexivity.
Qed.

Hint Resolve 
     ilist_ilist_app_assoc
     ilist_icons_ilist_app_2
     ilist_icons_ilist_app : ilist_scope.

Reserved Notation "x ^p< n" (at level 60). 
Fixpoint IWordPower (x:ilist)(n:nat) := 
  match n with
    | O => <[]
    | S n => (x ^p< n) <++ x
  end
    where "x ^p< n" := (IWordPower x n).

Instance IWordPower_proper : Proper (_eq ==> _eq ==> _eq) IWordPower.
Proof.
  repeat red.
  induction x0;simpl;intros.
  rewrite <-H0.
  simpl;auto with ilist_scope.
  rewrite <- H0.
  simpl.
  eapply ilist_app_proper;auto with typeclass_instances.
  apply IHx0;auto.
Qed.

(** lists to ilists conversion function *)

Reserved Notation "<@ a" (at level 50).
Fixpoint list_to_ilist (a:list Z) : ilist :=
  match a with
    | nil => <[]
    | a::xs => (<[]<::a) <++ (<@ xs)
  end
    where "<@ a" := (list_to_ilist a).

Instance list_to_ilist_m : Proper (_eq ==> _eq) list_to_ilist.
Proof.
  repeat red.
  induction 1 .
  reflexivity.
  simpl.
  normalize_notations.
  rewrite H.
  rewrite IHlist_eq.
  reflexivity.
Qed.
  
(** ilists to lists conversion function *)
Reserved Notation "@> a" (at level 50).
Fixpoint ilist_to_list (a:ilist) : list Z :=
  match a with
    | <[] => nil (A:=Z)
    | l<::x => app (@> l) (x::nil)
  end
    where "@> a" := (ilist_to_list a).

Instance ilist_to_list_m : Proper (_eq ==> _eq) ilist_to_list.
Proof.
  repeat red.
  induction 1 .
  reflexivity.
  simpl.
  normalize_notations;auto with typeclass_instances.
  induction IHilist_eq.
  inv H;autotc.
  do 2 rewrite <- app_comm_cons.
  constructor;auto.
Qed.

Theorem exListFromIlist : forall w, exists w', w' === <@ w.
Proof.
  induction w.
  simpl.
  exists inil;reflexivity.
  simpl.
  destruct IHw as [w' Hw'].
  exists (ilist_app (icons inil a) w').
  apply ilist_app_proper;auto.
Qed.

(** Polymorphic list general rewriting support por append and construction *)

Instance app_m : Proper (_eq ==> _eq ==> _eq) (@app Z).
Proof.
  repeat red.
  induction 1;simpl;intros;auto with typeclass_instances.
  normalize_notations.
  constructor;auto.
Qed.

Instance cons_m : Proper (_eq ==> _eq ==> _eq) (@cons Z).
Proof.
  repeat red.
  induction 1;simpl;intros;auto with typeclass_instances.
  constructor;auto.
Qed.

Theorem exIlistFromList : forall w', exists w, w === @> w'.
Proof.
  induction w'.
  simpl.
  exists (@nil Z).
  reflexivity.
  simpl.
  destruct IHw' as [w Hw].
  exists (app w (z::nil)).
  apply app_m;auto.
Qed.

(** Correctness of conversion operations between lists and ilists *)
Typeclasses Transparent ilist_OrderedType ilist_UsualOrderedType  ilist_Equivalence.

Lemma IlistFromListConc : forall w w',
                            <@ (w ++ w') === (<@ w) <++ (<@ w').
Proof.
  induction w.
  intro.
  simpl.
  rewrite ilist_ilist_app_inil.
  reflexivity.
  intros.
  simpl.
  rewrite (IHw w').
  rewrite ilist_ilist_app_assoc.
  reflexivity.
Qed.

Lemma ListFromIlistConc : forall  w' w'', 
                            @> (w' <++ w'') === app (@> w') (@> w'').
Proof.
  induction w''.
  simpl.
  rewrite <- app_nil_end.
  reflexivity.
  simpl.
  rewrite ass_app.
  apply app_m;auto.  
Qed.

Theorem  IlistFromList : forall w', 
                           <@ (@> w') === w'.
Proof.
  induction w'.
  simpl.
  reflexivity.
  simpl.
  rewrite IlistFromListConc.
  rewrite IHw'.
  simpl.
  reflexivity.
Qed.

Theorem ListFromIlist : forall w, @> (<@ w) === w.
Proof.
  induction w.
  simpl.
  reflexivity.
  simpl.
  generalize (ListFromIlistConc (<[] <:: a) (<@ w));intro.
  inv H.
  constructor;auto.
  normalize_notations.
  rewrite <- IHw.
  assumption.
Qed.

Lemma nil2inil : forall w, w === nil -> <@ w === <[].
Proof.
  intros w H;rewrite H;simpl.
  auto.
Qed.

Lemma inil2nil : forall w,  w === <[] -> @> w === nil.
Proof.
  intros.
  rewrite H;simpl.
  reflexivity.
Qed.

Lemma not_nil2inil : forall w, w =/= nil -> <@ w =/= <[].
Proof.
  intros.
  intro.
  apply inil2nil in H0.
  rewrite ListFromIlist in H0.
  contradiction.
Qed.
  
Lemma eq_app_iapp : forall w u v,
                      w === app u v -> <@ w === <@ u <++ <@ v.
Proof.
  intros w u v.
  revert v u w.
  induction v;simpl;intros.
  rewrite <- app_nil_end in H.
  inv H;auto. simpl. normalize_notations.
  rewrite H1;auto.

  replace (app u (a::v)) with (app (app u (a::nil)) v) in H.
  apply IHv in H.
  rewrite H.
  rewrite IlistFromListConc.
  simpl.
  rewrite ilist_ilist_app_assoc.
  simpl.
  reflexivity.
  rewrite app_ass.
  simpl.
  reflexivity.
Qed.

Hint Resolve
     nil2inil
     inil2nil
     IlistFromListConc
     ListFromIlistConc
     ListFromIlist
     IlistFromList
     eq_app_iapp
     not_nil2inil : ilist_scope.

Lemma ilist_eq_dec : forall l1 l2:ilist,
                       {l1 === l2}+{l1 =/= l2}.
Proof.
  intros.
  case_eq(compare l1 l2);intros.
  left.
  apply compare_2 in H.
  assumption.
  right.
  apply compare_1 in H.
  apply lt_not_eq in H.
  assumption.
  apply compare_3 in H.
  apply gt_not_eq in H.
  right;auto.
Qed.

(** * Some standard functions over [list], adaped to [ilist] *)

(** Function for element containance in a [ilist] *)

Fixpoint iIn (a:Z) (l:ilist) : Prop :=
  match l with
    | inil => False
    | m<::b => b === a \/ iIn a m
  end.

(** The length of an [ilist] *)

Fixpoint ilength(w:ilist):nat :=
  match w with 
    | inil => 0
    | icons y a => S (ilength y)
  end.

Instance ilength_m : Proper (_eq ==> eq) ilength.
Proof.
  repeat red.
  induction x;simpl;intros.
  inversion H.
  simpl.
  reflexivity.
  inversion_clear H.
  simpl.
  apply IHx in H1.
  rewrite H1.
  reflexivity.
Qed.

(**  Properties of the [ilength] function. *)

Lemma ilength_sum_one : forall l' a,
                          ilength ((<[] <:: a) <++ l') = S (ilength l').
Proof.
  induction l';simpl;intros.
  reflexivity.
  rewrite IHl'.
  reflexivity.
Qed.

Lemma ilength_sum : forall l l',
                      ilength (l <++ l') = ilength l + ilength l'.
Proof.
  induction l;simpl;intros;auto with arith.
  rewrite <- ilist_ilist_nil_app.
  reflexivity.
  rewrite ilist_icons_ilist_app.
  rewrite IHl.
  rewrite ilength_sum_one;auto with arith.
Qed.

(** Extra properties of the [iapp] function. *)

Lemma iapp_inv_head:
  forall l l1 l2, l1 <++ l === l2 <++ l -> l1 === l2.
Proof.
  induction l; simpl; auto. 
  intros.
  inversion_clear H.
  apply IHl in H1.
  assumption.
Qed.

Lemma iapp_inv_left : forall l l1 l2,
                        l <++ l1 === l <++ l2 -> l1 === l2.
Proof.
  intros l l1 l2; revert l1 l2 l.
  induction l1 as [ | x1 l1]; destruct l2 as [ | x2 l2];
  simpl; auto; intros l H.
  absurd (ilength ((l <++ x2)<::l2) <= ilength l).
  simpl;intro.
  rewrite ilength_sum in H0.
  abstract omega.
  rewrite <- H;auto with arith.
  absurd (ilength ((l <++ x1)<::z) <= ilength l).
  simpl;intro.
  rewrite ilength_sum in H0.
  abstract omega.
  rewrite H;auto with arith.
  leibniz H.
  injection H;intros.
  constructor;auto with typeclass_instances.
  apply l1 with l.
  rewrite H1;reflexivity.
Qed.

