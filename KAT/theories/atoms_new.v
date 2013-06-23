Require Export NArith.
Require Export base.
Require Import Sets SetInterface SetProperties Relations.
Require Import Vectors.Vector.


(** Boolean strict less-than order on values of type [nat]. *)

Fixpoint ltb (n m:nat) : bool :=
  match n,m with
    | O , S _ => true
    | S k, S l => ltb k l
    | _,_ => false
  end.

(** Some basic properties of [ltb] *)

Proposition ltb0 : forall n, ltb n 0 = false.
Proof.
  induction n;simpl;intros;auto.
Qed.

Proposition ltb_S : forall n, ltb n (S n) = true.
Proof.
  induction n;simpl;eauto.
Qed.

Lemma ltb_correct : forall n m, ltb n m = true -> n < m.
Proof.
  induction n.
  - intros. destruct m. discriminate. omega.
  - simpl. intros. destruct m. 
    + discriminate.
    + apply IHn in H. omega.
Defined.

Lemma ltb_complete : forall n m, n < m -> ltb n m = true.
Proof.
  induction n.
  - intros. destruct m.
    + omega. 
    + auto.
  - intros. inv H.
    + simpl. apply ltb_S.
    + simpl. apply IHn. omega.
Defined.

Lemma ord_lt_correct :
  forall m n, ltb m n = true -> ltb (S m) (S n) = true.
Proof.
  intros.
  apply ltb_correct in H.
  apply ltb_complete.
  abstract(omega).
Qed.

(** * Definition of finite ordinal *)
(** The structure [ord] contains a number a number [m] and a proof involving [ltb] *)

Record ord (n:N) := Ord {nat_of_ord:> N; ord_lt: ltb nat_of_ord n = true }.

(** [O] and [S _] smart constructors for [ord] *)
  
Definition ord0 n : ord (S n) := @Ord  (S n) 0 eq_refl.
Definition ordS n (m:ord n) := @Ord (S n) (S m) ((ord_lt n m)). 

(** * Equality and strict orderings over [ord] *)
(** We consider only the underlying natural number, and ignore the proofs. *)

Definition ord_Eq n := 
  fun x y:ord n => @eq nat x y.
  
Definition ord_Lt n := 
  fun (x y:ord n) => (nat_of_ord n x) <<< (nat_of_ord n y).

Definition ord_Cmp n := 
  fun (x y:ord n) => _cmp (nat_of_ord n x) (nat_of_ord n y).


(** Bureaucratic instances to register [ord] as an ordered typ *)

Instance ord_Eq_equiv : forall n, Equivalence (ord_Eq n).
Proof.
  intros;constructor;repeat red;auto.
  intros;inversion H;inversion H0;auto.
Qed.

Instance ord_Lt_trans : forall n, Transitive (ord_Lt n).
Proof.
  intro;repeat red;intros.
  inversion H;inversion H0;subst;now(omega).
Qed.

Proposition ord_Lt_irrefl n :
  forall  x y,
    ord_Lt n x y -> ~ord_Eq n x y.
Proof.
  intros.
  intro.
  inversion H.
  - inversion H0;omega.
  - inversion H0;omega.
Qed.

Instance ord_StrictOrder : forall n, StrictOrder (ord_Lt n) (ord_Eq n).
Proof.
  intro;constructor;autotc.
  intros;apply ord_Lt_irrefl;auto.
Qed.

Lemma ord_Eq_unique :  
  forall n (x y:ord n), ord_Eq n x y -> x = y.
Proof.
  unfold ord_Eq.
  destruct x. destruct y.
  simpl.
  intros.
  subst.
  f_equal.
  eapply Eqdep_dec.UIP_dec.
  decide equality.
Qed.

Ltac ord_eq_un H := apply ord_Eq_unique in H;subst.

Instance ord_UStrict : forall n : nat, StrictOrder (ord_Lt n) eq.
Proof.
  intro.
  constructor;autotc.
  intros.
  unfold ord_Lt in H.
  intro.
  rewrite H0 in H.
  order.
Qed.

Instance ord_UOrderedType : forall n, UsualOrderedType (ord n) :=
  { SOT_lt  := ord_Lt n ;
    SOT_cmp := ord_Cmp n }.
Proof.
  intros.
  case_eq(ord_Cmp n x y);intros;constructor.
  - apply compare_2,ord_Eq_unique in H;auto.
  - apply compare_1 in H;unfold ord_Lt;auto.
  - apply compare_3 in H;unfold ord_Lt;auto.
Defined.

(*Definition ordS_map n (l:list (ord n)) : list (ord (S n)) := List.map (@ordS n) l.*)
(** Mapping adition to a list of ordinals *)

Definition ordS_mapS n (s:set (ord n)) : set (ord (S n)) := map (@ordS n) s.

(* Fixpoint smaller_ords n  {struct n} : list (ord n) := *)
(*   match n with *)
(*     | 0 => nil *)
(*     | S m => cons (ord0 m) (@ordS_map m (smaller_ords m)) *)
(*   end. *)

(** * Function to generate the set of all ordinals under a natural [n] *)

Fixpoint smaller_ordsS n  {struct n} : set (ord n) :=
  match n with
    | 0 => {}
    | S m => add (ord0 m) (@ordS_mapS m (smaller_ordsS m))
  end.

(* Lemma all_in_smaller_ord :  *)
(*   forall n (x:ord n),  List.In x (smaller_ords n). *)
(* Proof. *)
(*   induction n. *)
(*   - simpl;intros;inv x;pose proof ltb0 nat_of_ord0;congruence. *)
(*   - intros;simpl. right.  unfold ordS_map. *)
(*     destruct x. *)
(*     assert(ltb nat_of_ord0 n = true). *)
(*     simpl in ord_lt0. *)
(*     apply ltb_correct in ord_lt0. *)
(*     apply ltb_complete. *)
(*     omega. *)
(*     Check @Ord . *)

Lemma ord_ind' (P: forall n, ord n -> Prop) 
  (H0: forall n, P (S n) (ord0 n))
  (HS: forall n i, P n i -> P (S n) (ordS n i)): 
  forall n i, P n i.
Proof. 
  induction n.
  - intro i. inv i. pose proof ltb0 nat_of_ord0. congruence. 
  - destruct i as [[|i] Hi].
    replace ({| nat_of_ord := 0; ord_lt := Hi |}) with
      ((ord0 n)). apply H0.
    apply ord_Eq_unique.
    unfold ord0.
    unfold ord_Eq. simpl.
    reflexivity.
    change ({| nat_of_ord := S i; ord_lt := Hi |}) with (@ordS n (@Ord n i Hi)).
    apply HS.
    apply IHn.
Qed.

(* Lemma all_in_smaller_ords :  *)
(*   forall n i,  List.In i (smaller_ords n). *)
(* Proof. *)
(*   induction i using ord_ind'. *)
(*   - simpl. left;auto. *)
(*   - simpl. right. apply List.in_map_iff. exists i. auto. *)
(* Qed. *)

Global Instance ord_S_m : forall n,  Proper (_eq ==> _eq) (ordS n).
Proof.
  repeat red;intros.
  f_equal.
  repeat red in H.
  assumption.
Qed.

Lemma all_in_smaller_ordsS : 
  forall n i,  i \In (smaller_ordsS n).
Proof.
  induction i using ord_ind'.
  - simpl. apply add_1. reflexivity. 
  - simpl. apply add_2. apply map_iff. 
    + autotc.
    + exists i. auto.
Qed.

Fixpoint pow2(n:nat):nat :=
  match n with
    | O   => 1
    | S m => 2*pow2 m
  end.


Proposition pow2_geq_1 :
  forall n, 1 <= pow2 n .
Proof.
  induction n;simpl;auto with arith.
Qed.

(** Evaluate the nth-bit of the natural number wrapped in the ordinal *)

Definition nth_bit(m:nat)(k:ord m)(n:nat):bool := N.testbit_nat (N.of_nat k) n.
