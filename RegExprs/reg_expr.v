Add LoadPath "." as PDCoq.
Require Export quotient_proofs. 
(* OrderedTypeEx.*)

(** %{\em Regular expressions}% are defined by the following inductive type: *) 

(*Generalizable All Variables.*)

Inductive re : Type := 
| re0 : re
| re1 : re
| re_sy : Z -> re
| re_union : re -> re -> re
| re_conc : re -> re -> re
| re_star : re -> re.

(*Generate OrderedType re.*)
Hint Constructors re : lre.
Notation "0"      := re0.
Notation "1"      := re1.
Notation "\! s" := (re_sy s)(at level 10).
Notation "x + y"  := (re_union x y)(at level 50,left associativity).
Notation "x · y"  := (re_conc x y)(at level 58,left associativity).
Notation "x ⋆"    := (re_star x)(at level 45).

(* Length of regular expressions *)

Fixpoint len_re  (r:re) : nat :=
  match r with
    | 0 => (S O)
    | 1 =>  (S O)
    | \!_ => (S O)
    | x + y => S (len_re x + len_re y)
    | x · y => S (len_re x + len_re y)
    | x ⋆ => S (len_re x)
  end.

(** Symbol-length of regular expressions *)
Reserved Notation "|< x >|".
Fixpoint sylen  (r:re) : nat :=
  match r with
    | 0 => O
    | 1 => O
    | \!_ => (S O)
    | x + y => plus (sylen x) (sylen y)
    | x · y => plus (sylen x) (sylen y)
    | x ⋆ => (sylen x)
  end.
Notation "|< x >|" := (sylen x).

Fixpoint re2rel  (x:re) : language :=
  match x with
    | 0 => ∅
    | 1 => {ε}
    | \!a => {{a}}
    | X + Y => (re2rel X) ∪ (re2rel Y)
    | X · Y => (re2rel X) • (re2rel Y)
    | X ⋆ => (re2rel X) ∗
  end.

Coercion re2rel : re >-> language.
  
Global Instance re2rel_m : Proper(eq ==> leq) re2rel.
Proof.
  repeat red.
  split_eq;subst;
  eauto with lgs.
Qed.

Theorem re2rel_is_RL : forall r:re, rl r.
Proof.
  induction r;simpl;intros;try constructor;try auto.
Qed.

(** Word of the language of regular expressions is well formed  *)
Lemma re_wf : forall r:re, language_wf (r).
Proof.
  induction r;simpl;auto with lgs.
Qed.

(** Decidable syntactical equality of regular expressions is available
     (through definitional equality of $\Coq$), and they also form an
     ordered set. The ordering of regular expressions is a
     lexicografical one, and is defined in the following code block:
     *)

Lemma re_sy_dec : forall r1 r2:re, {r1=r2}+{r1<>r2}.
Proof.
  decide equality;auto with zarith.
  apply Z_eq_dec.
Qed.
  
  (** Determining the empty word property for regular expressions is a syntactical version of the [cases_epsilon] function.*)

Reserved Notation "ε( y )" (at level 45,right associativity).
Fixpoint c_of_re  (r:re) : bool :=
  match r with 
    | 0 => false
    | 1 => true
    | \!_ => false
    | _⋆ => true
    | x + y => ε(x) || ε(y)
    | x · y => ε(x) && ε(y)
  end
  where "ε( y )" := (c_of_re y).

Add Morphism c_of_re : c_of_re_m.
Proof.
  repeat red;intros;subst;auto.
Qed.

  (** We now determine the language of [c_of_re]. This means that, when [c_of_re] returns [true] then it must 
     represent $\{\epsilon\}$. Otherwise, if [c_of_re] returns [false], then it should describe the language
     $\emptyset$. We define [lc_of_re] as such a function, and relate it to the [cases_epsilon] function to ensure
     its correctness *)
  
Definition lc_of_re  (r:re) := if ε(r) then {ε} else ∅.
Notation "ε'( x )" := (lc_of_re x)(at level 45).
  

Instance lc_of_re_m : Proper(eq ==> leq) lc_of_re.
Proof.
  unfold lc_of_re.
  intro;intros.
  subst.
  destruct(ε(y));reflexivity.
Qed.
  
(** Production of the re. corresponding to the emptyness of the re. given
     as argument *)
Definition c_c_of_re (r:re) := if ε(r) then 1 else 0.
Notation "ε''( x )" := (c_c_of_re x)(at level 45).

Lemma c_of_c_c_true  : 
  forall r,
    ε(r) = true -> ε''(r) = 1.
Proof.
  intros r H;unfold c_c_of_re;rewrite H;auto.
Qed.

Lemma c_of_c_c_false : 
  forall r,
    ε(r) = false -> ε''(r) = 0.
Proof.
  intros r H;unfold c_c_of_re;rewrite H;auto.
Qed.

Lemma c_c_of_c_true : 
  forall r, 
    ε''(r) = 1 -> ε(r) = true.
Proof.
  intros r H;unfold c_c_of_re in H;destruct(ε(r));congruence. 
Qed.

Lemma c_c_of_c_false : 
  forall r, 
    ε''(r) = 0 -> ε(r) = false.
Proof.
  intros r H;unfold c_c_of_re in H;destruct(ε(r));congruence. 
Qed.

Hint Resolve 
  c_of_c_c_true 
  c_of_c_c_false
  c_c_of_c_true
  c_c_of_c_false : res.

(** Decidability of emptyness testing for an re. *)
Lemma c_of_re_dec : 
  forall r, 
    {ε(r) = false}+{ε(r) = true}.
Proof.
  intro r;destruct(ε(r));auto.
Qed.

(** Nullability and epsilon membership *)
Lemma null_eps_in_l :
  forall r:re,
   ε(r) = true -> [] ∈ re2rel r.
Proof.
  induction r;simpl;intros;try congruence;auto with lgs.
  simpl_bool;destruct H as [H1|H2];[apply IHr1 in H1|apply IHr2 in H2];
    solve_trivial_union.
  simpl_bool;destruct H as [H1 H2];apply IHr1 in H1;apply IHr2 in H2.
  rewrite app_nil_end;auto with lgs.
  constructor 1 with (n:=0%nat);simpl;auto with lgs.
Qed.

Lemma eps_in_l_null :
  forall r:re,
   [] ∈ re2rel r -> ε(r) = true.
Proof.
  induction r;simpl;intros;try congruence;try now(inv H);auto with lgs.
  simpl_bool;invc H;eauto.
  simpl_bool;inv H. 
  apply app_eq_nil in H0;destruct H0;subst;eauto.
Qed.

Lemma not_eps_not_in_l :
  forall r:re,
   ε(r) = false -> ~[] ∈ re2rel r.
Proof.
  induction r;simpl;intros;try congruence;try (now(intro H1;inv H1));
    auto with lgs.
  simpl_bool;destruct H as [H1 H2];intro;apply IHr1 in H1;apply IHr2 in H2;
    inv H.
  simpl_bool;destruct H as [H1|H2];intro;[apply IHr1 in H1|apply IHr2 in H2];
    inv H; apply app_eq_nil in H0;destruct H0;subst;eauto.
Qed.

Lemma neg_not_in_conc :
  forall r1 r2:re,
  ~ [] ∈ (r1 • r2) -> ~[] ∈ (re2rel r1) \/ ~[] ∈ (re2rel r2).
Proof.
  intros r1 r2 H;destruct(c_of_re_dec r1).
  apply not_eps_not_in_l in e;auto.
  right;intro;apply H;apply null_eps_in_l in e;
    rewrite app_nil_end;auto with lgs.
Qed.

Lemma not_in_l_not_eps :
  forall r:re,
   ~[] ∈ re2rel r -> ε(r) = false.
Proof.
  induction r;simpl;intros;try congruence;try (now(intro H1;inv H1));
    auto with lgs.
  assert([] ∈ {ε}) by auto with lgs;contradiction.
  apply neg_not_nil_aux_1 in H;simpl_bool;destruct H;eauto. 
  simpl_bool;apply neg_not_in_conc in H;destruct H;eauto.
  assert([] ∈ (r ∗)) by (constructor 1 with O;simpl;eauto with lgs);
    contradiction.
Qed.

Hint Resolve
  null_eps_in_l
  eps_in_l_null
  not_eps_not_in_l
  neg_not_in_conc
  not_in_l_not_eps : res lgs.

