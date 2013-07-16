Require Export language.

(** Reduce existing [Included] definitions, both in the context and in the goal. *)
Ltac red_incl :=
  repeat (match goal with
            | H : Included _ _ _ |- _ => red in H
            | |- Included _ _ _ => red
          end).

(** Solve the trivial case of having a inductive type with no constructors in the
    context. *)
Ltac solve_empty :=
  match goal with
    | H : _ ∈ ∅ |- _ => inv H
  end.

Ltac solvv :=
  match goal with
    | H : _ ∈ ∅ |- _ => inv H
  end.

Ltac solve_empty_union :=
  match goal with
    | H : _ ∈ (∅ ∪ _) |- _ => destruct H;try solve_empty
    | H : _ ∈ (_ ∪ ∅) |- _ => destruct H;try solve_empty
  end.    

Ltac solve_trivial_union :=
  match goal with 
    | H : ?w ∈ ?L |- ?w ∈ (_ ∪ ?L) => right;auto
    | H : ?w ∈ ?L |- ?w ∈ (?L ∪ _) => left;auto
    | H : ?w ∈ ?L |- ?w ∈ (_ ∪ (_ ∪ ?L)) => right;right;auto
    | H : ?w ∈ ?L |- ?w ∈ (_ ∪ (?L ∪ _)) => right;left;auto
    | H : ?w ∈ ?L |- ?w ∈ ((?L ∪ _) ∪ _) => left;left;auto
    | H : ?w ∈ ?L |- ?w ∈ ((_ ∪ ?L) ∪ _) => left;right;auto
    | H : ?w ∈ (?L ∪ _) |- ?w ∈ ?L => destruct H;auto
    | H : ?w ∈ (_ ∪ ?L) |- ?w ∈ ?L => destruct H;auto
  end.

(** Simple tactic that can be applied to split an equivalence corresponding to 
    the equality of two languages. *)

Ltac split_eq := split;unfold Included;intros.

Generalizable All Variables.

(** Some extra conditions. *)
Lemma neg_not_nil_aux_1 :
  forall l1 l2,
    ~[] ∈ (l1 ∪ l2) -> ~[] ∈ l1 /\ ~[] ∈ l2.
Proof.
  intros;split;intro;apply H;solve_trivial_union. 
Qed.

Lemma empty_not_nil  : {ε} !∼ ∅.
Proof.
  red;intro H.
  destruct H as [H0 H1].
  red_incl.
  assert([] ∈ {ε}) by eauto.
  apply H0 in H;solve_empty.
Qed.


(** Properties of the neutral and absorving elements of languages. *)

Section NeutralAndAbsorventLemmas.

  Variable l : language.

  Lemma conc_l_neutral_right : l • {ε} ∼ l.
  Proof.
    split_eq.
    destruct H as [w0 w1 H H0].
    destruct H0;rewrite <- app_nil_end;auto.
    rewrite app_nil_end;constructor;auto.
  Qed.

  Lemma conc_l_neutral_left : {ε} • l ∼ l.
  Proof.
    split_eq.
    do 2 destruct H;auto.
    change x with (nil++x)%list;constructor;auto.
  Qed.
  
  Lemma conc_l_empty_left : ∅ • l ∼ ∅.
  Proof.
    split_eq;destruct H;solve_empty.
  Qed.

  Lemma conc_l_empty_right : l • ∅ ∼ ∅.
  Proof.
    split_eq.
    destruct H as [x x' X H'];solve_empty.
    solve_empty.
  Qed.

  Lemma union_l_neutral_left : ∅ ∪ l ∼ l.
  Proof.
    split_eq.
    solve_empty_union;trivial.
    solve_trivial_union.
  Qed.

  Lemma union_l_neutral_right : l ∪ ∅ ∼ l.
  Proof.
    split_eq.
    solve_empty_union;auto.
    solve_trivial_union.
  Qed.

End NeutralAndAbsorventLemmas.

Hint Resolve
     @conc_l_empty_right
     @conc_l_empty_left
     @conc_l_neutral_left
     @conc_l_neutral_right
     @union_l_neutral_left
     @union_l_neutral_right : lgs.

(** Tactic to solve simple concatenation with the neutral element. *)

Ltac simpl_trivial_concat :=
  match goal with 
    | H : _ ∈ ({ε} • ?L) |- _ => rewrite conc_l_neutral_left in H
    | H : _ ∈ (?L • {ε}) |- _ => rewrite conc_l_neutral_right in H
    | |- _ ∈ ({ε} • ?L) => rewrite conc_l_neutral_left
    | |- _ ∈ (?L • {ε}) => rewrite conc_l_neutral_right
  end. 


Hint Rewrite 
     @conc_l_empty_right
     @conc_l_empty_left
     @conc_l_neutral_left
     @conc_l_neutral_right
     @union_l_neutral_left
     @union_l_neutral_right : lgs.

Section AssociativityLemmas. 

  Variables l1 l2 l3: language.

  Lemma conc_l_assoc : (l1 • l2) • l3 ∼ l1 • (l2 • l3).
  Proof.
    split_eq;
    [ destruct H as [x x' [x'' H H''] H'] |
      destruct H as [x x' H [x'' H' H'']] ];
    [ rewrite app_ass | rewrite <- app_ass];
    repeat constructor;assumption.
  Qed.
  
  Lemma union_l_assoc : (l1 ∪ l2) ∪ l3 ∼ l1 ∪ (l2 ∪ l3).
  Proof.
    split_eq.
    destruct H as [x [H1 | H1'] | x H2];solve_trivial_union.
    destruct H as [ x H1 | x [H1 | H2]];solve_trivial_union.
  Qed.

End AssociativityLemmas.

Hint Resolve 
      @conc_l_assoc 
      @union_l_assoc : lgs.

(** Distributivity of concatenation over union. *)

Section DistributivityLemmas.

  Variables l1 l2 l3 : language.

  Lemma conc_l_distr_right : l1 • (l2 ∪ l3) ∼ (l1 • l2) ∪ (l1 • l3).
  Proof.
    split_eq.
    destruct H as [x x' H [x'' H'|x'' H']];
      [left|right];auto with lgs.
    destruct H as [x [x' x'' H H'] | x [x' x'' H H']];clear x;
    constructor;auto;solve_trivial_union.
  Qed.

  Lemma conc_l_distr_left : (l1 ∪ l2) • l3 ∼ (l1 • l3) ∪ (l2 • l3).
  Proof.
    split_eq.
    destruct H as [x x' [x'' H |  x'' ] H'];
      [left|right];auto with lgs.
    destruct H as [x [x' x'' H H']|x [x' x'' H H']];
      constructor;auto;solve_trivial_union.
  Qed.

End DistributivityLemmas.

Hint Resolve
     @conc_l_distr_left
     @conc_l_distr_right : lgs.

(** Commutativity and idempotence of union. *)

Section CommutativityAndIdempotenceLemmas. 

  Variable l1 l2 : language.

  Lemma union_l_comm : l1 ∪ l2 ∼ l2 ∪ l1.
  Proof.
    split_eq;
    destruct H as [x H1 | x H2];
      solve [constructor 1;auto | constructor 2;auto].
  Qed.

  Lemma union_l_idemp : l1 ∪ l1 ∼ l1.
  Proof.
    split_eq;
    [inversion_clear H|constructor];auto.
  Qed.

End CommutativityAndIdempotenceLemmas.

Hint Resolve  
     @union_l_comm 
     @union_l_idemp : lgs. 

Hint Rewrite 
  union_l_idemp : lgs.

Ltac unfold_lleq :=
  match goal with
    | H : _ ≤_ |- _ => unfold lleq in H
    | |- _ ≤ _ => unfold lleq
    | _ => idtac
  end.

Section LessOrEqualRelationLemmas.

  Variable l1 l2 l3 : language.
  
  Lemma lleq_Included_equiv : l1 ≤ l2 <-> l1 ⊆ l2.
  Proof.
    split;intros;unfold_lleq;intros.
    red;intros.
    apply H;solve_trivial_union.
    red_incl;split_eq.
    solve_trivial_union.
    solve_trivial_union.
  Qed.

  Lemma  lleq_refl : l1 ≤ l1.
  Proof.
    unfold lleq;auto with lgs.
  Qed.

  Lemma lleq_trans : l1 ≤ l2 -> l2 ≤ l3 -> l1 ≤ l3.
  Proof.
    unfold lleq;intros;
    rewrite <- H0, <- union_l_assoc, H;reflexivity.
  Qed.

  Lemma mon_concat :  l1 ≤ l2 -> (l1 • l3) ≤ (l2 • l3).
  Proof.
    unfold lleq;intros.
    rewrite <- conc_l_distr_left, H;reflexivity.
  Qed.

  Lemma eq_to_leq : l1 ∼ l2 -> l1 ≤ l2.
  Proof.
    intro H;rewrite H;unfold lleq;auto with lgs.
  Qed.

  Lemma leq_to_eq : l1 ≤ l2 /\ l2 ≤ l1 -> l1 ∼ l2.
  Proof.
    unfold lleq;intros.
    destruct H;rewrite <- H, <- H0 at 1.
    auto with lgs.
  Qed.

End  LessOrEqualRelationLemmas.

Hint Resolve
     @lleq_refl
     @lleq_refl
     @lleq_trans
     @mon_concat
     @eq_to_leq : lgs.

Global Instance lleq_relf_m : Reflexive lleq.
Proof.
  unfold Reflexive;intro;auto with lgs.
Qed.

Global Instance lleq_trans_m : Transitive lleq. 
Proof.
  unfold Transitive;intros;eapply lleq_trans;eauto.
Qed.

(** We now enumerate a set of intermediary lemmas that are used to
establish the standard properties of Kleene's star operator.*)

Section LLeqStarLemmas.

  Lemma star_l_contains_eps :
    forall l,
      {ε} ≤ l∗.
  Proof.
    split_eq;
    solve_trivial_union.
    constructor 1 with 0;auto.
  Qed.

  Lemma star_l_union_l_comm :
    forall l,
      l ∪ l∗ ∼ l∗.
  Proof.
    split_eq;solve_trivial_union;econstructor 1 with 1;simpl;
    rewrite app_nil_end;auto with lgs.
  Qed.
  
  Lemma star_plus_on : forall l, {ε} ∪ l∗ ∼ l∗.
  Proof.
    intro;apply star_l_contains_eps.
  Qed.
  
  (* Star of empty is the epsilon language *)
  Lemma empty_star_is_epsilon : ∅ ∗ ∼ {ε}.
  Proof.
    split_eq.
    destruct H.
    induction n;auto with lang.
    simpl in H.
    destruct H;try solve_empty.
    constructor 1 with (n:=0);auto with lgs.
  Qed.
  
  (* Star of epsilon language is the epsilon language itself *)
  Lemma id_empty_star_is_epsilon : {ε} ∗ ∼ {ε}.
  Proof.
    split_eq.
    destruct H.
    induction n;auto.
    simpl in H;destruct H.
    apply IHn;auto.
    destruct H.
    assumption.
    constructor 1 with (n:=0);simpl;assumption.
  Qed.

  Lemma lang_in_star_to_n : forall w r,
    w ∈ (r ∗) -> exists n, w ∈  (r •• n).
  Proof.
    intros.
    destruct H as [n w H1];
    exists n;exact H1.
  Qed.

  (* Any language is contained in its kleene closure *)
  Lemma lang_in_star : forall l, l ≤ l∗.
  Proof.
    intro.
    unfold lleq;auto with lang.
    apply star_l_union_l_comm.
  Qed.

  Lemma star_l_ConL_comm : forall l,
    l • l∗ ≤ l∗.
  Proof.
    split_eq;solve_trivial_union.
    destruct H as [x1 x2 H1 [n x3 H2]].
    constructor 1 with (n:=S n);simpl;auto with lgs.
  Qed.

  Lemma inProdProdStar : forall l,
    l • l∗ ≤ l∗ • l∗.
  Proof.
    split_eq.
    solve_trivial_union.
    destruct H.
    constructor;auto.
    constructor 1 with (n:=1);simpl.
    rewrite (app_nil_end w1).
    constructor;[auto|constructor].
    solve_trivial_union.
  Qed.

  Lemma inProdProdInv : forall l,  l∗ • l ≤ l ∗ • l∗.
  Proof.
    split_eq.
    solve_trivial_union.
    do 2 destruct H.
    induction n.
    constructor;[constructor 1 with (n:=0)|constructor 1 with (n:=1)];auto.
    rewrite (app_nil_end w2).
    constructor;auto.
    constructor.
    constructor;
      [constructor 1 with (n:=S n)|constructor 1 with (n:=1)];simpl;auto.
    rewrite (app_nil_end w2);constructor;auto.
    solve_trivial_union.
  Qed.

  Lemma plus_l_conc : forall l n m,
    l •• (n+m) ∼ (l •• n) • (l •• m).
  Proof.
    intros l n;revert n l.
    induction n;simpl;split_eq.
    replace x with (nil++x)%list;auto.
    constructor;[constructor|auto].
    destruct H.
    destruct H;simpl;auto.
    destruct H.
    eapply conc_l_assoc.
    constructor;auto.
    eapply IHn;auto.
    apply conc_l_assoc in H.
    destruct H.
    constructor;auto.
    eapply IHn.
    assumption.
  Qed.

  Lemma assoc_succ_conc : forall l n m,
    l • (l •• (n+m)) ∼ (l •• (S n)) • (l •• m).
  Proof.
    induction n;
    split_eq.
    simpl in * |- *.
    destruct H.
    constructor;auto with lang.
    apply (conc_l_neutral_right _);auto.
    simpl.
    destruct H.
    constructor;auto.
    apply (conc_l_neutral_right l);auto.
    simpl.
    destruct H.
    destruct (conc_l_assoc l (l • (l••n)) (l••m)).
    apply H2.
    constructor;auto.
    clear H1;clear H2.
    simpl in H0.
    destruct (IHn m).
    apply H1 in H0.
    auto.
    simpl in H.
    apply conc_l_assoc in H.
    simpl.
    destruct H.
    constructor;auto.
    apply (IHn m).
    simpl.
    assumption.
  Qed.
  
  Lemma nconcat_invert_order : forall n l,
    l •• (S n) ∼ (l••n)•l.
  Proof.
    induction n;
    simpl;intros.
    rewrite conc_l_neutral_left.
    rewrite conc_l_neutral_right.
    reflexivity.
    simpl in IHn.
    rewrite IHn at 1.
    rewrite conc_l_assoc.
    reflexivity.
  Qed.

  Lemma star_prod_eq_star : forall l,
    l∗ ∼ l∗ • l∗.
  Proof.
    split_eq.
    rewrite (app_nil_end x);constructor;try assumption.
    constructor 1 with (n:=0);constructor.
    do 2 destruct H.
    destruct H0.
    constructor 1 with (n:=n+n0).
    induction n.
    destruct H.
    simpl;assumption.
    simpl in H.
    simpl.
    destruct H.
    rewrite app_ass.
    constructor;auto.
    eapply plus_l_conc.
    constructor;assumption.
  Qed.

  Lemma power_of_star_lang : forall n l,
    l∗ •• n ≤ l∗.
  Proof.
    induction n;simpl;split_eq.
    apply  star_plus_on in H.
    assumption.
    constructor 2;assumption.
    destruct H.
    destruct H.
    eapply star_prod_eq_star.
    constructor;auto.
    eapply IHn.
    constructor;assumption.
    assumption.
    constructor 2.
    assumption.
  Qed.

  Lemma double_star_in_star : forall l,
    l∗∗  ≤ l∗.
  Proof.
    split_eq.
    destruct H;auto.
    destruct H.
    apply power_of_star_lang with n.
    constructor 1.
    apply H.
    constructor 2;auto.
  Qed.

  Lemma double_star_eq_star : forall l,
    l∗∗ ∼ l ∗.
  Proof.
    split_eq.
    eapply double_star_in_star.
    left.
    auto.
    apply double_star_in_star in H.
    destruct H.
    assumption.
    constructor 1 with (n:=1).
    simpl.
    eapply conc_l_neutral_right.
    assumption.
  Qed.

End LLeqStarLemmas.

Hint Resolve
     @star_l_union_l_comm
     @star_plus_on
     @empty_star_is_epsilon
     @id_empty_star_is_epsilon
     @lang_in_star
     @lang_in_star_to_n
     @star_l_ConL_comm
     @inProdProdStar
     @inProdProdInv
     @plus_l_conc
     @assoc_succ_conc
     @nconcat_invert_order
     @star_prod_eq_star
     @power_of_star_lang
     @double_star_in_star : lgs.

Section KleeneAlgebraStarAxiom_1.

  Lemma kat_ax_1_aux_1 : forall l,
    {ε} ∪ (l • l∗) ≤ l∗.
  Proof.
    split_eq.
    destruct H as [ w [ w1 H1| w1 H2] | w H3];auto with lang.
    constructor 1 with (n:=0);auto.
    eapply star_prod_eq_star.
    destruct H2.
    constructor.
    constructor 1 with (n:=1);simpl;auto.
    rewrite (app_nil_end w1).
    constructor;auto.
    assumption.
    solve_trivial_union.
  Qed.

  Lemma kat_ax_1_aux_2 : forall l,
    l ∗ ≤ {ε} ∪ (l • l∗).
  Proof.
    split_eq.
    do 2 destruct H.
    revert n H.
    induction n;intros.
    constructor;auto.
    simpl in H.
    constructor 2.
    destruct H.
    constructor;auto.
    constructor 1 with (n:=n);auto.
    constructor 1;auto.
    constructor 2;auto.
    destruct H.
    constructor 2;constructor;auto.
    constructor 2;constructor 2;auto.
  Qed.

  (** First Kleene's star property  *)
  Lemma kat_ax_1_lang : forall l,
    {ε} ∪ (l • l∗) ∼ l∗.
  Proof.
    intros;apply leq_to_eq;intros.
    split.
    eapply kat_ax_1_aux_1.
    apply kat_ax_1_aux_2.
  Qed.

End KleeneAlgebraStarAxiom_1.

Hint Resolve
     @kat_ax_1_aux_1
     @kat_ax_1_aux_2
     @kat_ax_1_lang : lgs.

Section KleeneAlgebraStarAxiom_2.

  Lemma kat_ax2_aux_1 : forall l,
    {ε} ∪ (l∗ • l) ≤ l ∗.
  Proof.
    split_eq.
    do 2 destruct H.
    constructor 1 with (n:=0);auto.
    destruct H.
    eapply star_prod_eq_star.
    constructor;auto.
    constructor 1 with (n:=1);simpl.
    rewrite (app_nil_end w2).
    constructor;auto.
    constructor 1 with (n:=n);auto.
    solve_trivial_union.
  Qed.

  Lemma kat_ax2_aux_2_a : forall n l w,
    w ∈ ((l •• n) • l) -> w ∈ (l ∗ • l).
  Proof.
    induction n;intros.
    simpl in H.
    destruct H.
    constructor;auto.
    constructor 1 with (n:=0);simpl;auto.

    destruct H.
    constructor;auto.
    constructor 1 with (n:=S n);auto.
  Qed.

  Lemma kat_ax2_aux_2 : forall l,
    l ∗ ≤ {ε} ∪ (l ∗ • l).
  Proof.
    split_eq.
    destruct H.
    destruct H.
    induction n.
    constructor;auto.
    constructor 2.
    apply nconcat_invert_order in H.
    destruct H.
    constructor.
    constructor 1 with (n:=n).
    auto.
    auto.
    destruct H;
      [constructor|constructor 2];auto.
    constructor 2;auto.
  Qed.

  (** First Kleene's star property  *)
  Lemma kat_ax_2_lang : forall l,
    {ε} ∪ (l ∗ • l) ∼ l∗.
  Proof.
    intro.
    eapply leq_to_eq.
    split.
    apply kat_ax2_aux_1.
    apply kat_ax2_aux_2.
  Qed.

End KleeneAlgebraStarAxiom_2.

Hint Resolve
     @kat_ax2_aux_2_a
     @kat_ax2_aux_2
     @kat_ax_2_lang : lgs.

  (** Remaining axioms for Kleene algebra *)
Section KleeneAlgebraStarAxiom_3.

  Variables l1 l2 : language.
    
  (* The closure contains all the powers of the solution *)
  Lemma forall_n_closure_lang :
    forall l,
      (forall n:nat, (l1••n) • l2 ≤ l) -> l1 ∗ • l2 ≤ l.
  Proof.
    split_eq.
    destruct H0;auto.
    destruct H0.
    destruct H0.
    generalize (H n);clear H;intro H.
    apply H.
    constructor.
    constructor;auto.
    constructor 2;auto.
  Qed.
    
  Lemma kat_ax3_aux_4 :
    forall l,
      l2 ≤ l /\ l1 • l ≤ l ->
      (forall n, (l1••n) • l2 ≤ l).
  Proof.
    intuition.
    induction n.
    simpl.
    unfold lleq in * |- *.
    rewrite conc_l_neutral_left.
    assumption.
    simpl.
    unfold lleq in * |- *.
    rewrite conc_l_assoc.
    eapply(lleq_trans (l1 • ((l1 •• n) • l2)) (l1 • l) l);auto.
    split_eq.
    destruct H;auto.
    destruct H;auto.
    constructor;auto.
    apply IHn.
    constructor.
    assumption.
    constructor 2;auto.
  Qed.
  
  Lemma kat_ax3_aux_5 :
    forall x,
      (l1 • x) ∪ l2 ≤ x -> l2 ≤ x /\ l1 • x ≤ x.
  Proof.
    split;
      split_eq.
    destruct H0;auto.
    apply H.
    constructor.
    constructor 2;auto.
    constructor 2;auto.
    destruct H0.
    apply H;repeat constructor;auto.
    auto.
    constructor 2;auto.
  Qed.
  
  (** Third Kleene's star property  *)

  Lemma kat_ax_3_lang :
    forall x,
      (l1 • x) ∪ l2 ≤ x -> l1 ∗ • l2 ≤ x.
  Proof.
    intros x H1.
    apply forall_n_closure_lang.
    apply kat_ax3_aux_4.
    apply kat_ax3_aux_5.
    auto.
  Qed.
  
End KleeneAlgebraStarAxiom_3.

Hint Resolve
     @kat_ax_3_lang : lgs.
  
Section KleeneAlgebraStarAxiom_4.

  Variables l1 l2 : language.
    
  Lemma forall_n_closure_lang_inv :
    forall l,
      (forall n, l2 • (l1 •• n) ≤ l) ->
      l2 • l1∗ ≤ l.
  Proof.
    split_eq.
    destruct H0;auto.
    destruct H0.
    destruct H1.
    eapply H.
    constructor;constructor;auto.
    apply H1.
    constructor 2;auto.
  Qed.
  
  Lemma kat_ax4_aux_4 :
    forall x,
      l2 ≤ x /\ x • l1 ≤ x ->
      (forall n, l2 • (l1 •• n) ≤ x).
  Proof.
    intuition.
    induction n.
    simpl.
    unfold lleq.
    rewrite conc_l_neutral_right;auto.
    unfold lleq.
    rewrite nconcat_invert_order.
    rewrite <- conc_l_assoc.
    apply (lleq_trans ((l2 • (l1 •• n)) • l1) (x • l1) x);auto.
    split_eq.
    destruct H;auto.
    destruct H.
    constructor.
    apply IHn.
    constructor;auto.
    auto.
    constructor 2;auto.
  Qed.
  
  Lemma kat_ax4_aux_5 :
    forall x,
      (x • l1) ∪ l2 ≤ x -> l2 ≤ x /\ x • l1 ≤ x.
  Proof.
    split;split_eq.
    destruct H0;auto.
    apply H.
    constructor;constructor 2;auto.
    constructor 2;auto.
    destruct H0;auto.
    apply H;constructor;constructor;auto.
    constructor 2;auto.
  Qed.
  
  (** Forth Kleene's star property  *)
  
  Lemma kat_ax_4_lang :
    forall x,
      (x • l1) ∪ l2 ≤ x -> l2 • l1∗ ≤ x.
  Proof.
    intros x H1.
    apply forall_n_closure_lang_inv.
    apply kat_ax4_aux_4.
    apply kat_ax4_aux_5.
    assumption.
  Qed.
  
End KleeneAlgebraStarAxiom_4.

Hint Resolve @kat_ax_4_lang : lgs.

Section KaBissimulation_Auxiliary.

  Lemma KA_bissimulation_aux_1 :
    forall a b x,
      (x ∪ a • x • b ∗) ≤ (x∪x • b • b∗) ->
      (a∗ • x) ≤ (x • b∗).
  Proof.
    intros.
    apply kat_ax_3_lang.
    rewrite union_l_comm.
    cut(x • b∗ ∼ x∪x • (b • b∗)).
    intros.
    rewrite H0 at 2.
    repeat rewrite <- conc_l_assoc;auto.
    rewrite <- (conc_l_neutral_right x) at 2.
    rewrite <- conc_l_distr_right.
    apply conc_l_m;auto with lgs.
    symmetry;auto with lgs.
  Qed.
    
  Lemma KA_Bissimulation_aux_2 :
    forall a b x,
      a • x ≤ x • b ->
      x ∪ a • x • b ∗ ≤ x ∪ x • b • b∗.
  Proof.
    intros.
    apply union_l_lleq.
    apply lleq_refl.
    apply conc_l_lleq;
      [assumption|apply lleq_refl].
  Qed.
  
  (* Rest of adapted code *)
  
  Lemma KA_Bissimulation_Imply_1 :
    forall a b x,
      a • x ≤ x • b ->
      a ∗ • x ≤ x • b ∗.
  Proof.
    intros.
    apply KA_bissimulation_aux_1.
    apply KA_Bissimulation_aux_2.
    assumption.
  Qed.
  
  Lemma Bissimulation_Imply_2 :
    forall a b x,
      x • b ≤ a • x ->
      x • b∗ ≤ a∗ • x.
  Proof.
    intros.
    apply kat_ax_4_lang.
    (*pattern (a[*]) at 2.*)
    rewrite <- kat_ax_2_lang at 2.
    rewrite conc_l_distr_left.
    rewrite conc_l_neutral_left.
    rewrite union_l_comm.
    apply union_l_lleq.
    apply lleq_refl.
    do 2 rewrite conc_l_assoc.
    apply conc_l_lleq.
    apply lleq_refl.
    assumption.
  Qed.
  
End KaBissimulation_Auxiliary.

Hint Resolve
     @KA_Bissimulation_Imply_1
     @Bissimulation_Imply_2 : lgs.

Section KaDenesting_Auxiliary.

  Fact Denesting_aux_1 :
  forall a b,
    {ε} ≤ a∗ • (b • a∗)∗.
  Proof.
    intros.
    rewrite <- (conc_l_neutral_left {ε}) at 1.
    apply conc_l_lleq;apply star_l_contains_eps.
  Qed.
  
  Fact Denesting_aux_2 :
  forall a b,
    a • (a∗ • (b • a∗)∗) ≤ a∗ • (b • a∗)∗.
  Proof.
    intros.
    rewrite <- conc_l_assoc.
    apply conc_l_lleq;auto with lgs.
  Qed.
  
  Lemma Denesting_aux_3 : forall a b,
      b • (a∗ • (b • a∗)∗) ≤ (b • a∗)∗.
  Proof.
    intros.
    eapply (lleq_trans _ ((b • a ∗) • (b • a ∗) ∗) _).
    rewrite conc_l_assoc;auto with lgs.
    apply star_l_ConL_comm.
  Qed.
  
  Lemma Denesting_aux_4 : forall a b,
      (b • a∗)∗ ≤ a∗ • (b • a∗)∗.
  Proof.
    intros.
    rewrite <- (conc_l_neutral_left ((b • a∗)∗)) at 1.
    apply conc_l_lleq;auto with lgs.
    apply star_l_contains_eps.
  Qed.
  
  Lemma Denesting_aux_5 :
    forall a b,
      b • (a∗ • (b • a∗)∗) ≤ a∗ • (b • a∗)∗.
  Proof.
    intros.
    apply (lleq_trans _ ((b • a∗)∗) _).
    apply Denesting_aux_3.
    apply Denesting_aux_4.
  Qed.
    
  Lemma Denesting_aux_6 : forall a b,
     {ε} ∪ a • (a∗ • (b • a∗)∗) ∪
      b • (a∗ • (b • a∗)∗) ≤ a∗ • (b • a∗)∗.
  Proof.
    intros.
    do 2 rewrite <- (union_l_idemp (a ∗ • (b • a ∗) ∗)) at 3.
    rewrite <- (Denesting_aux_2 a b) at 3.
    rewrite <- (Denesting_aux_1 a b) at 4.
    rewrite (union_l_comm (a • (a ∗ • (b • a ∗) ∗)) ({ε})).
    apply union_l_lleq.
    reflexivity.
    apply Denesting_aux_5.
  Qed.
  
  Lemma Denesting_Imply_1 : forall a b,
      (a ∪ b)∗ ≤ a∗ • (b • a∗)∗.
  Proof.
    intros.
    rewrite <- (conc_l_neutral_right ((a ∪ b)∗)).
    apply kat_ax_3_lang.
    rewrite (union_l_comm _ {ε}).
    rewrite conc_l_distr_left.
    rewrite <- union_l_assoc.
    apply Denesting_aux_6.
  Qed.
      
  Lemma Denesting_aux_7 : forall a b,
    (a ∪ b)∗ • ((a ∪ b)∗)∗ ≤ (a ∪ b)∗.
  Proof.
    intros.
    rewrite double_star_eq_star.
    rewrite <- star_prod_eq_star.
    reflexivity.
  Qed.

  Lemma Denesting_aux_9 : forall a b,
    (a ∪ b)∗ • ((a ∪ b) • (a ∪ b)∗)∗
    ≤ (a ∪ b)∗ • ((a ∪ b)∗)∗.
  Proof.
    intros.
    apply conc_l_lleq.
    apply lleq_refl.
    apply star_l_lleq.
    apply star_l_ConL_comm.
  Qed.
      
  Lemma Denesting_aux_10 : forall a b,
      a∗ • (b • a∗)∗ ≤
      (a ∪ b)∗ • ((a ∪ b) • (a ∪ b)∗)∗.
  Proof.
    intros.
    apply conc_l_lleq.
    apply star_l_lleq.
    unfold lleq.
    rewrite <- union_l_assoc.
    rewrite union_l_idemp.
    reflexivity.
    apply star_l_lleq.
    apply conc_l_lleq.
    unfold lleq.
    rewrite union_l_comm.
    rewrite union_l_assoc.
    rewrite union_l_idemp.
    reflexivity.
    apply star_l_lleq.
    unfold lleq.
    rewrite <- union_l_assoc.
    rewrite union_l_idemp.
    reflexivity.
  Qed.
    
  Lemma Denesting_Imply_2 : forall a b,
      a∗ • (b • a∗)∗ ≤ (a ∪ b)∗.
  Proof.
    intros.
    transitivity ((a ∪ b)∗ • ((a ∪ b)∗)∗).
    transitivity ((a ∪ b)∗ • ((a ∪ b) • (a ∪ b)∗)∗).
    apply Denesting_aux_10.
    apply Denesting_aux_9.
    apply Denesting_aux_7.
  Qed.
  
End KaDenesting_Auxiliary.

(* end hide *)

Lemma ka_bisimulation :
  forall l1 l2 l3,
    l1 • l2 ∼ l2 • l3 -> l2 • l3∗ ∼ l1∗ • l2.
Proof.
  intros;destruct H;split;
  apply lleq_Included_equiv;apply lleq_Included_equiv in H;
  apply lleq_Included_equiv in H0;
     [apply Bissimulation_Imply_2|apply KA_Bissimulation_Imply_1];
     assumption.
Qed.
  
Lemma ka_denesting :
  forall l1 l2,
    (l1 ∪ l2)∗ ∼ l1∗ • (l2 • l1∗)∗.
Proof.
  intros.
  generalize(Denesting_Imply_1 l1 l2).  
  intro.
  generalize(Denesting_Imply_2 l1 l2).
  intro.
  unfold lleq in H,H0.
  rewrite <- H.
  rewrite <- H0 at 1;auto with lgs.
Qed.

Lemma ka_sliding :
  forall l1 l2,
    (l1 • l2)∗ • l1 ∼ l1 • (l2 • l1)∗.
Proof.
  intros.
  symmetry.
  apply ka_bisimulation.
  rewrite <- conc_l_assoc.
  reflexivity.
Qed.

Lemma empty_or_empty : 
  forall l1 l2,
    l1 ∪ l2 ∼ ∅ <-> l1 ∼ ∅ /\ l2 ∼ ∅.
Proof.
  intros.
  split;intros.
  do 2 split;red;intros;
  try apply H.
  constructor;auto.
  inversion H0.
  constructor 2;auto.
  inversion H0.
  destruct H.
  split;red;intros.
  destruct H1.
  apply H in H1;auto.
  apply H0 in H1;auto.
  inversion H1.
Qed.

Ltac solve_by_ka_axioms :=
  try reflexivity ;
  match goal with
    | |- context[?x • {ε} ∼ ?x] =>
        eapply conc_l_neutral_right
    | |- context[{ε} • ?l ∼ ?l] =>
        eapply conc_l_neutral_left
    | |- context[∅ • ?l ∼ ∅] =>
        eapply conc_l_empty_left
    | |- context[?l • ∅ ∼ ∅] =>
        eapply conc_l_empty_right
    | |- context[(?l1 • ?l2) • ?l3 ∼ ?l1 • (?l2 • ?l3)] =>
        eapply conc_l_assoc
    | |- context[?l1 • (?l2 ∪ ?l3) ∼ (?l1 • ?l2) ∪ (?l1 • ?l3)] =>
        eapply conc_l_distr_right
    | |- context[(?l1 ∪ ?l2) • ?l3 ∼ (?l1 • ?l3) ∪ (?l2 • ?l3)] =>
        eapply conc_l_distr_left
    | |- context[∅ ∪ ?l ∼ ?l] =>
        eapply union_l_neutral_left
    | |- context[?l ∪ ∅ ∼ ?l] =>
        eapply union_l_neutral_right
    | |- context[?l1 ∪ ?l2 ∼ ?l2 ∪ ?l1] =>
        eapply union_l_comm
    | |- context[?l ∪ ?l ∼ ?l] =>
        eapply union_l_idemp
    | |- context[(?l1 ∪ ?l2) ∪ ?l3 ∼ ?l1 ∪ (?l2 ∪ ?l3)] =>
        eapply union_l_assoc
    | |- context[{ε} ∪ (?l • (?l∗)) ∼ ?l∗] =>
        eapply kat_ax_1_lang
    | |- context[{ε} ∪ ((?l∗) • ?l) ∼ ?l∗] =>
        eapply kat_ax_2_lang
    | _ => fail 1 "Not an equation of Kleene algebra"
  end.

Ltac solve_by_ka :=
  try solve_by_ka_axioms;symmetry;solve_by_ka_axioms.

(** Some more usefull results. *)
Lemma not_null_in_lconc: 
  forall (w1 w2 x : word)(l1 l2 : language)(a : Z),
  w1 ∈  l1 -> w2 ∈  l2 -> (w1 ++ w2)%list = a :: x -> ~[] ∈  l1 -> 
  (exists k, w1 = a :: k).
Proof.
  induction w1;intros.
  inv H1.
  rewrite <- app_comm_cons in H1;injection H1;intros;subst.
  exists w1;auto.
Qed.

Lemma not_null_in_lconc_2: 
  forall (w1 w2 x : word)(l1 l2 : language)(a : Z),
  w1 ∈  l1 -> w2 ∈  l2 -> (w1 ++ w2)%list = a :: x -> w1 =/= [] -> 
  (exists k, w1 = a :: k).
Proof.
  induction w1;intros.
  elim H2;autotc.
  rewrite <- app_comm_cons in H1;injection H1;intros;subst.
  exists w1;auto.
Qed.
