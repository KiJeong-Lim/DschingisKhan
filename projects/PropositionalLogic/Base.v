Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module SyntaxOfPL.

  Import MyUtilities MyEnsemble.

  Definition pvar : Set := 
    nat
  .

  Inductive formula : Set :=
  | AtomF : forall i : pvar, formula
  | ContradictionF : formula
  | NegationF : forall p1 : formula, formula
  | ConjunctionF : forall p1 : formula, forall p2 : formula, formula
  | DisjunctionF : forall p1 : formula, forall p2 : formula, formula
  | ImplicationF : forall p1 : formula, forall p2 : formula, formula
  | BiconditionalF : forall p1 : formula, forall p2 : formula, formula
  .

  Lemma eq_formula_dec :
    forall p1 : formula,
    forall p2 : formula,
    {p1 = p2} + {p1 <> p2}.
  Proof with try ((right; congruence) || (left; congruence)).
    induction p1; destruct p2...
    - destruct (eq_dec_nat i i0)...
    - destruct (IHp1 p2)...
    - destruct (IHp1_1 p2_1); destruct (IHp1_2 p2_2)...
    - destruct (IHp1_1 p2_1); destruct (IHp1_2 p2_2)...
    - destruct (IHp1_1 p2_1); destruct (IHp1_2 p2_2)...
    - destruct (IHp1_1 p2_1); destruct (IHp1_2 p2_2)...
  Qed.

  Section WE_CAN_ENUMERATE_ALL_FORMULAE.

  Fixpoint getRankOfFormula (p : formula) {struct p} : nat :=
    match p with
    | AtomF i => 0
    | ContradictionF => 1
    | NegationF p1 => S (getRankOfFormula p1)
    | ConjunctionF p1 p2 => S (max (getRankOfFormula p1) (getRankOfFormula p2))
    | DisjunctionF p1 p2 => S (max (getRankOfFormula p1) (getRankOfFormula p2))
    | ImplicationF p1 p2 => S (max (getRankOfFormula p1) (getRankOfFormula p2))
    | BiconditionalF p1 p2 => S (max (getRankOfFormula p1) (getRankOfFormula p2))
    end
  .

  Fixpoint enum_formulae_of_rank (rank : nat) {struct rank} : nat -> formula :=
    match rank with
    | O => AtomF
    | S rank' =>
      fun seed0 : nat =>
      let seed1 : nat := fst (cantor_pairing seed0) in
      let piece : nat := snd (cantor_pairing seed0) in
      match piece with
      | 0 => ContradictionF
      | 1 => NegationF (enum_formulae_of_rank rank' seed1) 
      | 2 =>
        let seed2 : nat := fst (cantor_pairing seed1) in
        let seed3 : nat := snd (cantor_pairing seed1) in
        ConjunctionF (enum_formulae_of_rank rank' seed2) (enum_formulae_of_rank rank' seed3)
      | 3 =>
        let seed2 : nat := fst (cantor_pairing seed1) in
        let seed3 : nat := snd (cantor_pairing seed1) in
        DisjunctionF (enum_formulae_of_rank rank' seed2) (enum_formulae_of_rank rank' seed3)
      | 4 =>
        let seed2 : nat := fst (cantor_pairing seed1) in
        let seed3 : nat := snd (cantor_pairing seed1) in
        ImplicationF (enum_formulae_of_rank rank' seed2) (enum_formulae_of_rank rank' seed3)
      | 5 =>
        let seed2 : nat := fst (cantor_pairing seed1) in
        let seed3 : nat := snd (cantor_pairing seed1) in
        BiconditionalF (enum_formulae_of_rank rank' seed2) (enum_formulae_of_rank rank' seed3)
      | S (S (S (S (S (S i))))) => AtomF i
      end
    end
  .

  Local Ltac enum_formulae_of_rank_is_good_tac_aux1 :=
    match goal with
    | H : cantor_pairing ?seed = ?rhs |- _ => rewrite H; simpl
    end
  .

  Local Ltac enum_formulae_of_rank_is_good_tac_aux2 :=
    match goal with
    | H : enum_formulae_of_rank ?rank ?seed = ?p |- _ => rewrite <- H
    end
  .

  Local Ltac enum_formulae_of_rank_is_good_tac :=
    (unfold enum_formulae_of_rank); (repeat enum_formulae_of_rank_is_good_tac_aux1); (repeat enum_formulae_of_rank_is_good_tac_aux2); (eauto)
  .

  Lemma enum_formulae_of_rank_is_good :
    forall p : formula,
    forall rank : nat,
    getRankOfFormula p <= rank ->
    {seed : nat | enum_formulae_of_rank rank seed = p}.
  Proof with enum_formulae_of_rank_is_good_tac.
    assert (claim1 := fun x : nat => fun y : nat => fun z : nat => proj2 (cantor_pairing_spec x y z)).
    induction p as [i | | p1 IH1 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2]; simpl.
    { intros [| r'] H.
      - exists (i)...
      - assert (H0 : cantor_pairing (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i)))))) = (0, S (S (S (S (S (S i))))))) by now apply claim1.
        exists (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i))))))...
    }
    all: intros r H; set (rank := pred r); assert (H0 : S rank = r) by (now apply (guarantee1_S_pred_n_eq_n H)); rewrite <- H0.
    { set (piece := 0).
      exists (piece)...
    }
    { set (piece := 1).
      assert (H1 : getRankOfFormula p1 <= rank) by now apply le_elim_S_n_le_m.
      destruct (IH1 rank H1) as [seed2 H2].
      assert (H3 : cantor_pairing (sum_from_0_to (seed2 + piece) + piece) = (seed2, piece)) by now apply claim1.
      exists (sum_from_0_to (seed2 + piece) + piece)...
    }
    { set (piece := 2).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply le_elim_S_n_le_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      destruct (IH1 rank H2) as [seed2 H4].
      destruct (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 3).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply le_elim_S_n_le_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      destruct (IH1 rank H2) as [seed2 H4].
      destruct (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 4).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply le_elim_S_n_le_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      destruct (IH1 rank H2) as [seed2 H4].
      destruct (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 5).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply le_elim_S_n_le_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      destruct (IH1 rank H2) as [seed2 H4].
      destruct (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
  Defined.

  Definition enum_formula : nat -> formula :=
    fun n : nat =>
    let rank : nat := fst (cantor_pairing n) in
    let seed : nat := snd (cantor_pairing n) in
    enum_formulae_of_rank rank seed
  .

  Lemma formula_is_enumerable :
    forall p : formula,
    {n : nat | enum_formula n = p}.
  Proof.
    unfold enum_formula.
    intros p.
    destruct (enum_formulae_of_rank_is_good p (getRankOfFormula p) le_reflexivity) as [seed Heq].
    exists (sum_from_0_to (getRankOfFormula p + seed) + seed).
    rewrite <- (cantor_pairing_is_surjective (getRankOfFormula p) seed).
    exact Heq.
  Defined.

  End WE_CAN_ENUMERATE_ALL_FORMULAE.

End SyntaxOfPL.

Module FormulaNotationsOfPL.

  Import SyntaxOfPL.

  Global Declare Scope pl_formula_scope.

  Bind Scope pl_formula_scope with formula.

  Global Declare Custom Entry pl_formula_viewer.

  Global Notation " 'p_{' i  '}' " := (AtomF i) (in custom pl_formula_viewer at level 0).

  Global Notation " '_|_' " := (ContradictionF) (in custom pl_formula_viewer at level 0, no associativity).

  Global Notation " '~' p1 " := (NegationF p1) (in custom pl_formula_viewer at level 1, right associativity).

  Global Notation " p1 '/\' p2 " := (ConjunctionF p1 p2) (in custom pl_formula_viewer at level 1, right associativity).

  Global Notation " p1 '\/' p2 " := (DisjunctionF p1 p2) (in custom pl_formula_viewer at level 2, right associativity).

  Global Notation " p1 '->' p2 " := (ImplicationF p1 p2) (in custom pl_formula_viewer at level 2, right associativity).

  Global Notation " p1 '<->' p2 " := (BiconditionalF p1 p2) (in custom pl_formula_viewer at level 2, no associativity).

  Global Notation " p " := p (in custom pl_formula_viewer at level 0, p ident).

  Global Notation " '(' p ')' " := p (in custom pl_formula_viewer, p at level 3).

  Global Open Scope pl_formula_scope.

  Global Notation " '\obj[' p  ']' " := p (p custom pl_formula_viewer at level 3, at level 0, no associativity) : pl_formula_scope.

End FormulaNotationsOfPL.

Module SemanticsOfPL.

  Import MyUniverses MyEnsemble SyntaxOfPL FormulaNotationsOfPL.

  Definition truth_value : InferiorUniverse :=
    Prop
  .

  Definition pvar_env : InferiorUniverse :=
    pvar -> truth_value
  .

  Fixpoint eval_formula (v : pvar_env) (p : formula) {struct p} : truth_value :=
    match p with
    | \obj[ p_{ i } ] => v i
    | \obj[ _|_ ] => False
    | \obj[ ~ p1 ] => ~ eval_formula v p1
    | \obj[ p1 /\ p2 ] => eval_formula v p1 /\ eval_formula v p2
    | \obj[ p1 \/ p2 ] => eval_formula v p1 \/ eval_formula v p2
    | \obj[ p1 -> p2 ] => eval_formula v p1 -> eval_formula v p2
    | \obj[ p1 <-> p2 ] => eval_formula v p1 <-> eval_formula v p2
    end
  .

  Variant satisfies (v : pvar_env) (p : formula) : Prop :=
  | IsModel : eval_formula v p -> satisfies v p
  .

  Global Notation " hs '|=' c " := (forall v : pvar_env, (forall h : formula, member h hs -> satisfies v h) -> satisfies v c) (at level 70, no associativity) : type_scope.

  Lemma extend_entails {hs1 : ensemble formula} {c : formula} :
    hs1 |= c ->
    forall hs2 : ensemble formula,
    isSubsetOf hs1 hs2 ->
    hs2 |= c.
  Proof with eauto with *.
    intros H_entails hs2 H_incl...
  Qed.

  Definition isStructure : ensemble formula -> Prop :=
    fun ps : ensemble formula =>
    forall p : formula,
    member p ps <-> eval_formula (preimage AtomF ps) p
  .

  Definition structure_gives_its_subset_model :
    forall ps_dagger : ensemble formula,
    isStructure ps_dagger ->
    forall ps : ensemble formula,
    isSubsetOf ps ps_dagger ->
    {v : pvar_env | (forall p : formula, member p ps -> satisfies v p) /\ (v = preimage AtomF ps_dagger)}.
  Proof.
    intros ps_dagger ps_dagger_isStructure ps ps_isSubsetOf_ps_dagger.
    exists (preimage AtomF ps_dagger).
    split.
    - intros p p_in_ps.
      constructor.
      apply (proj1 (ps_dagger_isStructure p)).
      exact (ps_isSubsetOf_ps_dagger p p_in_ps).
    - reflexivity.
  Defined.

End SemanticsOfPL.

Module InferenceRulesOfPL.

  Import MyEnsemble MyEnsembleNova SyntaxOfPL FormulaNotationsOfPL.

  Global Reserved Notation " hs '|-' c " (at level 70, no associativity).

  Inductive infers : ensemble formula -> formula -> Prop :=
  | ByAssumption {hs : ensemble formula} :
    forall h : formula,
    h \in hs ->
    hs |- h
  | ContradictionI {hs : ensemble formula} :
    forall a : formula,
    hs |- a ->
    hs |- NegationF a ->
    hs |- ContradictionF
  | ContradictionE {hs : ensemble formula} :
    forall a : formula,
    hs |- ContradictionF ->
    hs |- a
  | NegationI {hs : ensemble formula} :
    forall a : formula,
    insert a hs |- ContradictionF ->
    hs |- NegationF a
  | NegationE {hs : ensemble formula} :
    forall a : formula,
    insert (NegationF a) hs |- ContradictionF ->
    hs |- a
  | ConjunctionI {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |- a ->
    hs |- b ->
    hs |- ConjunctionF a b
  | ConjunctionE1 {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |- ConjunctionF a b ->
    hs |- a
  | ConjunctionE2 {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |- ConjunctionF a b ->
    hs |- b
  | DisjunctionI1 {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |- a ->
    hs |- DisjunctionF a b
  | DisjunctionI2 {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |- b ->
    hs |- DisjunctionF a b
  | DisjunctionE {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    forall c : formula,
    hs |- DisjunctionF a b ->
    insert a hs |- c ->
    insert b hs |- c ->
    hs |- c
  | ImplicationI {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    insert a hs |- b ->
    hs |- ImplicationF a b
  | ImplicationE {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |- ImplicationF a b ->
    hs |- a ->
    hs |- b
  | BiconditionalI {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    insert a hs |- b ->
    insert b hs |- a ->
    hs |- BiconditionalF a b
  | BiconditionalE1 {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |- BiconditionalF a b ->
    hs |- a ->
    hs |- b
  | BiconditionalE2 {hs : ensemble formula} :
    forall a : formula,
    forall b : formula,
    hs |- BiconditionalF a b ->
    hs |- b ->
    hs |- a
  where " hs '|-' c " := (infers hs c) : type_scope.

  Local Hint Constructors infers : core.

  Lemma Law_of_Exclusive_Middle (p : formula) :
    \emptyset |- \obj[ p \/ ~ p ].
  Proof with reflexivity.
    eapply NegationE, ContradictionI.
    - eapply DisjunctionI2, NegationI, ContradictionI.
      + eapply DisjunctionI1, ByAssumption, in_insert_iff, or_introl...
      + eapply ByAssumption, in_insert_iff, or_intror, in_insert_iff, or_introl...
    - eapply ByAssumption, in_insert_iff, or_introl...
  Qed.

  Lemma cut_property {hs : ensemble formula} :
    forall p1 : formula,
    forall p2 : formula,
    hs |- p1 ->
    insert p1 hs |- p2 ->
    hs |- p2.
  Proof with eauto with *.
    intros p1 p2 H_infers H_cut.
    assert (claim1 : hs |- \obj[ p1 -> p2 ])...
  Qed.

  Lemma extend_infers {hs1 : ensemble formula} {c : formula} :
    hs1 |- c ->
    forall hs2 : ensemble formula,
    isSubsetOf hs1 hs2 ->
    hs2 |- c.
  Proof with eauto with *.
    intros H_infers.
    induction H_infers; intros hs' H_incl.
    - apply (ByAssumption h)...
    - apply (ContradictionI a)...
    - apply (ContradictionE a)...
    - apply (NegationI a)...
    - apply (NegationE a)...
    - apply (ConjunctionI a b)...
    - apply (ConjunctionE1 a b)...
    - apply (ConjunctionE2 a b)...
    - apply (DisjunctionI1 a b)...
    - apply (DisjunctionI2 a b)...
    - apply (DisjunctionE a b c)...
    - apply (ImplicationI a b)...
    - apply (ImplicationE a b)...
    - apply (BiconditionalI a b)...
    - apply (BiconditionalE1 a b)...
    - apply (BiconditionalE2 a b)...
  Qed.

End InferenceRulesOfPL.
