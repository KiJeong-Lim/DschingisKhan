Require Import DschingisKhan.pure.CBA.
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

  Definition eq_formula_dec :
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
  Defined.

  Section ENUMERATE_FORMULAS.

  Definition rankOfFormula : formula -> nat :=
    fix rankOfFormula_fix (p : formula) {struct p} : nat :=
    match p with
    | AtomF i => 0
    | ContradictionF => 1
    | NegationF p1 => S (rankOfFormula_fix p1)
    | ConjunctionF p1 p2 => S (max (rankOfFormula_fix p1) (rankOfFormula_fix p2))
    | DisjunctionF p1 p2 => S (max (rankOfFormula_fix p1) (rankOfFormula_fix p2))
    | ImplicationF p1 p2 => S (max (rankOfFormula_fix p1) (rankOfFormula_fix p2))
    | BiconditionalF p1 p2 => S (max (rankOfFormula_fix p1) (rankOfFormula_fix p2))
    end
  .

  Fixpoint enum_formula_aux (rank : nat) {struct rank} : nat -> formula :=
    match rank with
    | O => AtomF
    | S rank' =>
      fun seed0 : nat =>
      let seed1 : nat := fst (cantor_pairing seed0) in
      let piece : nat := snd (cantor_pairing seed0) in
      match piece with
      | 0 => ContradictionF
      | 1 => NegationF (enum_formula_aux rank' seed1) 
      | 2 =>
        let seed2 : nat := fst (cantor_pairing seed1) in
        let seed3 : nat := snd (cantor_pairing seed1) in
        ConjunctionF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
      | 3 =>
        let seed2 : nat := fst (cantor_pairing seed1) in
        let seed3 : nat := snd (cantor_pairing seed1) in
        DisjunctionF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
      | 4 =>
        let seed2 : nat := fst (cantor_pairing seed1) in
        let seed3 : nat := snd (cantor_pairing seed1) in
        ImplicationF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
      | 5 =>
        let seed2 : nat := fst (cantor_pairing seed1) in
        let seed3 : nat := snd (cantor_pairing seed1) in
        BiconditionalF (enum_formula_aux rank' seed2) (enum_formula_aux rank' seed3)
      | S (S (S (S (S (S i))))) => AtomF i
      end
    end
  .

  Local Ltac enum_formula_aux_is_good_tac_aux1 :=
    match goal with
    | H : cantor_pairing ?seed = ?rhs |- _ => rewrite H; simpl
    end
  .

  Local Ltac enum_formula_aux_is_good_tac_aux2 :=
    match goal with
    | H : enum_formula_aux ?rank ?seed = ?p |- _ => rewrite <- H
    end
  .

  Local Ltac enum_formula_aux_is_good_tac :=
    (unfold enum_formula_aux); (repeat enum_formula_aux_is_good_tac_aux1); (repeat enum_formula_aux_is_good_tac_aux2); (eauto)
  .

  Definition enum_formula_aux_is_good :
    forall p : formula,
    forall rank : nat,
    rankOfFormula p <= rank ->
    {seed : nat | enum_formula_aux rank seed = p}.
  Proof with enum_formula_aux_is_good_tac.
    assert (claim1 := fun x : nat => fun y : nat => fun z : nat => proj2 (cantor_pairing_is x y z)).
    induction p; simpl.
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
      assert (H1 : rankOfFormula p <= rank) by now apply le_elim_S_n_le_m.
      destruct (IHp rank H1) as [seed2 H2].
      assert (H3 : cantor_pairing (sum_from_0_to (seed2 + piece) + piece) = (seed2, piece)) by now apply claim1.
      exists (sum_from_0_to (seed2 + piece) + piece)...
    }
    { set (piece := 2).
      assert (H1 : max (rankOfFormula p1) (rankOfFormula p2) <= rank) by now apply le_elim_S_n_le_m.
      assert (H2 : rankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (rankOfFormula p1) (rankOfFormula p2)).
      assert (H3 : rankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (rankOfFormula p1) (rankOfFormula p2)).
      destruct (IHp1 rank H2) as [seed2 H4].
      destruct (IHp2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 3).
      assert (H1 : max (rankOfFormula p1) (rankOfFormula p2) <= rank) by now apply le_elim_S_n_le_m.
      assert (H2 : rankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (rankOfFormula p1) (rankOfFormula p2)).
      assert (H3 : rankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (rankOfFormula p1) (rankOfFormula p2)).
      destruct (IHp1 rank H2) as [seed2 H4].
      destruct (IHp2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 4).
      assert (H1 : max (rankOfFormula p1) (rankOfFormula p2) <= rank) by now apply le_elim_S_n_le_m.
      assert (H2 : rankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (rankOfFormula p1) (rankOfFormula p2)).
      assert (H3 : rankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (rankOfFormula p1) (rankOfFormula p2)).
      destruct (IHp1 rank H2) as [seed2 H4].
      destruct (IHp2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 5).
      assert (H1 : max (rankOfFormula p1) (rankOfFormula p2) <= rank) by now apply le_elim_S_n_le_m.
      assert (H2 : rankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (rankOfFormula p1) (rankOfFormula p2)).
      assert (H3 : rankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (rankOfFormula p1) (rankOfFormula p2)).
      destruct (IHp1 rank H2) as [seed2 H4].
      destruct (IHp2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
  Defined.

  Definition enum_formula : nat -> formula :=
    fun n : nat =>
    let rank : nat := fst (cantor_pairing n) in
    let seed : nat := snd (cantor_pairing n) in
    enum_formula_aux rank seed
  .

  Definition formula_is_enumerable : forall p : formula, {n : nat | enum_formula n = p} :=
    fun p : formula =>
    let seed : nat := proj1_sig (enum_formula_aux_is_good p (rankOfFormula p) (le_n (rankOfFormula p))) in
    exist (fun n : nat => enum_formula n = p) (sum_from_0_to (rankOfFormula p + seed) + seed) (eq_ind (rankOfFormula p, seed) (fun pr : nat * nat => enum_formula_aux (fst pr) (snd pr) = p) (proj2_sig (enum_formula_aux_is_good p (rankOfFormula p) (le_n (rankOfFormula p)))) (cantor_pairing (sum_from_0_to (rankOfFormula p + seed) + seed)) (cantor_pairing_is_surjective (rankOfFormula p) seed))
  .

  End ENUMERATE_FORMULAS.

End SyntaxOfPL.

Module FormulaNotationsOfPL.

  Import SyntaxOfPL.

  Global Declare Custom Entry pl_formula_scope.

  Global Notation " $$ p $$ " := p (p custom pl_formula_scope at level 3, only parsing).

  Global Notation " 'p_{' i  '}' " := (AtomF i) (in custom pl_formula_scope at level 0, only parsing).

  Global Notation " '_|_' " := (ContradictionF) (in custom pl_formula_scope at level 0, no associativity, only parsing).

  Global Notation " '~' p1 " := (NegationF p1) (in custom pl_formula_scope at level 1, right associativity, only parsing).

  Global Notation " p1 '/\' p2 " := (ConjunctionF p1 p2) (in custom pl_formula_scope at level 1, right associativity, only parsing).

  Global Notation " p1 '\/' p2 " := (DisjunctionF p1 p2) (in custom pl_formula_scope at level 2, right associativity, only parsing).

  Global Notation " p1 '->' p2 " := (ImplicationF p1 p2) (in custom pl_formula_scope at level 2, right associativity, only parsing).

  Global Notation " p1 '<->' p2 " := (BiconditionalF p1 p2) (in custom pl_formula_scope at level 2, no associativity, only parsing).

  Global Notation " x " := x (in custom pl_formula_scope at level 0, x ident).

  Global Notation " ( p ) " := p (in custom pl_formula_scope, p at level 3).

End FormulaNotationsOfPL.

Module SemanticsOfPL.

  Import MyUniverses MyEnsemble SyntaxOfPL.

  Definition value : InferiorUniverse :=
    Prop
  .

  Definition env : InferiorUniverse :=
    pvar -> value
  .

  Fixpoint eval_formula (v : env) (p : formula) : value :=
    match p with
    | AtomF i => v i
    | ContradictionF => False
    | NegationF p1 => ~ eval_formula v p1
    | ConjunctionF p1 p2 => eval_formula v p1 /\ eval_formula v p2
    | DisjunctionF p1 p2 => eval_formula v p1 \/ eval_formula v p2
    | ImplicationF p1 p2 => eval_formula v p1 -> eval_formula v p2
    | BiconditionalF p1 p2 => eval_formula v p1 <-> eval_formula v p2
    end
  .

  Variant satisfies (v : env) (p : formula) : Prop :=
  | IsModel : eval_formula v p -> satisfies v p
  .

  Global Notation " hs '|=' c " := (forall v : env, (forall h : formula, member h hs -> satisfies v h) -> satisfies v c) (at level 70, no associativity) : type_scope.

  Lemma extend_entails {hs1 : ensemble formula} {c : formula} :
    hs1 |= c ->
    forall hs2 : ensemble formula,
    hs1 \subseteq hs2 ->
    hs2 |= c.
  Proof with eauto with *.
    intros H_entails hs2 H_incl...
  Qed.

End SemanticsOfPL.

Module InferenceRulesOfPL.

  Import MyEnsemble MyEnsembleNova SyntaxOfPL FormulaNotationsOfPL.

  Inductive infers : ensemble formula -> formula -> Prop :=
  | ByAssumption {hs : ensemble formula} : forall h : formula, member h hs -> infers hs h
  | ContradictionI {hs : ensemble formula} : forall a : formula, infers hs a -> infers hs (NegationF a) -> infers hs ContradictionF
  | ContradictionE {hs : ensemble formula} : forall a : formula, infers hs ContradictionF -> infers hs a
  | NegationI {hs : ensemble formula} : forall a : formula, infers (insert a hs) ContradictionF -> infers hs (NegationF a)
  | NegationE {hs : ensemble formula} : forall a : formula, infers (insert (NegationF a) hs) ContradictionF -> infers hs a
  | ConjunctionI {hs : ensemble formula} : forall a : formula, forall b : formula, infers hs a -> infers hs b -> infers hs (ConjunctionF a b)
  | ConjunctionE1 {hs : ensemble formula} : forall a : formula, forall b : formula, infers hs (ConjunctionF a b) -> infers hs a
  | ConjunctionE2 {hs : ensemble formula} : forall a : formula, forall b : formula, infers hs (ConjunctionF a b) -> infers hs b
  | DisjunctionI1 {hs : ensemble formula} : forall a : formula, forall b : formula, infers hs a -> infers hs (DisjunctionF a b)
  | DisjunctionI2 {hs : ensemble formula} : forall a : formula, forall b : formula, infers hs b -> infers hs (DisjunctionF a b)
  | DisjunctionE {hs : ensemble formula} : forall a : formula, forall b : formula, forall c : formula, infers hs (DisjunctionF a b) -> infers (insert a hs) c -> infers (insert b hs) c -> infers hs c
  | ImplicationI {hs : ensemble formula} : forall a : formula, forall b : formula, infers (insert a hs) b -> infers hs (ImplicationF a b)
  | ImplicationE {hs : ensemble formula} : forall a : formula, forall b : formula, infers hs (ImplicationF a b) -> infers hs a -> infers hs b
  | BiconditionalI {hs : ensemble formula} : forall a : formula, forall b : formula, infers (insert a hs) b -> infers (insert b hs) a -> infers hs (BiconditionalF a b)
  | BiconditionalE1 {hs : ensemble formula} : forall a : formula, forall b : formula, infers hs (BiconditionalF a b) -> infers hs a -> infers hs b
  | BiconditionalE2 {hs : ensemble formula} : forall a : formula, forall b : formula, infers hs (BiconditionalF a b) -> infers hs b -> infers hs a
  .

  Local Hint Constructors infers : core.

  Global Notation " hs '|-' c " := (infers hs c) (at level 70, no associativity) : type_scope.

  Lemma Law_of_Exclusive_Middle (p : formula) :
    \emptyset |- $$p \/ ~ p$$.
  Proof with eauto with *.
    eapply NegationE, ContradictionI.
    - eapply DisjunctionI2, NegationI, ContradictionI.
      + eapply DisjunctionI1, ByAssumption...
      + eapply ByAssumption, in_insert_iff, or_intror...
    - eapply ByAssumption...
  Qed.

  Lemma cut_property {hs : ensemble formula} :
    forall p1 : formula,
    forall p2 : formula,
    hs |- p1 ->
    insert p1 hs |- p2 ->
    hs |- p2.
  Proof with eauto with *.
    intros p1 p2 H_infers H_cut.
    assert (claim1 : hs |- $$p1 -> p2$$)...
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
