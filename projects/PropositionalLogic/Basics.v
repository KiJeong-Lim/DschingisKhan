Require Import Coq.Lists.List.
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
      - exists i...
      - assert (H0 : cantor_pairing (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i)))))) = (0, S (S (S (S (S (S i))))))) by now apply claim1.
        exists (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i))))))...
    }
    all: intros r H; set (rank := pred r); assert (H0 : S rank = r) by (now apply (guarantee1_S_pred_n_eq_n H)); rewrite <- H0.
    { set (piece := 0).
      exists piece...
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

  Definition eval_formula : env -> formula -> value :=
    fun v : env =>
    fix eval_formula_fix (p : formula) {struct p} : value :=
    match p with
    | AtomF i => v i
    | ContradictionF => False
    | NegationF p1 => ~ eval_formula_fix p1
    | ConjunctionF p1 p2 => eval_formula_fix p1 /\ eval_formula_fix p2
    | DisjunctionF p1 p2 => eval_formula_fix p1 \/ eval_formula_fix p2
    | ImplicationF p1 p2 => eval_formula_fix p1 -> eval_formula_fix p2
    | BiconditionalF p1 p2 => eval_formula_fix p1 <-> eval_formula_fix p2
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

  Global Hint Constructors infers : my_hints.

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

Module LindenbaumBooleanAlgebraOnPL.

  Import BasicSetoidTheory MyEnsemble MyEnsembleNova CountableBooleanAlgebra SyntaxOfPL SemanticsOfPL InferenceRulesOfPL.

  Local Program Instance formula_isSetoid : isSetoid formula :=
    { eqProp :=
      fun b1 : formula =>
      fun b2 : formula =>
      \left\{ b1 \right\} |- b2 /\ \left\{ b2 \right\} |- b1
    }
  .

  Next Obligation with eauto with *.
    split.
    - intros b1.
      split; apply ByAssumption...
    - intros b1 b2 [H H0].
      split...
    - intros b1 b2 b3 [H H0] [H1 H2].
      split.
      + apply (cut_property b2 b3 H).
        apply (extend_infers H1)...
      + apply (cut_property b2 b1 H2).
        apply (extend_infers H0)...
  Qed.

  Global Program Instance LindenbaumBooleanAlgebra : @isCBA formula formula_isSetoid :=
    { trueB := ImplicationF ContradictionF ContradictionF
    ; falseB := ContradictionF
    ; negB := NegationF
    ; andB := ConjunctionF
    ; orB := DisjunctionF
    ; enumB := enum_formula
    }
  .

  Next Obligation with eauto with *.
    split.
    - apply NegationI.
      apply (ContradictionI b1).
      + apply (extend_infers H0)...
      + apply ByAssumption...
    - apply NegationI.
      apply (ContradictionI b1').
      + apply (extend_infers H)...
      + apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ConjunctionI.
      + apply (cut_property b1 b1').
        * apply (ConjunctionE1 b1 b2).
          apply ByAssumption...
        * apply (extend_infers H)...
      + apply (cut_property b2 b2').
        * apply (ConjunctionE2 b1 b2).
          apply ByAssumption...
        * apply (extend_infers H0)...
    - apply ConjunctionI.
      + apply (cut_property b1' b1).
        * apply (ConjunctionE1 b1' b2').
          apply ByAssumption...
        * apply (extend_infers H2)...
      + apply (cut_property b2' b2).
        * apply (ConjunctionE2 b1' b2').
          apply ByAssumption...
        * apply (extend_infers H1)...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 b2 (DisjunctionF b1' b2')).
      + apply ByAssumption...
      + apply (DisjunctionI1 b1' b2').
        apply (extend_infers H)...
      + apply (DisjunctionI2 b1' b2').
        apply (extend_infers H0)...
    - apply (DisjunctionE b1' b2' (DisjunctionF b1 b2)).
      + apply ByAssumption...
      + apply (DisjunctionI1 b1 b2).
        apply (extend_infers H2)...
      + apply (DisjunctionI2 b1 b2).
        apply (extend_infers H1)...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ConjunctionI.
      + apply ConjunctionI.
        * apply (ConjunctionE1 b1 (ConjunctionF b2 b3)).
          apply ByAssumption...
        * apply (ConjunctionE1 b2 b3).
          apply (ConjunctionE2 b1 (ConjunctionF b2 b3)).
          apply ByAssumption...
      + apply (ConjunctionE2 b2 b3).
        apply (ConjunctionE2 b1 (ConjunctionF b2 b3)).
        apply ByAssumption...
    - apply ConjunctionI.
      + apply (ConjunctionE1 b1 b2).
        apply (ConjunctionE1 (ConjunctionF b1 b2) b3).
        apply ByAssumption...
      + apply ConjunctionI.
        * apply (ConjunctionE2 b1 b2).
          apply (ConjunctionE1 (ConjunctionF b1 b2) b3).
          apply ByAssumption...
        * apply (ConjunctionE2 (ConjunctionF b1 b2) b3).
          apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 (DisjunctionF b2 b3)).
      + apply ByAssumption...
      + apply (DisjunctionI1 (DisjunctionF b1 b2) b3).
        apply (DisjunctionI1 b1 b2).
        apply ByAssumption...
      + apply (DisjunctionE b2 b3).
        * apply ByAssumption...
        * apply (DisjunctionI1 (DisjunctionF b1 b2) b3).
          apply (DisjunctionI2 b1 b2).
          apply ByAssumption...
        * apply (DisjunctionI2 (DisjunctionF b1 b2) b3).
          apply ByAssumption...
    - apply (DisjunctionE (DisjunctionF b1 b2) b3).
      + apply ByAssumption...
      + apply (DisjunctionE b1 b2).
        * apply ByAssumption...
        * apply (DisjunctionI1 b1 (DisjunctionF b2 b3)).
          apply ByAssumption...
        * apply (DisjunctionI2 b1 (DisjunctionF b2 b3)).
          apply (DisjunctionI1 b2 b3).
          apply ByAssumption...
      + apply (DisjunctionI2 b1 (DisjunctionF b2 b3)).
        apply (DisjunctionI2 b2 b3).
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ConjunctionE1 b1 b1).
      apply ByAssumption...
    - apply ConjunctionI; apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 b1 b1); apply ByAssumption...
    - apply DisjunctionI1.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ConjunctionI.
      + apply (ConjunctionE2 b1 b2).
        apply ByAssumption...
      + apply (ConjunctionE1 b1 b2).
        apply ByAssumption...
    - apply ConjunctionI.
      + apply (ConjunctionE2 b2 b1).
        apply ByAssumption...
      + apply (ConjunctionE1 b2 b1).
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 b2).
      + apply ByAssumption...
      + apply (DisjunctionI2 b2 b1).
        apply ByAssumption...
      + apply (DisjunctionI1 b2 b1).
        apply ByAssumption...
    - apply (DisjunctionE b2 b1).
      + apply ByAssumption...
      + apply (DisjunctionI2 b1 b2).
        apply ByAssumption...
      + apply (DisjunctionI1 b1 b2).
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b2 b3).
      + apply (ConjunctionE2 b1 (DisjunctionF b2 b3)).
        apply ByAssumption...
      + apply DisjunctionI1.
        apply ConjunctionI.
        * apply (ConjunctionE1 b1 (DisjunctionF b2 b3)).
          apply ByAssumption...
        * apply ByAssumption...
      + apply DisjunctionI2.
        apply ConjunctionI.
        * apply (ConjunctionE1 b1 (DisjunctionF b2 b3)).
          apply ByAssumption...
        * apply ByAssumption...
    - apply (DisjunctionE (ConjunctionF b1 b2) (ConjunctionF b1 b3)).
      + apply ByAssumption...
      + apply ConjunctionI.
        * apply (ConjunctionE1 b1 b2).
          apply ByAssumption...
        * apply DisjunctionI1.
          apply (ConjunctionE2 b1 b2).
          apply ByAssumption...
      + apply ConjunctionI.
        * apply (ConjunctionE1 b1 b3).
          apply ByAssumption...
        * apply DisjunctionI2.
          apply (ConjunctionE2 b1 b3).
          apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ConjunctionI.
      + apply (DisjunctionE b1 (ConjunctionF b2 b3)).
        * apply ByAssumption...
        * apply DisjunctionI1.
          apply ByAssumption...
        * apply DisjunctionI2.
          apply (ConjunctionE1 b2 b3).
          apply ByAssumption...
      + apply (DisjunctionE b1 (ConjunctionF b2 b3)).
        * apply ByAssumption...
        * apply DisjunctionI1.
          apply ByAssumption...
        * apply DisjunctionI2.
          apply (ConjunctionE2 b2 b3).
          apply ByAssumption...
  - apply (DisjunctionE b1 b2).
    + apply (ConjunctionE1 (DisjunctionF b1 b2) (DisjunctionF b1 b3)).
      apply ByAssumption...
    + apply DisjunctionI1.
      apply ByAssumption...
    + apply (DisjunctionE b1 b3).
      * apply (ConjunctionE2 (DisjunctionF b1 b2) (DisjunctionF b1 b3)).
        apply ByAssumption...
      * apply DisjunctionI1.
        apply ByAssumption...
      * apply DisjunctionI2.
        apply ConjunctionI; apply ByAssumption...
        apply in_insert_iff, or_intror...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ConjunctionE1 b1 (DisjunctionF b1 b2)).
      apply ByAssumption...
    - apply ConjunctionI.
      + apply ByAssumption...
      + apply DisjunctionI1.
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 (ConjunctionF b1 b2)).
      + apply ByAssumption...
      + apply ByAssumption...
      + apply (ConjunctionE1 b1 b2).
        apply ByAssumption...
    - apply DisjunctionI1.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ConjunctionE2 b1 ContradictionF).
      apply ByAssumption...
    - apply ConjunctionI.
      + apply ContradictionE.
        apply ByAssumption...
      + apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ImplicationI.
      apply ByAssumption...
    - apply DisjunctionI2.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (DisjunctionE b1 ContradictionF).
      + apply ByAssumption...
      + apply ByAssumption...
      + apply ContradictionE.
        apply ByAssumption...
    - apply DisjunctionI1.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ConjunctionE1 b1 (ImplicationF ContradictionF ContradictionF)).
      apply ByAssumption...
    - apply ConjunctionI.
      + apply ByAssumption...
      + apply ImplicationI.
        apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply (ContradictionI b1).
      + apply (ConjunctionE1 b1 (NegationF b1)).
        apply ByAssumption...
      + apply (ConjunctionE2 b1 (NegationF b1)).
        apply ByAssumption...
    - apply ContradictionE.
      apply ByAssumption...
  Qed.

  Next Obligation with eauto with *.
    split.
    - apply ImplicationI.
      apply ByAssumption...
    - apply (extend_infers (Law_of_Exclusive_Middle b1)).
      intros p H.
      apply in_empty_iff in H...
  Qed.

  Next Obligation with eauto with *.
    destruct (formula_is_enumerable b) as [n H]...
  Qed.

  Lemma leq_LBA :
    forall b1 : formula,
    forall b2 : formula,
    andB b1 b2 == b1 <-> \left\{ b1 \right\} |- b2.
  Proof with eauto with *.
    intros b1 b2.
    split.
    - intros [H H0].
      apply (ConjunctionE2 b1 b2)...
    - intros H.
      split.
      + apply (ConjunctionE1 b1 b2).
        apply ByAssumption...
      + apply ConjunctionI.
        * apply ByAssumption...
        * apply H.
  Qed.

  Lemma andBs_LBA :
    forall ps : list formula,
    forall hs : ensemble formula,
    (forall p : formula, In p ps -> member p hs) ->
    forall c : formula,
    \left\{ fold_right andB trueB ps \right\} |- c <-> (exists hs' : ensemble formula, (forall h : formula, In h ps <-> member h hs') /\ hs' |- c).
  Proof with eauto with *.
    induction ps as [| p ps IH]; simpl.
    { intros hs H c.
      split.
      - intros H0.
        exists \emptyset.
        split.
        + intros p.
          rewrite in_empty_iff.
          reflexivity.
        + apply (ConjunctionE2 (ImplicationF ContradictionF ContradictionF) c).
          apply (cut_property (ImplicationF ContradictionF ContradictionF) (ConjunctionF (ImplicationF ContradictionF ContradictionF) c)).
          * apply ImplicationI.
            apply ByAssumption...
          * apply ConjunctionI; [apply ByAssumption | apply (extend_infers H0)]...
      - intros [hs' [H0 H1]].
        assert (claim1 : isSubsetOf hs' \emptyset).
        { intros h.
          rewrite <- (H0 h).
          intros [].
        }
        assert (claim2 : \emptyset |- c) by now apply (extend_infers H1).
        apply (extend_infers claim2)...
    }
    { intros hs H c.
      split.
      - intros H0.
        assert (claim3 : forall h : formula, In h ps -> member h hs) by firstorder.
        assert (claim4 : \left\{ fold_right andB trueB ps \right\} |- ImplicationF p c).
        { apply ImplicationI.
          apply (cut_property (fold_right andB trueB (p :: ps)) c).
          - simpl.
            apply ConjunctionI; apply ByAssumption...
          - apply (extend_infers H0)...
        }
        destruct (proj1 (IH hs claim3 (ImplicationF p c)) claim4) as [hs' [H1 H2]].
        exists (insert p hs').
        split.
        + intros h.
          rewrite in_insert_iff.
          firstorder.
        + apply (cut_property (ImplicationF p c) c).
          apply (extend_infers H2)...
          apply (ImplicationE p c).
          * apply ByAssumption...
          * apply ByAssumption, in_insert_iff, or_intror...
      - intros [hs' [H0 H1]].
        destruct (in_dec eq_formula_dec p ps) as [H_yes | H_no].
        + assert (claim5 : forall h : formula, In h ps -> member h hs) by firstorder.
          assert (claim6 : exists hs' : ensemble formula, (forall h : formula, In h ps <-> member h hs') /\ hs' |- c).
          { exists hs'.
            split.
            - intros h'.
              split.
              + firstorder.
              + intros H2.
                destruct (proj2 (H0 h') H2) as [H3 | H3].
                * subst...
                * apply H3.
            - apply H1.
          }
          assert (claim7 : \left\{ fold_right andB trueB ps \right\} |- c) by apply (proj2 (IH hs claim5 c) claim6).
          apply (cut_property (fold_right andB trueB ps) c).
          * simpl.
            apply (ConjunctionE2 p (fold_right ConjunctionF (ImplicationF ContradictionF ContradictionF) ps)).
            apply ByAssumption...
          * apply (extend_infers claim7)...
        + assert (claim8 : forall h : formula, In h ps -> member h (delete p hs)).
          { intros h H2.
            apply in_delete_iff.
            split...
            intros Heq.
            subst...
          }
          assert (claim9 : exists hs' : ensemble formula, (forall h : formula, In h ps <-> member h hs') /\ hs' |- ImplicationF p c).
          { exists (delete p hs').
            split.
            - intros h.
              rewrite in_delete_iff, <- H0.
              split.
              + intros H2.
                split...
                intros Heq.
                subst...
              + intros [[H2 | H2] H3]...
                subst; contradiction.
            - apply ImplicationI.
              apply (extend_infers H1).
              intros h' H2.
              rewrite in_insert_iff, in_delete_iff.
              destruct (eq_formula_dec h' p)...
          }
        assert (claim10 : \left\{ fold_right andB trueB ps \right\} |- ImplicationF p c) by apply (proj2 (IH (delete p hs) claim8 (ImplicationF p c)) claim9).
        apply (ImplicationE p c).
        { apply (cut_property (fold_right andB trueB ps) (ImplicationF p c)); simpl.
          - apply (ConjunctionE2 p (fold_right ConjunctionF (ImplicationF ContradictionF ContradictionF) ps)).
            apply ByAssumption...
          - apply (extend_infers claim10)...
        }
        { apply (ConjunctionE1 p (fold_right ConjunctionF (ImplicationF ContradictionF ContradictionF) ps)).
          apply ByAssumption...
        }
    }
  Qed.

End LindenbaumBooleanAlgebraOnPL.
