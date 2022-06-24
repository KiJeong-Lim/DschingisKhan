Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Math.BooleanAlgebra.

Module SyntaxOfPL.

  Definition propVar : Set := nat.

  Inductive formula : Set :=
  | AtomF (i : propVar) : formula
  | ContradictionF : formula
  | NegationF (p1 : formula) : formula
  | ConjunctionF (p1 : formula) (p2 : formula) : formula
  | DisjunctionF (p1 : formula) (p2 : formula) : formula
  | ImplicationF (p1 : formula) (p2 : formula) : formula
  | BiconditionalF (p1 : formula) (p2 : formula) : formula
  .

  Global Instance formulaEqDec
    : EqDec formula.
  Proof with try ((left; congruence) || (right; congruence)).
    change (forall lhs : formula, forall rhs : formula, {lhs = rhs} + {lhs <> rhs}).
    induction lhs as [i | | p1 IH1 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2], rhs as [i' | | p1' | p1' p2' | p1' p2' | p1' p2' | p1' p2']...
    { pose proof (eq_dec i i') as [i_eq_i' | i_ne_i']... }
    { pose proof (IH1 p1') as [p1_eq_p1' | p1_ne_p1']... }
    { pose proof (IH1 p1') as [p1_eq_p1' | p1_ne_p1']; pose proof (IH2 p2') as [p2_eq_p2' | p2_ne_p2']... }
    { pose proof (IH1 p1') as [p1_eq_p1' | p1_ne_p1']; pose proof (IH2 p2') as [p2_eq_p2' | p2_ne_p2']... }
    { pose proof (IH1 p1') as [p1_eq_p1' | p1_ne_p1']; pose proof (IH2 p2') as [p2_eq_p2' | p2_ne_p2']... }
    { pose proof (IH1 p1') as [p1_eq_p1' | p1_ne_p1']; pose proof (IH2 p2') as [p2_eq_p2' | p2_ne_p2']... }
  Defined.

  Section ENUMERATE_FORMULA.

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

  Local Notation plus6 i := (S (S (S (S (S (S i)))))).

  Fixpoint enumFormula' (rank : nat) (seed0 : nat) {struct rank} : formula :=
    match rank with
    | zero => AtomF seed0
    | suc rank' =>
      let seed1 : nat := fst (cantor_pairing seed0) in
      let piece : nat := snd (cantor_pairing seed0) in
      let seed2 : nat := fst (cantor_pairing seed1) in
      let seed3 : nat := snd (cantor_pairing seed1) in
      match piece with
      | 0 => ContradictionF
      | 1 => NegationF (enumFormula' rank' seed1)
      | 2 => ConjunctionF (enumFormula' rank' seed2) (enumFormula' rank' seed3)
      | 3 => DisjunctionF (enumFormula' rank' seed2) (enumFormula' rank' seed3)
      | 4 => ImplicationF (enumFormula' rank' seed2) (enumFormula' rank' seed3)
      | 5 => BiconditionalF (enumFormula' rank' seed2) (enumFormula' rank' seed3)
      | plus6 i => AtomF i
      end
    end
  .

  Local Tactic Notation "tac_aux1" :=
    match goal with
    | [ H : cantor_pairing ?seed = ?rhs |- _ ] => rewrite H; simpl
    end
  .

  Local Tactic Notation "tac_aux2" :=
    match goal with
    | [ H : enumFormula' ?rank ?seed = ?p |- _ ] => rewrite <- H
    end
  .

  Local Tactic Notation "tac" := (unfold enumFormula'); (repeat tac_aux1); (repeat tac_aux2); (eauto).

  Lemma specOf_enumFormula' (p : formula) (rank : nat)
    (RANK_LE : getRankOfFormula p <= rank)
    : {seed0 : nat | enumFormula' rank seed0 = p}.
  Proof with tac.
    revert p rank RANK_LE.
    pose proof (claim1 := fun x : nat => fun y : nat => fun z : nat => proj2 (cantor_pairing_spec x y z)).
    induction p as [i | | p1 IH1 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2]; simpl.
    { intros [ | r'] H.
      - exists (i)...
      - assert (H0 : cantor_pairing (sum_from_0_to (0 + plus6 i) + plus6 i) = (0, plus6 i)) by now apply claim1.
        exists (sum_from_0_to (0 + plus6 i) + plus6 i)...
    }
    all: intros r H; set (rank := pred r); (assert (H0 : S rank = r) by now apply (suc_pred_n_eq_n_if_m_lt_n H)); rewrite <- H0.
    { set (piece := 0).
      exists (piece)...
    }
    { set (piece := 1).
      assert (H1 : getRankOfFormula p1 <= rank) by now apply n_le_pred_m_if_n_lt_m.
      pose proof (IH1 rank H1) as [seed2 H2].
      assert (H3 : cantor_pairing (sum_from_0_to (seed2 + piece) + piece) = (seed2, piece)) by now apply claim1.
      exists (sum_from_0_to (seed2 + piece) + piece)...
    }
    { set (piece := 2).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply n_le_pred_m_if_n_lt_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      pose proof (IH1 rank H2) as [seed2 H4].
      pose proof (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 3).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply n_le_pred_m_if_n_lt_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      pose proof (IH1 rank H2) as [seed2 H4].
      pose proof (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 4).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply n_le_pred_m_if_n_lt_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      pose proof (IH1 rank H2) as [seed2 H4].
      pose proof (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 5).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply n_le_pred_m_if_n_lt_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      pose proof (IH1 rank H2) as [seed2 H4].
      pose proof (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
  Qed.

  Definition enumFormula (seed : nat) : formula :=
    let rank : nat := fst (cantor_pairing seed) in
    let seed0 : nat := snd (cantor_pairing seed) in
    enumFormula' rank seed0
  .

  Theorem formula_is_enumerable (p : formula)
    : {seed : nat | enumFormula seed = p}.
  Proof.
    pose proof (specOf_enumFormula' p (getRankOfFormula p) le_reflexitivity) as [seed0 H_EQ].
    exists (cantor_pairing_inv (getRankOfFormula p) seed0). unfold cantor_pairing_inv, enumFormula.
    now repeat rewrite <- cantor_pairing_is_surjective.
  Qed.

  Corollary enumFormula_isSurjective
    : isSurjective enumFormula.
  Proof. intros p. pose proof (formula_is_enumerable p) as [seed H_EQ]. now exists (seed). Qed.

  Global Instance formula_isCountable : isCountable formula :=
    { enum := enumFormula
    ; enum_isSurjective := enumFormula_isSurjective
    }
  .

  Corollary enumFormula_isSurjection
    : isSurjection enumFormula.
  Proof. intros p. pose proof (formula_is_enumerable p) as [seed H_EQ]. now exists (seed). Qed.

  Global Instance formula_isRecursivelyEnumerable : isRecursivelyEnumerable formula :=
    { RecursivelyEnumerable_requiresCountable := formula_isCountable
    ; enum_isSurjection := enumFormula_isSurjection
    }
  .

  End ENUMERATE_FORMULA.

End SyntaxOfPL.

Module FormulaNotationsOfPL.

  Import SyntaxOfPL.

  Global Declare Scope pl_formula_scope.
  Global Bind Scope pl_formula_scope with formula.
  Global Declare Custom Entry pl_formula_viewer.
  Global Open Scope pl_formula_scope.

  Global Notation " 'p_{' i  '}' " := (AtomF i) (in custom pl_formula_viewer at level 0).
  Global Notation " '_|_' " := (ContradictionF) (in custom pl_formula_viewer at level 0, no associativity).
  Global Notation " '~' p1 " := (NegationF p1) (in custom pl_formula_viewer at level 1, right associativity).
  Global Notation " p1 '/\' p2 " := (ConjunctionF p1 p2) (in custom pl_formula_viewer at level 1, right associativity).
  Global Notation " p1 '\/' p2 " := (DisjunctionF p1 p2) (in custom pl_formula_viewer at level 2, right associativity).
  Global Notation " p1 '->' p2 " := (ImplicationF p1 p2) (in custom pl_formula_viewer at level 2, right associativity).
  Global Notation " p1 '<->' p2 " := (BiconditionalF p1 p2) (in custom pl_formula_viewer at level 2, no associativity).
  Global Notation " p " := p (in custom pl_formula_viewer at level 0, p ident).
  Global Notation " '(' p ')' " := p (in custom pl_formula_viewer, p at level 3).
  Global Notation " '\pl[' p  ']' " := p (p custom pl_formula_viewer at level 3, at level 0, no associativity) : pl_formula_scope.

End FormulaNotationsOfPL.

Module SemanticsOfPL.

  Import SyntaxOfPL FormulaNotationsOfPL.

  Definition truth_value : Type := Prop.

  Global Delimit Scope type_scope with truth_value.

  Definition propVarEnv : Type := propVar -> truth_value.

  Fixpoint evalFormula (env : propVarEnv) (p : formula) {struct p} : truth_value :=
    match p with
    | \pl[ p_{ i } ] => env i
    | \pl[ _|_ ] => False
    | \pl[ ~ p1 ] => ~ evalFormula env p1
    | \pl[ p1 /\ p2 ] => evalFormula env p1 /\ evalFormula env p2
    | \pl[ p1 \/ p2 ] => evalFormula env p1 \/ evalFormula env p2
    | \pl[ p1 -> p2 ] => evalFormula env p1 -> evalFormula env p2
    | \pl[ p1 <-> p2 ] => evalFormula env p1 <-> evalFormula env p2
    end
  .

  Variant satisfies (env : propVarEnv) (A : formula) : Prop :=
  | IsModel
    (EVAL_TO_TRUE : evalFormula env A)
    : satisfies env A
  .

  Global Infix " `satisfies` " := satisfies (at level 70, no associativity) : type_scope.

  Definition entails (Gamma : ensemble formula) (A : formula) : Prop :=
    forall env : propVarEnv, forall env_satisfies : forall B : formula, forall B_IN : B \in Gamma, env `satisfies` B, env `satisfies` A
  .

  Global Infix " ⊧ " := entails (at level 70, no associativity) : type_scope.

  Lemma extend_entails (Gamma1 : ensemble formula) (Gamma2 : ensemble formula) (C : formula)
    (ENTAILS : Gamma1 ⊧ C)
    (Gamma1_isSubsetOf_Gamma2 : isSubsetOf Gamma1 Gamma2)
    : Gamma2 ⊧ C.
  Proof. ii. eauto with *. Qed.

  Definition isStructure (Gamma : ensemble formula) : Prop :=
    forall A : formula, A \in Gamma <-> evalFormula (preimage AtomF Gamma) A
  .

  Lemma structure_gives_its_subset_to_model (Gamma : ensemble formula) (Gamma' : ensemble formula)
    (IS_STRUCTURE : isStructure Gamma')
    (SUBSET : isSubsetOf Gamma Gamma')
    : << MODEL : forall B : formula, B \in Gamma -> preimage AtomF Gamma' `satisfies` B >>.
  Proof. ii. econstructor. eapply IS_STRUCTURE. eauto with *. Qed.

End SemanticsOfPL.

Module InferenceRulesOfPL.

  Import SyntaxOfPL FormulaNotationsOfPL.

  Global Reserved Infix " ⊢ " (at level 70, no associativity).

  Inductive infers (Gamma : ensemble formula) : forall C : formula, Prop :=
  | ByAssumption :
    forall C : formula,
    C \in Gamma ->
    Gamma ⊢ C
  | ContradictionI :
    forall A : formula,
    Gamma ⊢ A ->
    Gamma ⊢ NegationF A ->
    Gamma ⊢ ContradictionF
  | ContradictionE :
    forall A : formula,
    Gamma ⊢ ContradictionF ->
    Gamma ⊢ A
  | NegationI :
    forall A : formula,
    insert A Gamma ⊢ ContradictionF ->
    Gamma ⊢ NegationF A
  | NegationE :
    forall A : formula,
    insert (NegationF A) Gamma ⊢ ContradictionF ->
    Gamma ⊢ A
  | ConjunctionI :
    forall A : formula,
    forall B : formula,
    Gamma ⊢ A ->
    Gamma ⊢ B ->
    Gamma ⊢ ConjunctionF A B
  | ConjunctionE1 :
    forall A : formula,
    forall B : formula,
    Gamma ⊢ ConjunctionF A B ->
    Gamma ⊢ A
  | ConjunctionE2 :
    forall A : formula,
    forall B : formula,
    Gamma ⊢ ConjunctionF A B ->
    Gamma ⊢ B
  | DisjunctionI1 :
    forall A : formula,
    forall B : formula,
    Gamma ⊢ A ->
    Gamma ⊢ DisjunctionF A B
  | DisjunctionI2 :
    forall A : formula,
    forall B : formula,
    Gamma ⊢ B ->
    Gamma ⊢ DisjunctionF A B
  | DisjunctionE :
    forall A : formula,
    forall B : formula,
    forall C : formula,
    Gamma ⊢ DisjunctionF A B ->
    insert A Gamma ⊢ C ->
    insert B Gamma ⊢ C ->
    Gamma ⊢ C
  | ImplicationI :
    forall A : formula,
    forall B : formula,
    insert A Gamma ⊢ B ->
    Gamma ⊢ ImplicationF A B
  | ImplicationE :
    forall A : formula,
    forall B : formula,
    Gamma ⊢ ImplicationF A B ->
    Gamma ⊢ A ->
    Gamma ⊢ B
  | BiconditionalI :
    forall A : formula,
    forall B : formula,
    insert A Gamma ⊢ B ->
    insert B Gamma ⊢ A ->
    Gamma ⊢ BiconditionalF A B
  | BiconditionalE1 :
    forall A : formula,
    forall B : formula,
    Gamma ⊢ BiconditionalF A B ->
    Gamma ⊢ A ->
    Gamma ⊢ B
  | BiconditionalE2 :
    forall A : formula,
    forall B : formula,
    Gamma ⊢ BiconditionalF A B ->
    Gamma ⊢ B ->
    Gamma ⊢ A
  where " Gamma ⊢ C " := (infers Gamma C) : type_scope.

  Local Hint Constructors infers : core.

  Lemma Law_of_Exclusive_Middle (A : formula)
    : empty ⊢ \pl[ A \/ ~ A ].
  Proof with exact (eq_refl).
    eapply NegationE, ContradictionI.
    - eapply DisjunctionI2, NegationI, ContradictionI.
      + eapply DisjunctionI1, ByAssumption. left...
      + eapply ByAssumption. right; left...
    - eapply ByAssumption. left...
  Qed.

  Lemma Cut_property (Gamma : ensemble formula) (A : formula) (B : formula)
    (INFERS : Gamma ⊢ A)
    (CUT : insert A Gamma ⊢ B)
    : Gamma ⊢ B.
  Proof. assert (claim1 : Gamma ⊢ \pl[ A -> B ]); eauto with *. Qed.

  Lemma extend_infers (Gamma : ensemble formula) (Gamma' : ensemble formula) (C : formula)
    (INFERS : Gamma ⊢ C)
    (Gamma_isSubsetOf_Gamma' : isSubsetOf Gamma Gamma')
    : Gamma' ⊢ C.
  Proof with eauto with *.
    revert Gamma' Gamma_isSubsetOf_Gamma'.
    induction INFERS; ii.
    - eapply ByAssumption...
    - eapply ContradictionI...
    - eapply ContradictionE...
    - eapply NegationI...
    - eapply NegationE...
    - eapply ConjunctionI...
    - eapply ConjunctionE1...
    - eapply ConjunctionE2...
    - eapply DisjunctionI1...
    - eapply DisjunctionI2...
    - eapply DisjunctionE...
    - eapply ImplicationI...
    - eapply ImplicationE...
    - eapply BiconditionalI...
    - eapply BiconditionalE1...
    - eapply BiconditionalE2...
  Qed.

End InferenceRulesOfPL.

Module LindenbaumBooleanAlgebraOfPL.

  Import ListNotations BooleanAlgebra CountableBooleanAlgebra SyntaxOfPL InferenceRulesOfPL.

  Global Instance formula_hasBooleanAlgebraMethods : BooleanAlgebra_sig formula :=
    { andBA := ConjunctionF
    ; orBA := DisjunctionF
    ; notBA := NegationF
    ; trueBA := ImplicationF ContradictionF ContradictionF
    ; falseBA := ContradictionF
    }
  .

  Local Obligation Tactic := intros.

  Global Program Instance formula_isSetoid : isSetoid formula :=
    { eqProp (lhs : formula) (rhs : formula) := singleton lhs ⊢ rhs /\ singleton rhs ⊢ lhs }.
  Next Obligation with eauto with *.
    split.
    - ii. split; eapply ByAssumption...
    - ii. des...
    - ii. des.
      all: eapply Cut_property...
      all: eapply extend_infers...
      all: ii; left...
  Qed.


  Local Instance LBA_obeysBooleanAlgebra_axiom
    : BooleanAlgebra_axiom formula (requiresSetoid := formula_isSetoid) (requiresBooleanAlgebraMethods := formula_hasBooleanAlgebraMethods).
  Proof with reflexivity || eauto with *.
    split; iis; simpl in *; des.
    { eapply ConjunctionI.
      - eapply Cut_property with (A := lhs1).
        + eapply ConjunctionE1, ByAssumption...
        + eapply extend_infers... ii; left...
      - eapply Cut_property with (A := lhs2).
        + eapply ConjunctionE2, ByAssumption...
        + eapply extend_infers... ii; left...
    }
    { eapply ConjunctionI.
      - eapply Cut_property with (A := rhs1).
        + eapply ConjunctionE1, ByAssumption...
        + eapply extend_infers... ii; left...
      - eapply Cut_property with (A := rhs2).
        + eapply ConjunctionE2, ByAssumption...
        + eapply extend_infers... ii; left...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply DisjunctionI1, extend_infers... ii; left...
      - eapply DisjunctionI2, extend_infers... ii; left...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply DisjunctionI1, extend_infers... ii; left...
      - eapply DisjunctionI2, extend_infers... ii; left...
    }
    { eapply NegationI. eapply ContradictionI with (A := lhs1).
      - eapply extend_infers... ii; left...
      - eapply ByAssumption. right...
    }
    { eapply NegationI. eapply ContradictionI with (A := rhs1).
      - eapply extend_infers... ii; left...
      - eapply ByAssumption. right...
    }
    { eapply ConjunctionI.
      - eapply ConjunctionI.
        + eapply ConjunctionE1, ByAssumption...
        + eapply ConjunctionE1, ConjunctionE2, ByAssumption...
      - eapply ConjunctionE2, ConjunctionE2, ByAssumption...
    }
    { eapply ConjunctionI.
      - eapply ConjunctionE1, ConjunctionE1, ByAssumption...
      - eapply ConjunctionI.
        + eapply ConjunctionE2, ConjunctionE1, ByAssumption...
        + eapply ConjunctionE2, ByAssumption...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply DisjunctionI1, DisjunctionI1, ByAssumption. left...
      - eapply DisjunctionE.
        + eapply ByAssumption. left...
        + eapply DisjunctionI1, DisjunctionI2, ByAssumption. left...
        + eapply DisjunctionI2, ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply DisjunctionE.
        + eapply ByAssumption. left...
        + eapply DisjunctionI1, ByAssumption. left...
        + eapply DisjunctionI2, DisjunctionI1, ByAssumption. left...
      - eapply DisjunctionI2, DisjunctionI2, ByAssumption. left...
    }
    { eapply ConjunctionI.
      - eapply ConjunctionE2, ByAssumption...
      - eapply ConjunctionE1, ByAssumption...
    }
    { eapply ConjunctionI.
      - eapply ConjunctionE2, ByAssumption...
      - eapply ConjunctionE1, ByAssumption...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply DisjunctionI2, ByAssumption. left...
      - eapply DisjunctionI1, ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply DisjunctionI2, ByAssumption. left...
      - eapply DisjunctionI1, ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ConjunctionE2, ByAssumption...
      - eapply DisjunctionI1, ConjunctionI.
        + eapply ConjunctionE1, ByAssumption. right...
        + eapply ByAssumption. left...
      - eapply DisjunctionI2, ConjunctionI.
        + eapply ConjunctionE1, ByAssumption. right...
        + eapply ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply ConjunctionI.
        + eapply ConjunctionE1, ByAssumption. left...
        + eapply DisjunctionI1, ConjunctionE2, ByAssumption. left...
      - eapply ConjunctionI.
        + eapply ConjunctionE1, ByAssumption. left...
        + eapply DisjunctionI2, ConjunctionE2, ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ConjunctionE1, ByAssumption...
      - eapply DisjunctionI1, ConjunctionI.
        + eapply ByAssumption. left...
        + eapply ConjunctionE2, ByAssumption. right...
      - eapply DisjunctionI2, ConjunctionI.
        + eapply ByAssumption. left...
        + eapply ConjunctionE2, ByAssumption. right...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply ConjunctionI.
        + eapply DisjunctionI1, ConjunctionE1, ByAssumption. left...
        + eapply ConjunctionE2, ByAssumption. left...
      - eapply ConjunctionI.
        + eapply DisjunctionI2, ConjunctionE1, ByAssumption. left...
        + eapply ConjunctionE2, ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply ConjunctionI.
        + eapply DisjunctionE.
          * eapply ByAssumption. right...
          * eapply DisjunctionI1, ByAssumption. left...
          * eapply DisjunctionI2, ConjunctionE1, ByAssumption. left...
        + eapply DisjunctionE.
          * eapply ByAssumption. right...
          * eapply DisjunctionI1, ByAssumption. left...
          * eapply DisjunctionI2, ConjunctionE2, ByAssumption. left...
      - eapply ConjunctionI.
        + eapply DisjunctionE.
          * eapply ByAssumption. right...
          * eapply DisjunctionI1, ByAssumption. left...
          * eapply DisjunctionI2, ConjunctionE1, ByAssumption. left...
        + eapply DisjunctionE.
          * eapply ByAssumption. right...
          * eapply DisjunctionI1, ByAssumption. left...
          * eapply DisjunctionI2, ConjunctionE2, ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ConjunctionE1, ByAssumption...
      - eapply DisjunctionI1, ByAssumption. left...
      - eapply DisjunctionE.
        + eapply ConjunctionE2, ByAssumption. right...
        + eapply DisjunctionI1, ByAssumption. left...
        + eapply DisjunctionI2, ConjunctionI.
          * eapply ByAssumption. right; left...
          * eapply ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply ConjunctionI.
        + eapply DisjunctionI1, ConjunctionE1, ByAssumption. left...
        + eapply DisjunctionI1, ConjunctionE2, ByAssumption. left...
      -  eapply ConjunctionI.
        + eapply DisjunctionI2, ByAssumption. left...
        + eapply DisjunctionI2, ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ConjunctionE1, ByAssumption...
      - eapply DisjunctionE.
        + eapply ConjunctionE2, ByAssumption. right...
        + eapply DisjunctionI1, ConjunctionI.
          * eapply ByAssumption. right; left...
          * eapply ByAssumption. left...
        + eapply DisjunctionI2, ByAssumption. left...
      - eapply DisjunctionI2, ByAssumption. left...
    }
    { eapply ConjunctionE2, ByAssumption... }
    { eapply ConjunctionI.
      - eapply ImplicationI, ByAssumption. left...
      - eapply ByAssumption...
    }
    { eapply ConjunctionE1, ByAssumption... }
    { eapply ConjunctionI.
      - eapply ByAssumption...
      - eapply ImplicationI, ByAssumption. left...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply ContradictionE, ByAssumption. left...
      - eapply ByAssumption. left...
    }
    { eapply DisjunctionI2, ByAssumption... }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply ByAssumption. left...
      - eapply ContradictionE, ByAssumption. left...
    }
    { eapply DisjunctionI1, ByAssumption... }
    { eapply ConjunctionE1, ByAssumption... }
    { eapply ConjunctionI.
      - eapply ByAssumption...
      - eapply ContradictionE, ByAssumption...
    }
    { eapply ConjunctionE2, ByAssumption... }
    { eapply ConjunctionI.
      - eapply ContradictionE, ByAssumption...
      - eapply ByAssumption...
    }
    { eapply ImplicationI, ByAssumption. left... }
    { eapply DisjunctionI1, ImplicationI, ByAssumption. left... }
    { eapply ImplicationI, ByAssumption. left... }
    { eapply DisjunctionI2, ImplicationI, ByAssumption. left... }
    { eapply ConjunctionE1, ByAssumption... }
    { eapply ConjunctionI; eapply ByAssumption... }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply ByAssumption. left...
      - eapply ByAssumption. left...
    }
    { eapply DisjunctionI1, ByAssumption... }
    { eapply ConjunctionE1, ByAssumption... }
    { eapply ConjunctionI.
      - eapply ByAssumption...
      - eapply DisjunctionI1, ByAssumption...
    }
    { eapply DisjunctionE.
      - eapply ByAssumption...
      - eapply ByAssumption. left...
      - eapply ConjunctionE1, ByAssumption. left...
    }
    { eapply DisjunctionI1, ByAssumption... }
    { eapply ContradictionI with (A := x).
      - eapply ConjunctionE1, ByAssumption...
      - eapply ConjunctionE2, ByAssumption...
    }
    { eapply ContradictionE, ByAssumption... }
    { eapply ImplicationI, ByAssumption. left... }
    { eapply extend_infers.
      - eapply Law_of_Exclusive_Middle.
      - eapply isSubsetOf_empty_if.
    }
  Qed.

  Global Instance LBA_pl : isBooleanAlgebra formula (requiresSetoid := formula_isSetoid) :=
    { hasBooleanAlgebraMethods := formula_hasBooleanAlgebraMethods
    ; BooleanAlgebra_obeysBooleanAlgebra_axiom := LBA_obeysBooleanAlgebra_axiom
    }
  .

  Global Instance LBA_pl_asCBA : isCBA formula (requiresSetoid := formula_isSetoid) :=
    { CBA_requiresBooleanAlgebra := LBA_pl
    ; CBA_requiresCountable := formula_isCountable
    }
  .

  Lemma leBA_iff (lhs : formula) (rhs : formula)
    : lhs =< rhs <-> singleton lhs ⊢ rhs.
  Proof.
    simpl. split.
    - intros [INFERS INFERS']. eapply Cut_property with (A := ConjunctionF lhs rhs); trivial.
      eapply ConjunctionE2, ByAssumption. left. reflexivity.
    - intros INFERS. split.
      + eapply ConjunctionE1, ByAssumption. reflexivity.
      + eapply ConjunctionI; trivial.
        eapply ByAssumption. reflexivity.
  Qed.

End LindenbaumBooleanAlgebraOfPL.
