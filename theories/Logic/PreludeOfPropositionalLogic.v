Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.
Require Import DschingisKhan.Math.BasicPosetTheory.

Module SyntaxOfPropositionalLogic.

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
    induction lhs, rhs...
    { destruct (eq_dec i i0)... }
    { destruct (IHlhs rhs)... }
    { destruct (IHlhs1 rhs1); destruct (IHlhs2 rhs2)... }
    { destruct (IHlhs1 rhs1); destruct (IHlhs2 rhs2)... }
    { destruct (IHlhs1 rhs1); destruct (IHlhs2 rhs2)... }
    { destruct (IHlhs1 rhs1); destruct (IHlhs2 rhs2)... }
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
      | S (S (S (S (S (S i))))) => AtomF i
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
      - assert (H0 : cantor_pairing (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i)))))) = (0, S (S (S (S (S (S i))))))) by now apply claim1.
        exists (sum_from_0_to (0 + S (S (S (S (S (S i)))))) + S (S (S (S (S (S i))))))...
    }
    all: intros r H; set (rank := pred r); assert (H0 : S rank = r) by (now apply (suc_pred_n_eq_n_if_m_lt_n H)); rewrite <- H0.
    { set (piece := 0).
      exists (piece)...
    }
    { set (piece := 1).
      assert (H1 : getRankOfFormula p1 <= rank) by now apply n_le_pred_m_if_n_lt_m.
      destruct (IH1 rank H1) as [seed2 H2].
      assert (H3 : cantor_pairing (sum_from_0_to (seed2 + piece) + piece) = (seed2, piece)) by now apply claim1.
      exists (sum_from_0_to (seed2 + piece) + piece)...
    }
    { set (piece := 2).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply n_le_pred_m_if_n_lt_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      destruct (IH1 rank H2) as [seed2 H4].
      destruct (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 3).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply n_le_pred_m_if_n_lt_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      destruct (IH1 rank H2) as [seed2 H4].
      destruct (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 4).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply n_le_pred_m_if_n_lt_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      destruct (IH1 rank H2) as [seed2 H4].
      destruct (IH2 rank H3) as [seed3 H5].
      assert (H6 : cantor_pairing (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
      assert (H7 : cantor_pairing (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
      exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
    }
    { set (piece := 5).
      assert (H1 : max (getRankOfFormula p1) (getRankOfFormula p2) <= rank) by now apply n_le_pred_m_if_n_lt_m.
      assert (H2 : getRankOfFormula p1 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      assert (H3 : getRankOfFormula p2 <= rank) by now apply (le_elim_max_n1_n2_le_m (getRankOfFormula p1) (getRankOfFormula p2)).
      destruct (IH1 rank H2) as [seed2 H4].
      destruct (IH2 rank H3) as [seed3 H5].
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
    : {n : nat | enumFormula n = p}.
  Proof.
    pose proof (specOf_enumFormula' p (getRankOfFormula p) le_reflexitivity) as [seed0 H_EQ].
    exists (cantor_pairing_inv (getRankOfFormula p) seed0). unfold cantor_pairing_inv.
    unfold enumFormula. now repeat rewrite <- cantor_pairing_is_surjective.
  Qed.

  End ENUMERATE_FORMULA.

End SyntaxOfPropositionalLogic.
