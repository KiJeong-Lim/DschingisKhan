Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Data.InteractionTree.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Logic.ConstructiveDomainTheory.

Module InteractionTreeTheory.

  Import InteractionTrees BasicPosetTheory BasicCoLaTheory ParameterizedCoinduction.

  Section ITREE_EQUIVALENCE_RELATION.

  Context {E : Type -> Type} {R : Type} {requiresSetoid : isSetoid R}.

  Lemma eqITreeF_isMonotonicMap
    : isMonotonicMap (fun BISIM : ensemble (itree E R * itree E R) => eqITreeF BISIM).
  Proof. exact (eqITreeF_monotonic). Defined.

  Definition eqITree (lhs : itree E R) (rhs : itree E R) : Prop :=
    member (lhs, rhs) (paco eqITreeF cola_empty)
  .

  Lemma eqITree_iff_itreeBisim (lhs : itree E R) (rhs : itree E R)
    : eqITree lhs rhs <-> itreeBisim lhs rhs.
  Proof.
    revert lhs rhs. keep (uncurry itreeBisim) as itreeBisim' into (ensemble (itree E R * itree E R)).
    set (f := @exist (ensemble (itree E R * itree E R) -> ensemble (itree E R * itree E R)) isMonotonicMap eqITreeF eqITreeF_isMonotonicMap).
    enough (claim1 : isSubsetOf itreeBisim' (proj1_sig f itreeBisim')).
    enough (claim2 : isSupremumOf itreeBisim' (PostfixedPoints (proj1_sig f))).
    enough (claim3 : paco eqITreeF cola_empty == itreeBisim').
    - ii. exact (claim3 (lhs, rhs)).
    - eapply @Supremum_preserves_eqProp_wrtEnsembles with (requiresPoset := ensemble_isPoset (itree E R * itree E R)%type) (X1 := PostfixedPoints (proj1_sig f)) (X2 := PostfixedPoints (proj1_sig f)).
      + rewrite paco_init with (F_monotonic := eqITreeF_isMonotonicMap). eapply nu_isSupremumOf_PostfixedPoints.
      + exact (claim2).
      + reflexivity.
    - intros Y. split.
      + intros le_Y X X_in. unnw. do 2 red in X_in. rewrite <- le_Y. intros [lhs rhs] H_in. change (itreeBisim lhs rhs). revert lhs rhs H_in.
        cofix CIH. ii. econstructor. exact (eqITreeF_isMonotonicMap X (uncurry itreeBisim) (fun '(LHS, RHS) => CIH LHS RHS) (lhs, rhs) (X_in (lhs, rhs) H_in)).
      + intros ?; desnw. eapply UPPER_BOUND. exact (claim1).
    - intros [lhs rhs] H_in. eapply unfold_itreeBisim. exact (H_in). 
  Qed.

  End ITREE_EQUIVALENCE_RELATION.

End InteractionTreeTheory.
