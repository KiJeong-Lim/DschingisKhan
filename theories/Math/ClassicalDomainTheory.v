Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeClassic.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Math.BasicGeneralTopology.
Require Import DschingisKhan.Logic.ScottTopology.

Module BasicCpoTheory.

  Import MathProps MathClasses BasicPosetTheory BasicGeneralTopology DomainTheoryHelper ScottTopology ExclusiveMiddle.

  Definition ScottContinuousMaps (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : Type :=
    @sig (Hask.arrow dom cod) (isContinuousMap (dom_isTopology := TopologyOfDanaScott dom) (cod_isTopology := TopologyOfDanaScott cod))
  .

  Local Instance ScottContinuousMaps_asPoset (dom : Type) (cod : Type) {dom_requiresPoset : isPoset dom} {cod_requiresPoset : isPoset cod} : isPoset (ScottContinuousMaps dom cod) :=
    subPoset (Hask.arrow dom cod) (requiresPoset := arrow_isPoset dom cod)
  .

  Local Notation " ⟬ dom ⟶ cod ⟭ " := (ScottContinuousMaps dom cod) : type_scope.

  Definition U {D : Type} {D_isPoset : isPoset D} (x : D) : ensemble D :=
    fun z : D => ~ z =< x
  .

  Lemma U_x_isOpen {D : Type} {D_isPoset : isPoset D} (x : D)
    : isOpen (U x).
  Proof. (* Thanks to Junyoung Jang *)
    split.
    - intros y z y_in_U_x y_le_z z_le_x. unnw. contradiction y_in_U_x. now transitivity (z).
    - intros X [X_nonempty X_isDirected] sup_X sup_X_isSupremumOf_X sup_X_in_U_x. unnw.
      assert (NOT_UPPER_BOUND: ~ << UPPER_BOUND : forall z : D, member z X -> z =< x >>).
      { intros UPPER_BOUND. contradiction sup_X_in_U_x. now eapply sup_X_isSupremumOf_X. }
      eapply NNPP. intros H_false. contradiction NOT_UPPER_BOUND. intros y y_in_X.
      eapply NNPP. intros y_in_U_x. contradiction H_false. now exists (y).
  Qed.

  Lemma ContinuousMap_isMonotonicMap {dom : Type} {cod : Type} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (f : dom -> cod)
    (f_isContinuousMap : isContinuousMap f)
    : isMonotonicMap f.
  Proof.
    intros x1 x2 x1_le_x2. eapply NNPP. intros f_x1_in_U_f_x2.
    assert (x1_in_preimage_f_U_f_x2 : member x1 (preimage f (U (f x2)))) by now econstructor.
    assert (preimage_f_U_f_x2_isOpen : isOpen (preimage f (U (f x2)))) by eapply f_isContinuousMap, U_x_isOpen.
    assert (x2_in_preimage_f_U_f_x2 : member x2 (preimage f (U (f x2)))).
    { inversion preimage_f_U_f_x2_isOpen. eapply UPWARD_CLOSED with (x := x1); eauto. }
    assert (f_x2_in_U_f_x2 : member (f x2) (U (f x2))) by now inversion x2_in_preimage_f_U_f_x2; subst.
    now contradiction f_x2_in_U_f_x2.
  Qed.

End BasicCpoTheory.
