Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeClassic.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Math.BasicGeneralTopology.
Require Import DschingisKhan.Logic.ScottTopology.

Module BasicCpoTheory.

  Import MathProps MathClasses BasicPosetTheory BasicGeneralTopology DomainTheoryHelper ScottTopology.

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
  Proof.
    split.
    - intros y z y_in_U_x y_le_z z_le_x. unnw.
      contradiction y_in_U_x. now transitivity (z).
    - intros X X_nonempty X_isDirected sup_X sup_X_isSupremumOf_X sup_X_in_U_x. unnw.
      assert (JunyoungJang'sAdvice : ~ << UPPER_BOUND : forall z : D, member z X -> z =< x >>).
      { intros UPPER_BOUND. contradiction (sup_X_in_U_x). now eapply sup_X_isSupremumOf_X. }
      pose proof (ExclusiveMiddle.classic (exists z : D, z \in X /\ z \in U x)) as [H_yes | H_no]; trivial.
      contradiction JunyoungJang'sAdvice. intros y y_in_X.
      pose proof (ExclusiveMiddle.classic (y =< x)) as [y_le_x | y_in_U_x]; trivial.
      contradiction H_no. now exists (y).
  Qed.

End BasicCpoTheory.
