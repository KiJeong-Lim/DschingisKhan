Require Import Coq.Lists.List.
Require Import DschingisKhan.classical.ExclusiveMiddle.
Require Import DschingisKhan.pure.CBA.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.
Require Import DschingisKhan.projects.PropositionalLogic.Basics.
Require Import DschingisKhan.projects.PropositionalLogic.ClassicalMetaTheories.
Require Import DschingisKhan.projects.PropositionalLogic.ConstructiveMetaTheories.

Module PropositionLogic.

  Import MyEnsemble MyEnsembleNova ClassicalLogic SyntaxOfPL SemanticsOfPL InferenceRulesOfPL SoundnessOfPL CountableBooleanAlgebra ClassicalLogic LindenbaumBooleanAlgebraOnPL ConstructiveMetaTheoryOnPropositonalLogic.

  Theorem infers_iff_entails (hs : ensemble formula) (c : formula) :
    hs |- c <-> hs |= c.
  Proof.
    intros hs c.
    split.
    - apply SoundnessOfPropositionalLogic.
    - apply CompletenessOfPropositionalLogic.
  Qed.

End PropositionLogic.
