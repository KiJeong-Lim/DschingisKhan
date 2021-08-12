Require Import Coq.Lists.List.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.
Require Import DschingisKhan.projects.PropositionalLogic.Basics.
Require Import DschingisKhan.projects.PropositionalLogic.ClassicalMetaTheories.
Require Import DschingisKhan.projects.PropositionalLogic.ConstructiveMetaTheories.

Module PropositionLogic.

  Import MyEnsemble MyEnsembleNova ConstructiveMetaTheoryOnPropositonalLogic SyntaxOfPL SemanticsOfPL InferenceRulesOfPL ConstructiveMetaTheoryOnPropositonalLogic SoundnessOfPL CompletenessOfPL.

  Theorem infers_iff_entails (hs : ensemble formula) (c : formula) :
    hs |- c <-> hs |= c.
  Proof.
    split.
    - apply SoundnessOfPropositionalLogic.
    - apply CompletenessOfPropositionalLogic.
  Qed.

End PropositionLogic.
