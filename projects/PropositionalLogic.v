Require Import Coq.Lists.List.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.
Require Import DschingisKhan.projects.PropositionalLogic.Basics.
Require Import DschingisKhan.projects.PropositionalLogic.ClassicalMetaTheories.
Require Import DschingisKhan.projects.PropositionalLogic.ConstructiveMetaTheories.

Module PropertiesOfPropositionLogic.

  Import MyEnsemble MyEnsembleNova SyntaxOfPL SemanticsOfPL InferenceRulesOfPL ConstructiveMetaTheoryOnPropositonalLogic SoundnessOfPropositionLogic CompletenessOfPropositionLogic.

  Theorem infers_iff_entails (hs : ensemble formula) (c : formula) :
    hs |- c <-> hs |= c.
  Proof.
    split.
    - exact (the_propositional_soundness_theorem hs c).
    - exact (the_propositional_completeness_theorem hs c).
  Qed.

  Theorem the_propositional_compactness_theorem (hs : ensemble formula) (c : formula) :
    hs |= c <-> (exists ps : list formula, (forall p : formula, In p ps -> member p hs) /\ (exists hs0 : ensemble formula, (forall h : formula, In h ps <-> member h hs0) /\ hs0 |= c)).
  Proof with try now firstorder.
    split.
    - intros hs_entails_c.
      assert (hs_infers_c := proj2 (infers_iff_entails hs c) hs_entails_c).
      destruct (infers_has_compactness hs c hs_infers_c) as [ps [hs0_subseteq_hs [hs0 [hs0_finite hs0_infers_c]]]].
      assert (hs0_entails_c := proj1 (infers_iff_entails hs0 c) hs0_infers_c)...
    - intros [ps [hs0_subseteq_hs [hs0 [hs0_finite hs0_entails_c]]]].
      apply (extend_entails hs0_entails_c)...
  Qed.

End PropertiesOfPropositionLogic.
