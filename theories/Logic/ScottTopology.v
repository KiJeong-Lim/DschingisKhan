Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Math.BasicGeneralTopology.

Module ScottTopology.

  Import MathProps MathClasses BasicPosetTheory BasicGeneralTopology DomainTheoryHelper.

  Section BUILD_SCOTT_TOPOLOGY.

  Context {D : Type} {requiresPoset : isPoset D}.

  Variant isOpen_Scott (O : ensemble D) : Prop :=
  | ScottTopologyOpen
    (UPWARD_CLOSED : forall x : D, forall y : D, << H_IN : member x O >> -> << H_LE : x =< y >> -> member y O)
    (LIMIT : forall X : ensemble D, << NONEMPTY : exists x : D, member x X >> -> << IS_DIRECTED : isDirectedSubset X >> -> forall sup_X : D, << IS_SUPREMUM : isSupremumOf sup_X X >> -> << SUPREMUM_IN : member sup_X O >> -> exists x : D, member x X /\ member x O)
    : isOpen_Scott O
  .

  Local Hint Constructors isOpen_Scott : core.

  Local Instance theScottTopology
    : Topology_axiom isOpen_Scott.
  Proof with (now vm_compute; firstorder) || (eauto with *).
    split.
    - econstructor; ii; desnw; unnw...
    - ii. econstructor; ii; desnw; unnw...
      apply in_unions_iff in SUPREMUM_IN.
      destruct SUPREMUM_IN as [X_i [sup_X_in_X_i X_i_in_Xs]].
      exploit (every_member_of_Xs_isOpen X_i X_i_in_Xs) as [? ?].
      pose proof (LIMIT X NONEMPTY IS_DIRECTED sup_X IS_SUPREMUM sup_X_in_X_i) as [x [x_in_X x_in_X_i]]...
    - ii. econstructor; ii; desnw; unnw...
      apply in_intersection_iff in SUPREMUM_IN.
      destruct SUPREMUM_IN as [SUPREMUM_IN1 SUPREMUM_IN2].
      destruct XL_isOpen as [XL_UPWARD_CLOSED XL_LIMIT].
      destruct XR_isOpen as [XR_UPWARD_CLOSED XR_LIMIT].
      exploit XL_LIMIT as [x1 [x1_in_X x1_in_XL]]...
      exploit XR_LIMIT as [x2 [x2_in_X x2_in_XR]]...
      pose proof (IS_DIRECTED x1 x1_in_X x2 x2_in_X) as [x3 [x3_in [x1_le_x3 x2_le_x3]]]...
    - ii; desnw; unnw. destruct X_isOpen as [? ?]. econstructor.
      + ii; desnw. rewrite <- X_eq_X'. eapply UPWARD_CLOSED with (x := x)...
      + ii; desnw. unnw. exploit LIMIT as [? [? ?]]...
  Qed.

  End BUILD_SCOTT_TOPOLOGY.

  Global Instance TopologyOfDanaScott (D : Type) {requiresPoset : isPoset D} : isTopologicalSpace D :=
    { isOpen := isOpen_Scott (requiresPoset := requiresPoset)
    ; TopologicalSpace_obeysTopology_axiom := theScottTopology (requiresPoset := requiresPoset)
    }
  .

End ScottTopology.
