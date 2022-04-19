Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Math.BasicPosetTheory.

Module BasicGeneralTopology.

  Import MathProps MathClasses.

  Lemma fullOpen {A : Hask.t} {requiresTopology : isTopologicalSpace A}
    : isOpen (@full A).
  Proof. eapply full_isOpen; eauto. Qed.

  Lemma unionsOpen {A : Hask.t} {requiresTopology : isTopologicalSpace A} (Os : ensemble (ensemble A))
    (every_member_of_Os_isOpen : forall O : ensemble A, member O Os -> isOpen O)
    : isOpen (unions Os).
  Proof. eapply unions_isOpen; eauto. Qed.

  Lemma intersectionOpen {A : Hask.t} {requiresTopology : isTopologicalSpace A} (O1 : ensemble A) (O2 : ensemble A)
    (O1_isOpen : isOpen O1)
    (O2_isOpen : isOpen O2)
    : isOpen (intersection O1 O2).
  Proof. eapply intersection_isOpen; eauto. Qed.

  Global Hint Resolve fullOpen unionsOpen intersectionOpen : khan_hints.

  Section SUBTOPOLOGY.

  Context {A : Hask.t}.

  Variable phi : A -> Prop.

  Let Subspace : Hask.t := @sig A phi.

  Context {requiresTopology : isTopologicalSpace A}.

  Definition isOpen_inSubspace (O_repr : ensemble (@sig A phi)) : Prop :=
    exists O : ensemble A, isFilterReprOf phi O_repr O /\ isOpen O
  .

  Local Hint Unfold isOpen_inSubspace : core.

  Global Instance Subtopology
    : Topology_axiom isOpen_inSubspace.
  Proof with (now vm_compute; firstorder) || (eauto with *).
    split.
    - exists (full). split...
    - intros Xs H_Xs. exists (unions (bind Xs (fun X : ensemble Subspace => fun O : ensemble A => isFilterReprOf phi X O /\ isOpen O))).
      cbn. unfold E.ensemble_bind. unfold "\in". split... eapply unions_isOpen...
    - intros X1 X2 [O1 [O1_repr O1_open]] [O2 [O2_repr O2_open]].
      exists (intersection O1 O2). split...
    - intros X X' [O [O_repr O_open]] X_eq_X'...
  Qed.

  End SUBTOPOLOGY.

  Local Instance SubspaceTopology {A : Type} (phi : A -> Prop) {requiresTopology : isTopologicalSpace A} : isTopologicalSpace (@sig A phi) :=
    { isOpen := isOpen_inSubspace phi
    ; TopologicalSpace_obeysTopology_axiom := Subtopology phi
    }
  .

  Section ScottTopology.

  Context {D : Type} {requiresPoset : isPoset D}.

  Variant isOpen_Scott (O : ensemble D) : Prop :=
  | ScottTopologyOpen
    (UPWARD_CLOSED : forall x : D, forall y : D, << H_IN : member x O >> -> << H_LE : x =< y >> -> member y O)
    (LIMIT : forall X : ensemble D, << H_NONEMPTY : exists x : D, member x X >> -> << IS_DIRECTED : isDirectedSubset X >> -> forall sup_X : D, << IS_SUPREMUM : isSupremumOf sup_X X >> -> << SUPREMUM_IN : member sup_X O >> -> << INTERSECTION_NONEMPTY : exists x : D, member x X /\ member x O >>)
    : isOpen_Scott O
  .

  Local Hint Constructors isOpen_Scott : core.

  Local Instance ScottTopology
    : Topology_axiom isOpen_Scott.
  Proof with (now vm_compute; firstorder) || (eauto with *).
    split.
    - econstructor; ii; desnw; unnw...
    - ii. econstructor; ii; desnw; unnw...
      apply in_unions_iff in SUPREMUM_IN.
      destruct SUPREMUM_IN as [X_i [sup_X_in_X_i X_i_in_Xs]].
      exploit (every_member_of_Xs_isOpen X_i X_i_in_Xs) as [? ?].
      pose proof (LIMIT X H_NONEMPTY IS_DIRECTED sup_X IS_SUPREMUM sup_X_in_X_i) as [x [x_in_X x_in_X_i]]...
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

  End ScottTopology.

End BasicGeneralTopology.
