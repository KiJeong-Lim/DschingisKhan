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

  Import MathProps MathClasses BasicPosetTheory.

  Create HintDb topology_hints.

  Class Topology_axiom {A : Type} (isOpen : ensemble A -> Prop) : Prop :=
    { full_isOpen
      : isOpen full
    ; unions_isOpen (Xs : ensemble (ensemble A))
      (every_member_of_Xs_isOpen : forall X : ensemble A, << X_in_Xs : member X Xs >> -> isOpen X)
      : isOpen (unions Xs)
    ; intersection_isOpen (XL : ensemble A) (XR : ensemble A)
      (XL_isOpen : isOpen XL)
      (XR_isOpen : isOpen XR)
      : isOpen (intersection XL XR)
    ; isOpen_compatWith_eqProp (X : ensemble A) (X' : ensemble A)
      (X_isOpen : isOpen X)
      (X_eq_X' : X == X')
      : isOpen X'
    }
  .

  Class isTopologicalSpace (A : Type) : Type :=
    { isOpen (O : ensemble A) : Prop
    ; TopologicalSpace_obeysTopology_axiom :> Topology_axiom isOpen
    }
  .

  Global Add Parametric Morphism {A : Type} (requiresTopology : isTopologicalSpace A) :
    (isOpen (isTopologicalSpace := requiresTopology)) with signature (eqProp ==> iff)
    as eqProp_lifts_isOpen.
  Proof. iis; ii; eapply isOpen_compatWith_eqProp; eauto with *. Qed.

  Lemma fullOpen {A : Type} {requiresTopology : isTopologicalSpace A}
    : isOpen (@full A).
  Proof. eapply full_isOpen; eauto. Qed.

  Lemma unionsOpen {A : Type} {requiresTopology : isTopologicalSpace A} (Os : ensemble (ensemble A))
    (every_member_of_Os_isOpen : forall O : ensemble A, member O Os -> isOpen O)
    : isOpen (@unions A Os).
  Proof. eapply unions_isOpen; eauto. Qed.

  Lemma intersectionOpen {A : Type} {requiresTopology : isTopologicalSpace A} (O1 : ensemble A) (O2 : ensemble A)
    (O1_isOpen : isOpen O1)
    (O2_isOpen : isOpen O2)
    : isOpen (@intersection A O1 O2).
  Proof. eapply intersection_isOpen; eauto. Qed.

  Lemma emptyOpen {A : Type} {requiresTopology : isTopologicalSpace A}
    : isOpen (@empty A).
  Proof.
    eapply isOpen_compatWith_eqProp.
    - eapply unions_isOpen with (Xs := empty). ii; desnw.
      apply in_empty_iff in X_in_Xs. tauto.
    - intros z. rewrite in_unions_iff. split.
      + intros [X [z_in_X []]].
      + intros [].
  Qed.

  Global Hint Resolve fullOpen unionsOpen intersectionOpen emptyOpen : topology_hints.

  Definition isContinuousMap {dom : Type} {cod : Type} {dom_isTopology : isTopologicalSpace dom} {cod_isTopology : isTopologicalSpace cod} (f : dom -> cod) : Prop :=
    forall Y : ensemble cod, << TGT_OPEN : isOpen Y >> -> << SRC_OPEN : isOpen (preimage f Y) >>
  .

  Section SUBTOPOLOGY.

  Context {A : Type} (phi : A -> Prop).

  Let Subspace : Type := @sig A phi.

  Context {requiresTopology : isTopologicalSpace A}.

  Definition isOpen_inSubspace (O_repr : ensemble Subspace) : Prop :=
    exists O : ensemble A, isFilterReprOf phi O_repr O /\ isOpen O
  .

  Local Hint Unfold isOpen_inSubspace : core.

  Global Instance Subtopology
    : Topology_axiom isOpen_inSubspace.
  Proof with (now vm_compute; firstorder) || (eauto with *).
    split.
    - exists (full). split...
    - intros Xs H_Xs. exists (unions (bind Xs (fun O_repr : ensemble Subspace => fun O : ensemble A => isFilterReprOf phi O_repr O /\ isOpen O))). split... eapply unions_isOpen...
    - intros X1 X2 [O1 [O1_repr O1_open]] [O2 [O2_repr O2_open]]. exists (intersection O1 O2). split...
    - intros X X' [O [O_repr O_open]] X_eq_X'...
  Qed.

  End SUBTOPOLOGY.

  Local Instance SubspaceTopology {A : Type} {requiresTopology : isTopologicalSpace A} (phi : A -> Prop) : isTopologicalSpace (@sig A phi) :=
    { isOpen := @isOpen_inSubspace A phi requiresTopology
    ; TopologicalSpace_obeysTopology_axiom := @Subtopology A phi requiresTopology
    }
  .

  Lemma proj1_sig_isContinuousMap_fromSubspaceTopology {A : Type} {requiresTopology : isTopologicalSpace A} (X : ensemble A)
    : isContinuousMap (dom := @sig A X) (cod := A) (@proj1_sig A X).
  Proof with eauto with *. ii; desnw; unnw. exists (Y). split... eapply isFilterReprOf_iff... Qed.

End BasicGeneralTopology.
