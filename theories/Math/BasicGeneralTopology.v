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

End BasicGeneralTopology.
