Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module AczelSet.

  Universe AczelSetUniv_lv.

  Monomorphic Definition Univ : Type@{AczelSetUniv_lv + 1} := Type@{AczelSetUniv_lv}.

  Polymorphic Inductive Tree@{AczelSet_lv} : Univ :=
  | Node (children : Type@{AczelSet_lv}) (childtrees : children -> Tree) : Tree
  .

  Polymorphic Definition AczelSet@{lv} : Univ := Tree@{lv}.

  Polymorphic Definition getChildren@{lv} (root : AczelSet@{lv}) : Type@{lv} :=
    match root in Tree return Type@{lv} with
    | Node children childtrees => children
    end
  .

  Polymorphic Definition getChildTrees@{lv} (root : AczelSet@{lv}) : getChildren@{lv} root -> AczelSet@{lv} :=
    match root as tree in Tree return getChildren@{lv} tree -> Tree@{lv} with
    | Node children childtrees => childtrees
    end
  .

(** "Relations on Set" *)

  Fixpoint eqTree (lhs : AczelSet) (rhs : AczelSet) : Prop :=
    match lhs in Tree, rhs in Tree return Prop with
    | Node children1 childtrees1, Node children2 childtrees2 => ⟪ lhs_simulates_rhs : forall child1 : children1, exists child2 : children2, eqTree (childtrees1 child1) (childtrees2 child2) ⟫ /\ ⟪ rhs_simulates_lhs : forall child2 : children2, exists child1 : children1, eqTree (childtrees1 child1) (childtrees2 child2) ⟫
    end
  .

  Global Instance eqTree_Reflexive
    : Reflexive eqTree.
  Proof.
    intros x; induction x as [x_children x_childtree IH].
    cbn in *; split; unnw; eauto.
  Qed.

  Global Hint Resolve eqTree_Reflexive : khan_hints.

  Global Instance eqTree_Symmetric
    : Symmetric eqTree.
  Proof.
    intros x; induction x as [x_children x_childtree IH]; intros [y_children y_childtree] [x_sim_y y_sim_x].
    cbn in *; split; unnw; [intros c_y | intros c_x].
    - exploit (y_sim_x c_y) as [c_x hyp_eq1]; eauto.
    - exploit (x_sim_y c_x) as [c_y hyp_eq1]; eauto.
  Qed.

  Global Hint Resolve eqTree_Symmetric : khan_hints.

  Global Instance eqTree_Transitive
    : Transitive eqTree.
  Proof.
    intros x y; revert x; induction y as [y_children y_childtree IH]; intros [x_children x_childtree] [z_children z_childtree] [x_sim_y y_sim_x] [y_sim_z z_sim_y].
    cbn in *; split; unnw; [intros c_x | intros c_z].
    - exploit (x_sim_y c_x) as [c_y hyp_eq1]; exploit (y_sim_z c_y) as [c_z hyp_eq2]; eauto.
    - exploit (z_sim_y c_z) as [c_y hyp_eq1]; exploit (y_sim_x c_y) as [c_x hyp_eq2]; eauto.
  Qed.

  Global Hint Resolve eqTree_Transitive : khan_hints.

  Local Instance equality_Equivalence : Equivalence eqTree :=
    { Equivalence_Reflexive := eqTree_Reflexive
    ; Equivalence_Symmetric := eqTree_Symmetric
    ; Equivalence_Transitive := eqTree_Transitive
    }
  .

  Global Instance AczelSet_isSetoid : isSetoid AczelSet :=
    { eqProp := eqTree
    ; eqProp_Equivalence := equality_Equivalence
    }
  .

  Lemma eqTree_unfold
    : eqTree = (fun lhs : AczelSet => fun rhs : AczelSet => lhs == rhs).
  Proof. reflexivity. Qed.

  Ltac unfold_eqTree := rewrite <- eqTree_unfold in *.

  Definition elem (finger : AczelSet) (hand : AczelSet) : Prop :=
    exists bone : getChildren hand, finger == getChildTrees hand bone
  .

  Global Hint Unfold elem : khan_hints.

  Local Infix " `elem` " := elem (at level 70, no associativity) : type_scope.

  Lemma elem_intro {z : AczelSet} {x : AczelSet} (c_x : getChildren x)
    (z_eq_x_c : z == getChildTrees x c_x)
    : z `elem` x.
  Proof. eauto with *. Qed.

  Lemma eqProp_elem_elem (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (x_eq_y : x == y)
    (y_in_z : y `elem` z)
    : x `elem` z.
  Proof. destruct y_in_z as [c_z y_eq_z_c]. eexists; etransitivity; eauto with *. Qed.

  Lemma elem_eqProp_elem (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (y_eq_z : y == z)
    (x_in_y : x `elem` y)
    : x `elem` z.
  Proof.
    destruct z as [z_children z_childtree]; destruct y as [y_children y_childtree].
    destruct y_eq_z as [y_subset_z_c z_c_subset_y]; destruct x_in_y as [c_y x_eq_y_c].
    destruct (y_subset_z_c c_y) as [c_z c_y_eq_c_z]. eexists; etransitivity; eauto with *.
  Qed.

  Global Add Parametric Morphism :
    elem with signature (eqProp ==> eqProp ==> iff)
    as elem_compatWith_eqProp.
  Proof with eauto with *.
    intros x1 y1 hyp_eq1 x2 y2 hyp_eq2.
    transitivity (x1 `elem` y2).
    - split; eapply elem_eqProp_elem...
    - split; eapply eqProp_elem_elem... 
  Qed.

  Global Hint Resolve elem_compatWith_eqProp : khan_hints.

  Local Add Parametric Morphism :
    (Acc elem) with signature (eqProp ==> iff)
    as Acc_elem_compatWith_eqProp.
  Proof with eauto with *.
    enough (to_show : forall lhs : AczelSet, forall rhs : AczelSet, lhs == rhs -> Acc elem lhs -> Acc elem rhs).
    { intros x y h_eq. split; eapply to_show... }
    intros lhs rhs x_eq_y acc_x. cbn. pose proof (Acc_inv acc_x) as claim1. econstructor...
    intros z z_in_y. eapply claim1. rewrite x_eq_y... 
  Qed.

  Lemma AczelSet_elem_well_founded
    : forall root : AczelSet, Acc elem root.
  Proof.
    induction root as [x_children x_childtree IH]. econstructor.
    intros z [c_x z_eq_x_c]. rewrite z_eq_x_c. exact (IH c_x).
  Qed.

  Global Instance AczelSet_isWellFounded : isWellFounded AczelSet :=
    { wfRel := elem
    ; wfRel_well_founded := AczelSet_elem_well_founded
    }
  .

  Theorem AczelSet_extensional_equality (lhs : AczelSet) (rhs : AczelSet)
    : lhs == rhs <-> << EXT_EQ : forall z : AczelSet, z `elem` lhs <-> z `elem` rhs >>.
  Proof with cbn; eauto with *.
    unnw. split.
    - intros h_eq z. rewrite h_eq. reflexivity.
    - revert rhs. induction lhs as [x_children x_childtree IH]; intros [y_children y_childtree].
      intros h_eq. simpl. split; unnw.
      + intros c_x.
        assert (claim1 : (x_childtree c_x) `elem` Node x_children x_childtree).
        { eapply elem_intro... }
        destruct (proj1 (h_eq (x_childtree c_x)) claim1) as [c_y x_c_eq_y]...
      + intros c_y.
        assert (claim1 : (y_childtree c_y) `elem` Node y_children y_childtree).
        { eapply elem_intro... }
        destruct (proj2 (h_eq (y_childtree c_y)) claim1) as [c_x y_c_eq_x]...
  Qed.

  Definition subseteq (x : AczelSet) (y : AczelSet) : Prop :=
    forall z : AczelSet, z `elem` x -> z `elem` y
  .

  Global Hint Unfold subseteq : khan_hints.

  Global Instance subseteq_PreOrder
    : PreOrder subseteq.
  Proof. split; eauto with *. Qed.

  Global Instance subseteq_PartialOrder
    : PartialOrder eqProp subseteq.
  Proof.
    intros lhs rhs. simpl. rewrite AczelSet_extensional_equality.
    unfold relation_conjunction, flip, subseteq. cbn; unnw. now firstorder.
  Qed.

  Global Add Parametric Morphism :
    subseteq with signature (eqProp ==> eqProp ==> iff)
    as subseteq_compatWith_eqProp.
  Proof with eauto with *.
    intros x1 x2 h_x_eq y1 y2 h_y_eq.
    transitivity (subseteq x1 y2); unfold subseteq; split; intros h_subset z h_in.
    - rewrite <- h_y_eq...
    - rewrite -> h_y_eq...
    - rewrite <- h_x_eq in h_in...
    - rewrite -> h_x_eq in h_in...
  Qed.

  Definition compatWith_eqTree (phi : AczelSet -> Prop) : Prop :=
    forall x : AczelSet, phi x ->
    forall y : AczelSet, x == y ->
    phi y
  .

  Definition eqTree_closure (phi : AczelSet -> Prop) (x : AczelSet) : Prop :=
    exists y : AczelSet, x == y /\ phi y
  .

  Lemma equality_closure_compatWith_eqTree (phi : AczelSet -> Prop)
    : compatWith_eqTree (eqTree_closure phi).
  Proof.
    unfold eqTree_closure, compatWith_eqTree. intros x [y [x_eq_y phi_y]] z x_eq_z.
    exists (y). split; [symmetry; etransitivity; now eauto | exact (phi_y)].
  Qed.

(** "Set Constructions" *)

  Definition fromWf {A : Type} {wfRel : A -> A -> Prop} : forall root : A, Acc wfRel root -> Tree :=
    fix fromWf_fix (tree : A) (tree_acc : Acc wfRel tree) {struct tree_acc} : Tree :=
    match tree_acc with
    | Acc_intro _ hyp_acc => Node {subtree : A | wfRel subtree tree} (fun childtree : {subtree : A | wfRel subtree tree} => fromWf_fix (proj1_sig childtree) (hyp_acc (proj1_sig childtree) (proj2_sig childtree)))
    end
  .

(** "Ordinals" *)

  Definition isTransitiveSet (x : AczelSet) : Prop :=
    forall y : AczelSet, y `elem` x ->
    forall z : AczelSet, z `elem` y ->
    z `elem` x
  .

  Variant isOrdinal (alpha : AczelSet) : Prop :=
  | transitive_set_of_transitive_sets_isOrdinal
    (alpha_isTransitiveSet : isTransitiveSet alpha)
    (every_member_of_alpha_isTransitiveSet : forall beta, beta `elem` alpha -> isTransitiveSet beta)
    : isOrdinal alpha
  .

  Lemma every_member_of_Ordinal_isOrdinal (alpha : AczelSet)
    (alpha_isOrdinal : isOrdinal alpha)
    : forall beta : AczelSet, beta `elem` alpha -> isOrdinal beta.
  Proof.
    inversion alpha_isOrdinal; subst.
    intros beta beta_in_alpha; econstructor; eauto.
  Qed.

End AczelSet.
