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

(** "Equality and Membership" *)

  Fixpoint equality (lhs : AczelSet) (rhs : AczelSet) : Prop :=
    match lhs in Tree, rhs in Tree return Prop with
    | Node children1 childtrees1, Node children2 childtrees2 => ⟪ lhs_subset_rhs : forall child1 : children1, exists child2 : children2, equality (childtrees1 child1) (childtrees2 child2) ⟫ /\ ⟪ rhs_subset_lhs : forall child2 : children2, exists child1 : children1, equality (childtrees1 child1) (childtrees2 child2) ⟫
    end
  .

  Global Instance equality_Equivalence
    : Equivalence equality.
  Proof with eauto.
    split.
    - intros x; induction x as [x_children x_childtree IH].
      cbn in *; split; unnw...
    - intros x; induction x as [x_children x_childtree IH]; intros [y_children y_childtree] [x_subset_y y_subset_x].
      cbn in *; split; unnw; [intros c_y | intros c_x].
      + exploit (y_subset_x c_y) as [c_x hyp_eq1]...
      + exploit (x_subset_y c_x) as [c_y hyp_eq1]...
    - intros x y; revert x; induction y as [y_children y_childtree IH]; intros [x_children x_childtree] [z_children z_childtree] [x_subset_y y_subset_x] [y_subset_z z_subset_y].
      cbn in *; split; unnw; [intros c_x | intros c_z].
      + exploit (x_subset_y c_x) as [c_y hyp_eq1]; exploit (y_subset_z c_y) as [c_z hyp_eq2]...
      + exploit (z_subset_y c_z) as [c_y hyp_eq1]; exploit (y_subset_x c_y) as [c_x hyp_eq2]...
  Qed.

  Global Instance AczelSet_isSetoid : isSetoid AczelSet :=
    { eqProp := equality
    ; eqProp_Equivalence := equality_Equivalence
    }
  .

  Lemma unfold_eqProp_inAczelSet (lhs : AczelSet) (rhs : AczelSet)
    : (lhs == rhs) = equality lhs rhs.
  Proof. reflexivity. Qed.

  Ltac fold_equality := rewrite <- unfold_eqProp_inAczelSet in *.

  Definition elem (finger : AczelSet) (hand : AczelSet) : Prop :=
    exists bone : getChildren hand, finger == getChildTrees hand bone
  .

  Local Infix " `elem` " := elem (at level 70, no associativity) : type_scope.

  Lemma unfold_elem (finger : AczelSet) (hand : AczelSet)
    : finger `elem` hand = (exists bone : getChildren hand, finger == getChildTrees hand bone).
  Proof. reflexivity. Qed.

  Lemma elem_intro {z : AczelSet} {x : AczelSet} (c_x : getChildren x)
    (z_eq_x_c : z == getChildTrees x c_x)
    : z `elem` x.
  Proof.
    exists c_x. exact (z_eq_x_c).
  Qed.

  Lemma eqProp_elem_elem (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (x_eq_y : x == y)
    (y_in_z : y `elem` z)
    : x `elem` z.
  Proof.
    destruct y_in_z as [c_z y_eq_z_c]. eexists.
    etransitivity; [exact (x_eq_y) | exact (y_eq_z_c)].
  Qed.

  Lemma elem_eqProp_elem (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (y_eq_z : y == z)
    (x_in_y : x `elem` y)
    : x `elem` z.
  Proof.
    destruct z as [z_children z_childtree]; destruct y as [y_children y_childtree].
    destruct y_eq_z as [y_subset_z_c z_c_subset_y]; destruct x_in_y as [c_y x_eq_y_c].
    destruct (y_subset_z_c c_y) as [c_z c_y_eq_c_z]. cbn in *.
    eexists. etransitivity; [exact (x_eq_y_c) | exact (c_y_eq_c_z)].
  Qed.

  Global Add Parametric Morphism :
    elem with signature (eqProp ==> eqProp ==> iff)
  as elem_compatWith_eqProp.
  Proof with eauto.
    intros x1 y1 hyp_eq1 x2 y2 hyp_eq2.
    transitivity (x1 `elem` y2); split.
    - eapply elem_eqProp_elem...
    - eapply elem_eqProp_elem. symmetry...
    - eapply eqProp_elem_elem. symmetry...
    - eapply eqProp_elem_elem...
  Qed.

  Local Add Parametric Morphism :
    (Acc elem) with signature (eqProp ==> iff)
  as Acc_elem_compatWith_eqProp.
  Proof.
    enough (to_show : forall lhs : AczelSet, forall rhs : AczelSet, lhs == rhs -> Acc elem lhs -> Acc elem rhs).
    { intros x y h_eq. split; eapply to_show; [exact (h_eq) | symmetry; exact (h_eq)]. }
    intros lhs rhs x_eq_y acc_x. cbn. pose proof (Acc_inv acc_x) as claim1. econstructor.
    intros z z_in_y. eapply claim1. rewrite x_eq_y. exact (z_in_y). 
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

  Theorem AczelSet_extensional_equality (lhs : AczelSet) (rhs : AczelSet) :
    lhs == rhs <->
    << EXT_EQ : forall z : AczelSet, z `elem` lhs <-> z `elem` rhs >>.
  Proof.
    unnw. split.
    - intros h_eq z. rewrite h_eq. reflexivity.
    - revert rhs. induction lhs as [x_children x_childtree IH]; intros [y_children y_childtree].
      intros h_eq. simpl. split; unnw.
      + intros c_x.
        assert (claim1 : (x_childtree c_x) `elem` Node x_children x_childtree).
        { eapply elem_intro. reflexivity. }
        destruct (proj1 (h_eq (x_childtree c_x)) claim1) as [c_y x_c_eq_y].
        exists (c_y). exact (x_c_eq_y).
      + intros c_y.
        assert (claim1 : (y_childtree c_y) `elem` Node y_children y_childtree).
        { eapply elem_intro. reflexivity. }
        destruct (proj2 (h_eq (y_childtree c_y)) claim1) as [c_x y_c_eq_x].
        exists (c_x). symmetry. exact (y_c_eq_x).
  Qed.

  Definition fromAcc {A : Type} {wfRel : A -> A -> Prop} : forall root : A, Acc wfRel root -> Tree :=
    fix fromAcc_fix (tree : A) (tree_acc : Acc wfRel tree) {struct tree_acc} : Tree :=
    match tree_acc with
    | Acc_intro _ hyp_acc => Node {subtree : A | wfRel subtree tree} (fun childtree : {subtree : A | wfRel subtree tree} => fromAcc_fix (proj1_sig childtree) (hyp_acc (proj1_sig childtree) (proj2_sig childtree)))
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
