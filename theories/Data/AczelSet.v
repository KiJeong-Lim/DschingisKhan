Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module AczelSetUniv.

  Universe AczelSetUniv_lv.

  Definition t : Type@{AczelSetUniv_lv + 1} := Type@{AczelSetUniv_lv}.

End AczelSetUniv.

Module AczelSet. (* THANKS TO "Hanul Jeon" *)

  Universe AczelSet_smallUniv_lv.

  Constraint AczelSet_smallUniv_lv < AczelSetUniv.AczelSetUniv_lv.

  Definition smallUniv : AczelSetUniv.t := Type@{AczelSet_smallUniv_lv}.

  Inductive Tree : AczelSetUniv.t :=
  | Node {children : smallUniv} (childtrees : forall c : children, Tree) : Tree
  .

  Definition AczelSet : AczelSetUniv.t := Tree.

  Definition getChildren (root : AczelSet) : smallUniv :=
    match root with
    | @Node children childtrees => children
    end
  .

  Definition getChildTrees (root : AczelSet) : getChildren root -> AczelSet :=
    match root with
    | @Node children childtrees => childtrees
    end
  .

  Lemma AczelSet_eta (x : AczelSet)
    : x = @Node (getChildren x) (fun child : getChildren x => getChildTrees x child).
  Proof. destruct x; reflexivity. Defined.

(** "Relations on Set" *)

  Fixpoint eqTree (lhs : AczelSet) (rhs : AczelSet) {struct lhs} : Prop :=
    match lhs in Tree, rhs in Tree return Prop with
    | Node childtrees1, Node childtrees2 => ⟪ lhs_simulates_rhs : forall child1, exists child2, eqTree (childtrees1 child1) (childtrees2 child2) ⟫ /\ ⟪ rhs_simulates_lhs : forall child2, exists child1, eqTree (childtrees1 child1) (childtrees2 child2) ⟫
    end
  .

  Global Instance eqTree_Reflexive
    : Reflexive eqTree.
  Proof.
    change (forall x : AczelSet, eqTree x x).
    induction x as [x_children x_childtrees IH]. simpl; unnw. split.
    - intros c_x. exists (c_x). eapply IH.
    - intros c_x. exists (c_x). eapply IH.
  Defined.

  Global Instance eqTree_Symmetric
    : Symmetric eqTree.
  Proof.
    change (forall x : AczelSet, forall y : AczelSet, eqTree x y -> eqTree y x).
    induction x as [x_children x_childtrees IH], y as [y_children y_childtrees]. simpl; unnw. intros [x_sim_y y_sim_x]. split.
    - intros c_y. pose proof (y_sim_x c_y) as [c_x x_c_eq_y_c]. exists (c_x). eapply IH; exact (x_c_eq_y_c).
    - intros c_x. pose proof (x_sim_y c_x) as [c_y y_c_eq_x_c]. exists (c_y). eapply IH; exact (y_c_eq_x_c).
  Defined.

  Global Instance eqTree_Transitive
    : Transitive eqTree.
  Proof.
    change (forall x : AczelSet, forall y : AczelSet, forall z : AczelSet, eqTree x y -> eqTree y z -> eqTree x z).
    induction x as [x_children x_childtrees IH], y as [y_children y_childtrees], z as [z_children z_childtrees]. simpl; unnw. intros [x_sim_y y_sim_x] [y_sim_z z_sim_y]. split.
    - intros c_x. pose proof (x_sim_y c_x) as [c_y y_c_eq_x_c]. pose proof (y_sim_z c_y) as [c_z y_c_eq_z_c]. exists (c_z). eapply IH; [exact (y_c_eq_x_c) | exact (y_c_eq_z_c)].
    - intros c_z. pose proof (z_sim_y c_z) as [c_y y_c_eq_z_c]. pose proof (y_sim_x c_y) as [c_x x_c_eq_y_c]. exists (c_x). eapply IH; [exact (x_c_eq_y_c) | exact (y_c_eq_z_c)].
  Defined.

  Global Instance eqTree_Equivalence : Equivalence eqTree :=
    { Equivalence_Reflexive := eqTree_Reflexive
    ; Equivalence_Symmetric := eqTree_Symmetric
    ; Equivalence_Transitive := eqTree_Transitive
    }
  .

  Global Instance AczelSet_isSetoid : isSetoid AczelSet :=
    { eqProp := eqTree
    ; eqProp_Equivalence := eqTree_Equivalence
    }
  .

  Lemma eqTree_unfold
    : eqTree = (fun lhs : AczelSet => fun rhs : AczelSet => lhs == rhs).
  Proof. reflexivity. Defined.

  Local Hint Resolve eqTree_Reflexive eqTree_Symmetric eqTree_Transitive : core.

  Ltac unfold_eqTree := rewrite eqTree_unfold in *.

  Definition elem (finger : AczelSet) (hand : AczelSet) : Prop :=
    exists bone : getChildren hand, finger == getChildTrees hand bone
  .

  Lemma elem_well_founded
    : forall root : AczelSet, Acc (fun subtree : AczelSet => fun tree : AczelSet => exists key : getChildren tree, eqTree subtree (getChildTrees tree key)) root.
  Proof.
    enough (Acc_compatWith_eqTree : forall lhs : AczelSet, forall rhs : AczelSet, eqTree lhs rhs -> Acc elem lhs -> Acc elem rhs).
    - induction root as [x_children x_childtrees IH]. econstructor. intros y [c_x y_eq_x_c]. eapply Acc_compatWith_eqTree; [eapply eqTree_Symmetric; exact (y_eq_x_c)| exact (IH c_x)].
    - intros lhs rhs lhs_eq_rhs Acc_lhs. pose proof (@Acc_inv AczelSet elem lhs Acc_lhs) as claim1.
      econstructor. intros z z_in_rhs. eapply claim1. revert z_in_rhs. unfold elem. clear Acc_lhs claim1.
      destruct lhs as [x_children x_childtrees]; destruct rhs as [y_children y_childtrees]; destruct lhs_eq_rhs as [x_sim_y y_sim_x].
      unnw; cbn. intros [c_y z_eq_y_c]. pose proof (y_sim_x c_y) as [c_x x_c_eq_y_c]. exists (c_x). eapply eqTree_Transitive; [exact (z_eq_y_c) | eapply eqTree_Symmetric; exact (x_c_eq_y_c)].
  Defined.

  Local Hint Unfold elem : khan_hints.

  Global Instance AczelSet_isWellFounded : isWellFounded AczelSet :=
    { wfRel := elem
    ; wfRel_well_founded := elem_well_founded
    }
  .

  Global Infix " `elem` " := elem (at level 70, no associativity) : type_scope.

  Lemma AczelSet_rect (phi : AczelSet -> Type)
    (IND : forall x : AczelSet, ⟪ IH : forall y : AczelSet, y `elem` x -> phi y ⟫ -> phi x)
    : forall x : AczelSet, phi x.
  Proof. eapply NotherianRecursion. exact (IND). Defined.

  Lemma elem_intro (x : AczelSet) (c_x : getChildren x)
    : getChildTrees x c_x `elem` x.
  Proof. exists (c_x). exact (eqTree_Reflexive (getChildTrees x c_x)). Defined.

  Lemma eqProp_elem_elem (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (x_eq_y : x == y)
    (y_in_z : y `elem` z)
    : x `elem` z.
  Proof. destruct y_in_z as [c_z y_eq_z_c]. eexists; etransitivity; eauto with *. Qed.

  Lemma elem_eqProp_elem (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (x_in_y : x `elem` y)
    (y_eq_z : y == z)
    : x `elem` z.
  Proof.
    destruct z as [z_children z_childtrees]; destruct y as [y_children y_childtrees].
    destruct y_eq_z as [y_subset_z_c z_c_subset_y]; destruct x_in_y as [c_y x_eq_y_c].
    pose proof (y_subset_z_c c_y) as [c_z c_y_eq_c_z]. eexists; etransitivity; eauto with *.
  Qed.

  Global Add Parametric Morphism :
    elem with signature (eqProp ==> eqProp ==> iff)
    as elem_compatWith_eqProp.
  Proof with eauto with *.
    pose proof (elem_eqProp_elem) as claim1.
    pose proof (eqProp_elem_elem) as claim2.
    intros x1 y1 hyp_eq1 x2 y2 hyp_eq2.
    simpl in *; split; ii; eauto with *.
  Qed.

  Local Hint Resolve elem_compatWith_eqProp : khan_hints.

  Theorem AczelSet_extensional_equality (lhs : AczelSet) (rhs : AczelSet)
    : lhs == rhs <-> << EXTENSIONAL_EQUALITY : forall z : AczelSet, z `elem` lhs <-> z `elem` rhs >>.
  Proof with cbn; eauto with *.
    unnw. split.
    - intros h_eq z. rewrite h_eq. reflexivity.
    - revert rhs. induction lhs as [x_children x_childtrees IH]; intros [y_children y_childtrees].
      intros h_eq. simpl; unnw. split; [intros c_x | intros c_y].
      + assert (claim1 : x_childtrees c_x `elem` Node x_childtrees) by eapply elem_intro.
        pose proof (proj1 (h_eq (x_childtrees c_x)) claim1) as [c_y x_c_eq_y]...
      + assert (claim1 : y_childtrees c_y `elem` Node y_childtrees) by eapply elem_intro.
        pose proof (proj2 (h_eq (y_childtrees c_y)) claim1) as [c_x y_c_eq_x]...
  Qed.

  Definition subseteq (x : AczelSet) (y : AczelSet) : Prop :=
    forall z : AczelSet, z `elem` x -> z `elem` y
  .

  Global Infix " `subseteq` " := subseteq (at level 70, no associativity) : type_scope.

  Local Hint Unfold subseteq : khan_hints.

  Global Instance subseteq_PreOrder
    : PreOrder subseteq.
  Proof. split; eauto with *. Qed.

  Global Instance subseteq_PartialOrder
    : PartialOrder eqProp subseteq.
  Proof. intros lhs rhs. simpl. rewrite AczelSet_extensional_equality. now firstorder. Qed.

  Lemma eqTree_intro (lhs : AczelSet) (rhs : AczelSet)
    (lhs_subseteq_rhs : lhs `subseteq` rhs)
    (rhs_subseteq_lhs : rhs `subseteq` lhs)
    : lhs == rhs.
  Proof. eapply subseteq_PartialOrder; split; eauto with *. Qed.

  Global Add Parametric Morphism :
    subseteq with signature (eqProp ==> eqProp ==> iff)
    as subseteq_compatWith_eqProp.
  Proof with eauto with *.
    intros x1 x2 x1_eq_x2 y1 y2 y1_eq_y2.
    transitivity (subseteq x1 y2); unfold subseteq; split; intros h_subset z h_in.
    - rewrite <- y1_eq_y2...
    - rewrite -> y1_eq_y2...
    - rewrite <- x1_eq_x2 in h_in...
    - rewrite -> x1_eq_x2 in h_in...
  Qed.

  Local Hint Resolve subseteq_compatWith_eqProp : khan_hints.

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

  Definition elemLt {alpha : AczelSet} (lhs : getChildren alpha) (rhs : getChildren alpha) : Prop :=
    getChildTrees alpha lhs `elem` getChildTrees alpha rhs
  .

  Global Instance elemLt_isWellFounded (alpha : AczelSet) : isWellFounded (getChildren alpha) :=
    { wfRel := elemLt (alpha := alpha)
    ; wfRel_well_founded := well_founded_relation_on_image (getChildTrees alpha) elem elem_well_founded
    }
  .

(** "Set Constructions" *)

  Section AczelSet_filtering.

  Definition filtering (x : AczelSet) (phi : getChildren x -> Prop) : AczelSet := Node (fun child : @sig (getChildren x) phi => getChildTrees x (proj1_sig child)).

  Theorem AczelSet_filtering_spec (x : AczelSet) (phi : getChildren x -> Prop)
    : forall z : AczelSet, z `elem` filtering x phi <-> << IN_filtering : exists c_x : getChildren x, z == getChildTrees x c_x /\ phi c_x >>.
  Proof with eauto with *.
    intros z. unnw; split.
    - intros [[c_x phi_c_x] z_eq_x_c]. simpl in *...
    - intros [c_x [z_eq_x_c phi_c_x]]. exists (@exist _ _ c_x phi_c_x)...
  Qed.

  Corollary subset_filtering (x : AczelSet)
    : forall z : AczelSet, z `subseteq` x <-> << IS_A_SUBSET : exists phi : getChildren x -> Prop, z == filtering x phi >>.
  Proof with eauto with *.
    intros z. unnw. split.
    - intros z_subset_x. exists (fun c_x : getChildren x => getChildTrees x c_x `elem` z). eapply eqTree_intro.
      + intros y y_in_z. pose proof (z_subset_x y y_in_z) as [c_x y_eq_x_c].
        rewrite y_eq_x_c. rewrite y_eq_x_c in y_in_z. exists (@exist _ _ c_x y_in_z)...
      + intros y [[c_x x_c_in_z] y_eq_x_c]. rewrite y_eq_x_c...
    - intros [phi z_eq]. rewrite z_eq. intros y. rewrite AczelSet_filtering_spec. unnw.
      intros [c_x [z_eq_x_c phi_c_x]]...
  Qed.

  End AczelSet_filtering.

  Section AczelSet_filter.

  Definition filter (phi : AczelSet -> Prop) (x : AczelSet) : AczelSet := filtering x (fun c_x : getChildren x => phi (getChildTrees x c_x)).

  Theorem AczelSet_filter_spec (phi : AczelSet -> Prop) (x : AczelSet)
    : forall z : AczelSet, z `elem` filter phi x <-> << IN_filter : exists c_x : getChildren x, phi (getChildTrees x c_x) /\ z == getChildTrees x c_x >>.
  Proof with eauto with *.
    intros z. unfold filter. rewrite AczelSet_filtering_spec. unnw; split.
    - intros [c_x [z_eq_x_c phi_z]]...
    - intros [c_x [phi_x_c z_eq]]...
  Qed.

  Corollary in_filter_iff (phi : AczelSet -> Prop) (x : AczelSet)
    (phi_compatWith_eqTree : compatWith_eqTree phi)
    : forall z : AczelSet, z `elem` filter phi x <-> << FILTER : z `elem` x /\ phi z >>.
  Proof with cbn in *; eauto with *.
    intros z. unfold filter. rewrite AczelSet_filtering_spec. unnw; split.
    - intros [c_x [z_eq_x_c phi_z]]...
    - intros [[c_x z_eq_x_c] phi_z]...
  Qed.

  End AczelSet_filter.

  Section AczelSet_power.

  Definition power (x : AczelSet) : AczelSet := Node (fun child : getChildren x -> Prop => filtering x child).

  Theorem AczelSet_power_spec (x : AczelSet)
    : forall z : AczelSet, z `elem` power x <-> << IN_power : z `subseteq` x >>.
  Proof. intros z. unnw. rewrite subset_filtering. unfold power. eauto with *. Qed.

  End AczelSet_power.

  Section AczelSet_fromList.

  Definition fromList (xs : list AczelSet) : AczelSet := Node (fun child : Fin (length xs) => safe_nth xs child).

  Theorem AczelSet_fromList_spec (xs : list AczelSet)
    : forall z : AczelSet, z `elem` fromList xs <-> << IN_fromList : exists i : Fin (length xs), z == safe_nth xs i >>.
  Proof with eauto with *.
    unnw; intros z; split.
    - intros [c_x z_eq_x_c]...
    - intros [i z_eq_xs_at_i]...
  Qed.

  End AczelSet_fromList.

  Section AczelSet_unions_i.

  Definition unions_i {I : smallUniv} (xs : I -> AczelSet) : AczelSet := Node (fun child : {i : I & getChildren (xs i)} => getChildTrees (xs (projT1 child)) (projT2 child)).

  Theorem AczelSet_unions_i_spec {I : smallUniv} (xs : I -> AczelSet)
    : forall z : AczelSet, z `elem` unions_i xs <-> << IN_unions_i : exists i : I, z `elem` xs i >>.
  Proof with eauto with *.
    intros z. unnw; split.
    - intros [[i c_u] z_eq_u_c]. simpl in *...
    - intros [i [c_u z_eq_u_c]]. exists (@existT _ _ i c_u)...
  Qed.

  End AczelSet_unions_i.

  Section AczelSet_unions.

  Definition unions (x : AczelSet) : AczelSet := unions_i (I := getChildren x) (getChildTrees x).

  Theorem AczelSet_unions_spec (x : AczelSet)
    : forall z : AczelSet, z `elem` unions x <-> << IN_unions : exists y : AczelSet, z `elem` y /\ y `elem` x >>.
  Proof with eauto with *.
    intros z. unfold unions. rewrite AczelSet_unions_i_spec. unnw; split.
    - intros [i [c_x z_eq_x_c]]. exists (getChildTrees x i). split...
    - intros [y [z_in_y [c_x y_eq_x_c]]]. exists (c_x). rewrite <- y_eq_x_c...
  Qed.

  End AczelSet_unions.

  Section AczelSet_empty.

  Definition empty : AczelSet := Node (fun hyp_false : False => @False_rect AczelSet hyp_false).

  Lemma AczelSet_empty_spec
    : forall z : AczelSet, z `elem` empty <-> << IN_empty : False >>.
  Proof. unnw. intros z. unfold empty. split; [intros [c z_eq_c] | tauto]; eauto with *. Qed.

  End AczelSet_empty.

  Section AczelSet_union.

  Definition union (x1 : AczelSet) (x2 : AczelSet) : AczelSet := unions_i (fun b : bool => if b then x1 else x2).

  Lemma AczelSet_union_spec (x1 : AczelSet) (x2 : AczelSet)
    : forall z : AczelSet, z `elem` union x1 x2 <-> << IN_union : z `elem` x1 \/ z `elem` x2 >>.
  Proof.
    unnw. intros z. unfold union. rewrite AczelSet_unions_i_spec. unnw.
    split; [intros [[ | ] z_in] | intros [z_in | z_in]; [exists (true) | exists (false)]]; eauto with *.
  Qed.

  End AczelSet_union.

  Section AczelSet_singleton.

  Definition singleton (x : AczelSet) : AczelSet := fromList (cons x nil).

  Lemma AczelSet_singleton_spec (x : AczelSet)
    : forall z : AczelSet, z `elem` singleton x <-> << IN_singleton : z == x >>.
  Proof.
    unnw. intros z. unfold singleton. rewrite AczelSet_fromList_spec. unnw; cbn; unfold_eqTree; split.
    - intros [i z_eq]. revert i z_eq. now introFinS i.
    - intros z_eq_x. now exists (FZ).
  Qed.

  End AczelSet_singleton.

  Section AczelSet_Nat.

  Definition sucOf (x : AczelSet) : AczelSet := union x (singleton x).

  Fixpoint natToAczelSet (n : nat) {struct n} : AczelSet :=
    match n with
    | O => empty
    | S n' => sucOf (natToAczelSet n')
    end
  .

  Definition Nat : AczelSet := unions_i (I := nat) natToAczelSet.

  End AczelSet_Nat.

  Section AczelSet_intersection.

  Definition intersections_i {I : smallUniv} {default_of_I : I} (x_i : I -> AczelSet) : AczelSet :=
    filter (fun z : AczelSet => forall i : I, z `elem` x_i i) (x_i default_of_I)
  .

  Lemma AczelSet_intersections_i_spec {I : smallUniv} (default_of_I : I) (x_i : I -> AczelSet)
    : forall z : AczelSet, z `elem` intersections_i (default_of_I := default_of_I) x_i <-> << IN_intersections_i : forall i : I, z `elem` x_i i >>.
  Proof with eauto with *.
    unfold intersections_i. intros z. rewrite AczelSet_filter_spec. unnw. split.
    - intros [c_x [hyp_in z_eq]] i. rewrite z_eq...
    - intros z_in. exploit (z_in default_of_I) as [c z_eq]. exists (c). split...
      intros i. rewrite <- z_eq...
  Qed.

  Definition intersection (x1 : AczelSet) (x2 : AczelSet) : AczelSet :=
    intersections_i (I := bool) (default_of_I := true) (fun b : bool => if b then x1 else x2)
  .

  Lemma AczelSet_intersection_spec (x1 : AczelSet) (x2 : AczelSet)
    : forall z : AczelSet, z `elem` intersection x1 x2 <-> << IN_intersection : z `elem` x1 /\ z `elem` x2 >>.
  Proof.
    intros z. unfold intersection. rewrite AczelSet_intersections_i_spec. split; intros z_in.
    - split; [exact (z_in true) | exact (z_in false)].
    - unnw. intros [ | ]; tauto.
  Qed.

  End AczelSet_intersection.

  Section AczelSet_fromWf.

  Definition fromAcc {A : smallUniv} {wfRel : A -> A -> Prop} : forall root : A, Acc wfRel root -> AczelSet :=
    fix fromAcc_fix (tree : A) (tree_acc : Acc wfRel tree) {struct tree_acc} : AczelSet :=
    match tree_acc with
    | Acc_intro _ hyp_acc => Node (fun child : {subtree : A | wfRel subtree tree} => fromAcc_fix (proj1_sig child) (hyp_acc (proj1_sig child) (proj2_sig child)))
    end
  .

  Lemma fromAcc_unfold {A : smallUniv} {wfRel : A -> A -> Prop} (tree : A) (tree_acc : Acc wfRel tree)
    : forall z : AczelSet, z `elem` fromAcc tree tree_acc <-> << EXPANDED : exists child : {subtree : A | wfRel subtree tree}, z == fromAcc (proj1_sig child) (Acc_inv tree_acc (proj2_sig child)) >>.
  Proof.
    intros z. destruct tree_acc as [hyp_acc]. unnw; split.
    all: intros [[c hyp_wf] z_eq_c]; cbn in *; unfold_eqTree; now exists (@exist _ _ c hyp_wf).
  Qed.

  Lemma fromAcc_proof_irrelevance {A : smallUniv} {wfRel : A -> A -> Prop} (root : A) (root_acc1 : Acc wfRel root) (root_acc2 : Acc wfRel root)
    : fromAcc root root_acc1 == fromAcc root root_acc2.
  Proof with eauto with *.
    revert root root_acc1 root_acc2.
    enough (it_suffices_to_show : forall tree : A, Acc wfRel tree -> forall tree_acc1 : Acc wfRel tree, forall tree_acc2 : Acc wfRel tree, fromAcc tree tree_acc1 `subseteq` fromAcc tree tree_acc2).
    { ii. eapply subseteq_PartialOrder. split; eapply it_suffices_to_show... }
    intros tree tree_acc. induction tree_acc as [tree tree_acc_inv IH]. intros [tree_acc1_inv] [tree_acc2_inv].
    intros z [[subtree subtree_R_tree] z_eq]. simpl in *; unfold_eqTree. exists (@exist _ _ subtree subtree_R_tree).
    simpl; unfold_eqTree. rewrite z_eq. eapply subseteq_PartialOrder; split...
  Qed.

  Corollary fromAcc_elem_fromAcc_intro {A : smallUniv} {wfRel : A -> A -> Prop} (subtree : A) (subtree_acc : Acc wfRel subtree) (tree : A) (tree_acc : Acc wfRel tree)
    (subtree_R_tree : wfRel subtree tree)
    : fromAcc subtree subtree_acc `elem` fromAcc tree tree_acc.
  Proof. eapply fromAcc_unfold. exists (@exist _ _ subtree subtree_R_tree). simpl; unfold_eqTree. eapply fromAcc_proof_irrelevance. Qed.

  Lemma fromAcc_subseteq_iff {A : smallUniv} {wfRel : A -> A -> Prop} (tree : A) (tree_acc : Acc wfRel tree)
    : forall x : AczelSet, fromAcc tree tree_acc `subseteq` x <-> << LT_ELEM : forall subtree : A, forall subtree_R_tree : wfRel subtree tree, fromAcc subtree (Acc_inv tree_acc subtree_R_tree) `elem` x >>.
  Proof with eauto with *.
    intros x. split.
    - intros subseteq_x subtree subtree_R_tree. eapply subseteq_x, fromAcc_elem_fromAcc_intro...
    - destruct tree_acc as [tree_acc_inv]. intros LT_ELEM z z_in; unnw.
      apply fromAcc_unfold in z_in. unnw. destruct z_in as [[subtree subtree_R_tree] z_eq].
      simpl in *; unfold_eqTree. rewrite z_eq...
  Qed.

  Definition fromWf (A : smallUniv) {requiresWellFounded : isWellFounded A} : AczelSet := unions_i (fun root : A => fromAcc root (wfRel_well_founded root)).

  End AczelSet_fromWf.

  Section AczelSet_StrongCollection.

  (* << A Sketch of the Proof of Strong Collection >>
    -- Advice of "Hanul Jeon"
    > Aczel의 Strong Collection의 증명을 스케치해보면,
      Let's sketch the Aczel's proof of Strong Collection.
    > 우선 forall x:X, exists y, phi(x,y)가 성립한다고 합시다.
      First, assume $forall x \in X, exists y, phi(x, y)$.
    > 여기서 AC를 적용해서 forall x:X, phi(x,f(x))인 f를 찾고,
      By applying AC, find $f$ for which $forall x \in X, phi(x, f(x))$.
    > base set을 X의 base와 똑같이 잡을 겁니다.
      Now, take the base set as that of $X$.
    > 그리고 원소는 f(x)에 대응하게끔 잡을 거고요.
      And set the elements corresponding to $f(x)$.
    > 문제는 AC가 Coq에서 작동할 것 같지 않다는 거네요.
      Although, the problem is that AC may not work on Coq.
  *)

  Hypothesis AC : forall A : AczelSetUniv.t, forall B : AczelSetUniv.t, forall phi : A -> B -> Prop, << NONEMPTY : forall x : A, exists y : B, phi x y >> -> << CHOICE : exists f : A -> B, forall x : A, phi x (f x) >>.

  Theorem AxiomOfChoice_implies_StrongCollection (phi : AczelSet -> AczelSet -> Prop) (X : AczelSet)
    (phi_compatWith_eqTree_on_1st_arg : forall y : AczelSet, compatWith_eqTree (fun x : AczelSet => phi x y))
    (phi_compatWith_eqTree_on_2nd_arg : forall x : AczelSet, compatWith_eqTree (fun y : AczelSet => phi x y))
    (NONEMPTY : forall x : AczelSet, x `elem` X -> exists y : AczelSet, phi x y)
    : exists Y : AczelSet, ⟪ collects_for_1st_arg : forall x : AczelSet, x `elem` X -> exists y : AczelSet, y `elem` Y /\ phi x y ⟫ /\ ⟪ collects_for_2nd_arg : forall y : AczelSet, elem y Y -> exists x : AczelSet, elem x X /\ phi x y ⟫.
  Proof with eauto with *.
    set (base_set := getChildren X). unnw.
    assert (claim1 : exists f : base_set -> AczelSet, forall x : base_set, phi (getChildTrees X x) (f x)).
    { eapply AC with (phi := fun x : base_set => fun y : AczelSet => phi (getChildTrees X x) y)... }
    destruct claim1 as [f claim1]. exists (@Node base_set (fun x : base_set => f x)). split.
    - intros x [c_X x_eq_X_c]. exists (f c_X). split... eapply phi_compatWith_eqTree_on_1st_arg...
    - intros x [c_X x_eq_X_c]. exists (getChildTrees X c_X). split... eapply phi_compatWith_eqTree_on_2nd_arg...
  Qed.

  End AczelSet_StrongCollection.

(** "Ordinals" *)

  Definition isTransitiveSet (x : AczelSet) : Prop :=
    forall y : AczelSet, << y_in : y `elem` x >> ->
    forall z : AczelSet, << z_in : z `elem` y >> ->
    z `elem` x
  .

  Local Hint Unfold isTransitiveSet : core.

  Lemma isTransitiveSet_compatWith_eqTree
    : compatWith_eqTree isTransitiveSet.
  Proof.
    intros alpha alpha_isTranstiveSet beta alpha_eq_beta.
    unfold isTransitiveSet in *; ii; desnw.
    rewrite <- alpha_eq_beta in *; eauto.
  Qed.

  Variant isOrdinal (alpha : AczelSet) : Prop :=
  | transitive_set_of_transitive_sets_isOrdinal
    (IS_TRANSITIVE_SET : isTransitiveSet alpha)
    (EVERY_ELEMENT_IS_TRANSITIVE_SET : forall beta, << IS_ELEMENT : beta `elem` alpha >> -> isTransitiveSet beta)
    : isOrdinal alpha
  .

  Local Hint Constructors isOrdinal : khan_hints.

  Lemma every_member_of_Ordinal_isOrdinal (alpha : AczelSet)
    (alpha_isOrdinal : isOrdinal alpha)
    : forall beta : AczelSet, beta `elem` alpha -> isOrdinal beta.
  Proof.
    intros beta beta_in_alpha. econstructor; destruct alpha_isOrdinal as [? ?].
    - eapply EVERY_ELEMENT_IS_TRANSITIVE_SET. exact (beta_in_alpha).
    - intros gamma gamma_in_beta; unnw. ii; desnw.
      eapply EVERY_ELEMENT_IS_TRANSITIVE_SET.
      + eapply IS_TRANSITIVE_SET; [exact (beta_in_alpha) | exact (gamma_in_beta)].
      + exact (y_in).
      + exact (z_in).
  Defined.

  Lemma isOrdinal_compatWith_eqTree
    : compatWith_eqTree isOrdinal.
  Proof with eauto with *.
    intros alpha [? ?] beta alpha_eq_beta. split.
    - eapply isTransitiveSet_compatWith_eqTree...
    - intros gamma gamm_in_beta; unnw.
      rewrite <- alpha_eq_beta in gamm_in_beta.
      eapply EVERY_ELEMENT_IS_TRANSITIVE_SET...
  Qed.

  Lemma elem_implies_subseteq_forOrdinal (alpha : AczelSet) (beta : AczelSet)
    (alpha_isOrdinal : isOrdinal alpha)
    (beta_in_alpha : beta `elem` alpha)
    : beta `subseteq` alpha.
  Proof. inversion alpha_isOrdinal. exact (IS_TRANSITIVE_SET beta beta_in_alpha). Qed.

  Local Hint Resolve elem_intro every_member_of_Ordinal_isOrdinal elem_implies_subseteq_forOrdinal : core.

  Global Instance elemLt_StrictOrder {alpha : AczelSet}
    (alpha_isOrdinal : isOrdinal alpha)
    : StrictOrder (@elemLt alpha).
  Proof.
    pose proof (@elem_intro) as claim1. split.
    - exact (wfRel_Irreflexive (requiresWellFounded := elemLt_isWellFounded alpha)).
    - intros x y z x_lt_y y_lt_z. unfold elemLt in *.
      destruct alpha_isOrdinal as [? ?].
      eapply EVERY_ELEMENT_IS_TRANSITIVE_SET; unnw; eauto.
  Qed.

  Section EXAMPLES_OF_ORDINAL.

  Lemma empty_isOrdinal
    : isOrdinal empty.
  Proof.
    econstructor; ii; desnw.
    - apply AczelSet_empty_spec in y_in. unnw. tauto.
    - apply AczelSet_empty_spec in IS_ELEMENT. unnw. tauto.
  Qed.

  Lemma sucOf_isOrdinal (alpha : AczelSet)
    (alpha_isOrdinal : isOrdinal alpha)
    : isOrdinal (sucOf alpha).
  Proof with eauto with *.
    unfold sucOf. econstructor; ii; desnw.
    - apply AczelSet_union_spec in y_in.
      destruct y_in as [y_in_alpha | y_eq_alpha].
      + eapply AczelSet_union_spec; left.
        inversion alpha_isOrdinal...
      + apply AczelSet_singleton_spec in y_eq_alpha. unnw.
        eapply AczelSet_union_spec; left. rewrite <- y_eq_alpha...
    - apply AczelSet_union_spec in IS_ELEMENT.
      destruct IS_ELEMENT as [beta_in_alpha | beta_eq_alpha].
      + exploit (every_member_of_Ordinal_isOrdinal alpha alpha_isOrdinal) as [? ?]...
      + apply AczelSet_singleton_spec in beta_eq_alpha. unnw.
        exploit (isOrdinal_compatWith_eqTree alpha alpha_isOrdinal beta) as [? ?]...
  Qed.

  Lemma unions_i_isOrdinal {I : smallUniv} (alpha_i : I -> AczelSet)
    (alpha_i_isOrdinal : forall i : I, isOrdinal (alpha_i i))
    : isOrdinal (unions_i alpha_i).
  Proof with eauto with *.
    econstructor.
    - ii; desnw. apply AczelSet_unions_i_spec in y_in. desnw.
      eapply AczelSet_unions_i_spec. exists (i).
      exploit (alpha_i_isOrdinal i) as [? ?]...
    - ii; desnw. apply AczelSet_unions_i_spec in IS_ELEMENT. desnw.
      exploit (alpha_i_isOrdinal i) as [? ?]. eapply EVERY_ELEMENT_IS_TRANSITIVE_SET...
  Qed.

  Lemma intersections_i_isOrdinal {I : smallUniv} {default_of_I : I} (alpha_i : I -> AczelSet)
    (alpha_i_isOrdinal : forall i : I, isOrdinal (alpha_i i))
    : isOrdinal (intersections_i (default_of_I := default_of_I) alpha_i).
  Proof with eauto with *.
    split; ii; desnw.
    - eapply AczelSet_intersections_i_spec. ii.
      exploit (alpha_i_isOrdinal i) as [? ?].
      apply AczelSet_intersections_i_spec in y_in.
      exploit (y_in i) as y_in_alpha_i_i...
    - eapply AczelSet_intersections_i_spec in IS_ELEMENT.
      exploit (IS_ELEMENT default_of_I) as beta_in_alpha_i_i.
      exploit (alpha_i_isOrdinal default_of_I) as [? ?].
      eapply EVERY_ELEMENT_IS_TRANSITIVE_SET with (beta := beta)...
  Qed.

  End EXAMPLES_OF_ORDINAL.

  Fixpoint lePropOnRank (lhs : AczelSet) (rhs : AczelSet) {struct lhs} : Prop :=
    match lhs, rhs with
    | Node lhs_elems, Node rhs_elems => forall lhs_child, exists rhs_child, lePropOnRank (lhs_elems lhs_child) (rhs_elems rhs_child)
    end
  .

  Definition eqPropOnRank (lhs : AczelSet) (rhs : AczelSet) : Prop :=
    lePropOnRank lhs rhs /\ lePropOnRank rhs lhs
  .

  Variant ltPropOnRank (lhs : AczelSet) (rhs : AczelSet) : Prop :=
  | lhs_rLt_rhs_if (rhs_child : getChildren rhs)
    (RANK_LE : lePropOnRank lhs (getChildTrees rhs rhs_child))
    : ltPropOnRank lhs rhs
  .

  Global Arguments lhs_rLt_rhs_if {lhs} {rhs}.

  Global Infix " `rEq` " := eqPropOnRank (at level 70, no associativity) : type_scope.
  Global Infix " `rLe` " := lePropOnRank (at level 70, no associativity) : type_scope.
  Global Infix " `rLt` " := ltPropOnRank (at level 70, no associativity) : type_scope.

  Section RANK_OF_ACZEL_SET.

  Local Instance rLe_Reflexive
    : Reflexive lePropOnRank.
  Proof.
    intros x. induction x as [x_children x_childtrees IH]. simpl. eauto with *.
  Qed.

  Local Instance rLe_Transitive
    : Transitive lePropOnRank.
  Proof.
    intros x y z x_le_y y_le_z. revert x x_le_y z y_le_z. induction y as [y_children y_childtrees IH].
    intros [x_children x_childtrees] x_le_y [z_children z_childtrees] y_le_z. simpl in *.
    intros c_x; pose proof (x_le_y c_x) as [c_y ?]; pose proof (y_le_z c_y) as [c_z ?]; eauto with *.
  Qed.

  Global Instance rLe_PreOrder : PreOrder lePropOnRank :=
    { PreOrder_Reflexive := rLe_Reflexive
    ; PreOrder_Transitive := rLe_Transitive
    }
  .

  Global Instance rEq_Equivalence
    : Equivalence eqPropOnRank.
  Proof with eauto with *. unfold eqPropOnRank. split; ii; des... all: etransitivity... Qed.

  Global Instance rLe_PartialOrder
    : PartialOrder eqPropOnRank lePropOnRank.
  Proof. ii; red; reflexivity. Qed.

  Lemma rLe_eqTree_rLe (x : AczelSet) (lhs : AczelSet) (rhs : AczelSet)
    (x_le_lhs : x `rLe` lhs)
    (lhs_eq_rhs : lhs == rhs)
    : x `rLe` rhs.
  Proof.
    revert lhs rhs x_le_lhs lhs_eq_rhs. induction x as [x_children x_childtrees IH].
    intros [y_children y_childtrees] [z_children z_childtrees]. intros x_le_y y_eq_z c_x.
    simpl in *; unnw. unfold_eqTree. destruct y_eq_z as [y_sim_z z_sim_y].
    pose proof (x_le_y c_x) as [c_y x_c_le_y_c]. pose proof (y_sim_z c_y) as [c_z y_c_eq_z_c]. eauto with *.
  Qed.

  Lemma eqTree_rLe_rLe (lhs : AczelSet) (rhs : AczelSet) (x : AczelSet)
    (lhs_eq_rhs : lhs == rhs)
    (rhs_le_x : rhs `rLe` x)
    : lhs `rLe` x.
  Proof.
    revert lhs rhs lhs_eq_rhs rhs_le_x. induction x as [x_children x_childtrees IH].
    intros [y_children y_childtrees] [z_children z_childtrees]. intros y_eq_z z_le_x c_y.
    simpl in *; unnw. destruct y_eq_z as [y_sim_z z_sim_y]. unfold_eqTree.
    pose proof (y_sim_z c_y) as [c_z y_c_eq_z_c]. pose proof (z_le_x c_z) as [c_x z_c_le_x_c]. eauto with *.
  Qed.

  Local Hint Resolve rLe_eqTree_rLe eqTree_rLe_rLe : core.

  Global Add Parametric Morphism :
    lePropOnRank with signature (eqProp ==> eqProp ==> iff)
    as rLe_compatWith_eqProp.
  Proof. iis; eauto with *. Qed.

  Lemma rLt_implies_rLe (lhs : AczelSet) (rhs : AczelSet)
    (lhs_lt_rhs : lhs `rLt` rhs)
    : lhs `rLe` rhs.
  Proof.
    inversion lhs_lt_rhs. rewrite RANK_LE. clear lhs lhs_lt_rhs RANK_LE.
    revert rhs_child. induction rhs as [x_children x_childtrees IH].
    simpl in *. intros c_x. specialize IH with (c := c_x).
    destruct (x_childtrees c_x) as [z_children z_childtrees] eqn: x_c_eq_z.
    simpl in *. intros c_z. exists (c_x). rewrite x_c_eq_z. exact (IH c_z).
  Qed.

  Corollary elem_implies_rLt (lhs : AczelSet) (rhs : AczelSet)
    (lhs_in_rhs : lhs `elem` rhs)
    : lhs `rLt` rhs.
  Proof. destruct lhs_in_rhs as [rhs_child lhs_eq_rhs]. exists (rhs_child). now rewrite <- lhs_eq_rhs. Qed.

  Corollary rLe_rLt_rLt (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (x_le_y : x `rLe` y)
    (y_lt_z : y `rLt` z)
    : x `rLt` z.
  Proof. destruct y_lt_z as [c_z y_le_z_c]. exists (c_z). etransitivity; eauto with *. Qed.

  Lemma rLt_rLe_rLe (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (x_lt_y : x `rLt` y)
    (y_le_z : y `rLe` z)
    : x `rLt` z.
  Proof.
    destruct y as [y_children y_childtrees]. destruct x_lt_y as [c_y x_le_y_c]. destruct z as [z_children z_childtrees].
    simpl in *. pose proof (y_le_z c_y) as [c_z y_c_le_z_c]. exists (c_z). simpl. transitivity (y_childtrees c_y); eauto with *.
  Qed.

  Theorem rLt_isWellFounded
    : forall alpha : AczelSet, Acc ltPropOnRank alpha.
  Proof.
    intros rhs. remember (rhs) as lhs eqn: lhs_eq_rhs.
    assert (lhs_le_rhs : lhs `rLe` rhs) by now rewrite lhs_eq_rhs.
    clear lhs_eq_rhs. revert lhs lhs_le_rhs. induction rhs as [x_children x_childtrees IH].
    intros [y_children y_childtrees] y_le_x. econstructor. intros alpha alpha_lt_x.
    destruct alpha_lt_x as [c_y alpha_le_y_c]. simpl in *. destruct alpha as [alpha_base alpha_elems].
    pose proof (y_le_x c_y) as [c_x y_c_le_x_c]. eapply IH with (c := c_x). now transitivity (y_childtrees c_y).
  Qed.

  End RANK_OF_ACZEL_SET.

End AczelSet.
