Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module Univ.

  Monomorphic Universe AczelSetUniv_lv.

  Monomorphic Definition t : Type@{AczelSetUniv_lv + 1} := Type@{AczelSetUniv_lv}.

End Univ.

Module AczelSet. (* THANKS TO "Hanul Jeon" *)

  Inductive Tree : Univ.t :=
  | Node {children : Type} (childtrees : children -> Tree) : Tree
  .

  Definition AczelSet : Univ.t := Tree.

  Definition getChildren (root : AczelSet) : Type :=
    match root in Tree return Type with
    | @Node children childtrees => children
    end
  .

  Definition getChildTrees (root : AczelSet) : getChildren root -> AczelSet :=
    match root as tree in Tree return getChildren tree -> Tree with
    | @Node children childtrees => childtrees
    end
  .

(** "Relations on Set" *)

  Fixpoint eqTree (lhs : AczelSet) (rhs : AczelSet) : Prop :=
    match lhs in Tree, rhs in Tree return Prop with
    | Node childtrees1, Node childtrees2 => ⟪ lhs_simulates_rhs : forall child1, exists child2, eqTree (childtrees1 child1) (childtrees2 child2) ⟫ /\ ⟪ rhs_simulates_lhs : forall child2, exists child1, eqTree (childtrees1 child1) (childtrees2 child2) ⟫
    end
  .

  Global Instance eqTree_Reflexive
    : Reflexive eqTree.
  Proof.
    intros x; induction x as [x_children x_childtree IH].
    cbn in *; split; unnw; eauto.
  Defined.

  Local Hint Resolve eqTree_Reflexive : khan_hints.

  Global Instance eqTree_Symmetric
    : Symmetric eqTree.
  Proof.
    intros x; induction x as [x_children x_childtree IH]; intros [y_children y_childtree] [x_sim_y y_sim_x].
    cbn in *; split; unnw; [intros c_y | intros c_x].
    - exploit (y_sim_x c_y) as [c_x hyp_eq1]; eauto.
    - exploit (x_sim_y c_x) as [c_y hyp_eq1]; eauto.
  Defined.

  Local Hint Resolve eqTree_Symmetric : khan_hints.

  Global Instance eqTree_Transitive
    : Transitive eqTree.
  Proof.
    intros x y; revert x; induction y as [y_children y_childtree IH]; intros [x_children x_childtree] [z_children z_childtree] [x_sim_y y_sim_x] [y_sim_z z_sim_y].
    cbn in *; split; unnw; [intros c_x | intros c_z].
    - exploit (x_sim_y c_x) as [c_y hyp_eq1]; exploit (y_sim_z c_y) as [c_z hyp_eq2]; eauto.
    - exploit (z_sim_y c_z) as [c_y hyp_eq1]; exploit (y_sim_x c_y) as [c_x hyp_eq2]; eauto.
  Defined.

  Local Hint Resolve eqTree_Transitive : khan_hints.

  Local Instance eqTree_Equivalence : Equivalence eqTree :=
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

  Ltac unfold_eqTree := rewrite eqTree_unfold in *.

  Definition elem (finger : AczelSet) (hand : AczelSet) : Prop :=
    exists bone : getChildren hand, finger == getChildTrees hand bone
  .

  Local Hint Unfold elem : khan_hints.

  Local Infix " `elem` " := elem (at level 70, no associativity) : type_scope.

  Lemma elem_intro {z : AczelSet} {x : AczelSet} (c_x : getChildren x)
    (z_eq_x_c : z == getChildTrees x c_x)
    : z `elem` x.
  Proof. eauto with *. Defined.

  Lemma eqProp_elem_elem (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (x_eq_y : x == y)
    (y_in_z : y `elem` z)
    : x `elem` z.
  Proof. destruct y_in_z as [c_z y_eq_z_c]. eexists; etransitivity; eauto with *. Defined.

  Lemma elem_eqProp_elem (x : AczelSet) (y : AczelSet) (z : AczelSet)
    (y_eq_z : y == z)
    (x_in_y : x `elem` y)
    : x `elem` z.
  Proof.
    destruct z as [z_children z_childtree]; destruct y as [y_children y_childtree].
    destruct y_eq_z as [y_subset_z_c z_c_subset_y]; destruct x_in_y as [c_y x_eq_y_c].
    pose proof (y_subset_z_c c_y) as [c_z c_y_eq_c_z]. eexists; etransitivity; eauto with *.
  Defined.

  Global Add Parametric Morphism :
    elem with signature (eqProp ==> eqProp ==> iff)
    as elem_compatWith_eqProp.
  Proof with eauto with *.
    intros x1 y1 hyp_eq1 x2 y2 hyp_eq2.
    transitivity (x1 `elem` y2).
    - split; eapply elem_eqProp_elem...
    - split; eapply eqProp_elem_elem...
  Defined.

  Local Hint Resolve elem_compatWith_eqProp : khan_hints.

  Local Add Parametric Morphism :
    (Acc elem) with signature (eqProp ==> iff)
    as Acc_elem_compatWith_eqProp.
  Proof with eauto with *.
    enough (to_show : forall lhs : AczelSet, forall rhs : AczelSet, lhs == rhs -> Acc elem lhs -> Acc elem rhs).
    { intros x y h_eq. split; eapply to_show... }
    intros lhs rhs x_eq_y acc_x. cbn. pose proof (Acc_inv acc_x) as claim1. econstructor...
    intros z z_in_y. eapply claim1. rewrite x_eq_y...
  Defined.

  Lemma AczelSet_elem_well_founded
    : forall root : AczelSet, Acc elem root.
  Proof.
    induction root as [x_children x_childtree IH]. econstructor.
    intros z [c_x z_eq_x_c]. rewrite z_eq_x_c. exact (IH c_x).
  Defined.

  Global Instance AczelSet_isWellFounded : isWellFounded AczelSet :=
    { wfRel := elem
    ; wfRel_well_founded := AczelSet_elem_well_founded
    }
  .

  Lemma AczelSet_rect (phi : AczelSet -> Type)
    (IND : forall x : AczelSet, << IH : forall y : AczelSet, y `elem` x -> phi y >> -> phi x)
    : forall x : AczelSet, phi x.
  Proof. eapply NotherianRecursion. exact (IND). Defined.

  Theorem AczelSet_extensional_equality (lhs : AczelSet) (rhs : AczelSet)
    : lhs == rhs <-> << EXT_EQ : forall z : AczelSet, z `elem` lhs <-> z `elem` rhs >>.
  Proof with cbn; eauto with *.
    unnw. split.
    - intros h_eq z. rewrite h_eq. reflexivity.
    - revert rhs. induction lhs as [x_children x_childtree IH]; intros [y_children y_childtree].
      intros h_eq. simpl; unnw. split; [intros c_x | intros c_y].
      + assert (claim1 : x_childtree c_x `elem` Node x_childtree).
        { eapply elem_intro... }
        pose proof (proj1 (h_eq (x_childtree c_x)) claim1) as [c_y x_c_eq_y]...
      + assert (claim1 : y_childtree c_y `elem` Node y_childtree).
        { eapply elem_intro... }
        pose proof (proj2 (h_eq (y_childtree c_y)) claim1) as [c_x y_c_eq_x]...
  Qed.

  Definition subseteq (x : AczelSet) (y : AczelSet) : Prop :=
    forall z : AczelSet, z `elem` x -> z `elem` y
  .

  Local Infix " `subseteq` " := subseteq (at level 70, no associativity) : type_scope.

  Local Hint Unfold subseteq : khan_hints.

  Global Instance subseteq_PreOrder
    : PreOrder subseteq.
  Proof. split; eauto with *. Qed.

  Global Instance subseteq_PartialOrder
    : PartialOrder eqProp subseteq.
  Proof.
    intros lhs rhs. simpl. rewrite AczelSet_extensional_equality.
    unfold relation_conjunction, flip, subseteq. cbn; unnw. now firstorder.
  Qed.

  Lemma eqTree_intro (lhs : AczelSet) (rhs : AczelSet)
    (lhs_subseteq_rhs : lhs `subseteq` rhs)
    (rhs_subseteq_lhs : rhs `subseteq` lhs)
    : lhs == rhs.
  Proof. eapply subseteq_PartialOrder; split; eauto with *. Qed.

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

(** "Set Constructions" *)

  Section AczelSet_filtering.

  Definition filtering (x : AczelSet) (phi : getChildren x -> Prop) : AczelSet := Node (fun child : @sig (getChildren x) phi => getChildTrees x (proj1_sig child)).

  Theorem AczelSet_filtering_spec (x : AczelSet) (phi : getChildren x -> Prop)
    : forall z : AczelSet, z `elem` filtering x phi <-> << IN_filtering : exists c_x : getChildren x, z == getChildTrees x c_x /\ phi c_x >>.
  Proof with eauto with *.
    intros z. unnw; split.
    - intros [[c_x phi_c_x] z_eq_x_c]. simpl in *...
    - intros [c_x [z_eq_x_c phi_c_x]]. exists (exist _ c_x phi_c_x)...
  Qed.

  Corollary subset_filtering (x : AczelSet)
    : forall z : AczelSet, z `subseteq` x <-> << IS_A_SUBSET : exists phi : getChildren x -> Prop, z == filtering x phi >>.
  Proof with eauto with *.
    intros z. unnw. split.
    - intros z_subset_x. exists (fun c_x : getChildren x => getChildTrees x c_x `elem` z). eapply eqTree_intro.
      + intros y y_in_z. pose proof (z_subset_x y y_in_z) as [c_x y_eq_x_c].
        rewrite y_eq_x_c. rewrite y_eq_x_c in y_in_z. exists (exist _ c_x y_in_z)...
      + intros y [[c_x x_c_in_z] y_eq_x_c]. rewrite y_eq_x_c...
    - intros [phi z_eq]. rewrite z_eq. intros y. rewrite AczelSet_filtering_spec. unnw.
      intros [c_x [z_eq_x_c phi_c_x]]...
  Qed.

  End AczelSet_filtering.

  Section AczelSet_filter.

  Definition filter (phi : AczelSet -> Prop) (x : AczelSet) : AczelSet := filtering x (fun c_x : getChildren x => phi (getChildTrees x c_x)).

  Theorem AczelSet_filter_spec (x : AczelSet) (phi : AczelSet -> Prop)
    : forall z : AczelSet, z `elem` filter phi x <-> << IN_filter : exists c_x : getChildren x, phi (getChildTrees x c_x) /\ z == getChildTrees x c_x >>.
  Proof with eauto with *.
    intros z. unfold filter. rewrite AczelSet_filtering_spec. unnw; split.
    - intros [c_x [z_eq_x_c phi_z]]...
    - intros [c_x [phi_x_c z_eq]]...
  Qed.

  Corollary AczelSet_filter_MainProp (x : AczelSet) (phi : AczelSet -> Prop)
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

  Definition fromList (xs : list AczelSet) : AczelSet := Node (safe_nth xs).

  Theorem AczelSet_fromList_spec (xs : list AczelSet)
    : forall z : AczelSet, z `elem` fromList xs <-> << IN_fromList : exists i : Fin (length xs), z == safe_nth xs i >>.
  Proof with eauto with *.
    unnw; intros z; split.
    - intros [c_x z_eq_x_c]...
    - intros [i z_eq_xs_at_i]...
  Qed.

  End AczelSet_fromList.

  Section AczelSet_unions_i.

  Definition unions_i {I : Type} (xs : I -> AczelSet) : AczelSet := Node (fun child : {i : I & getChildren (xs i)} => getChildTrees (xs (projT1 child)) (projT2 child)).

  Theorem AczelSet_unions_i_spec {I : Type} (xs : I -> AczelSet)
    : forall z : AczelSet, z `elem` unions_i xs <-> << IN_unions_i : exists i : I, z `elem` xs i >>.
  Proof with eauto with *.
    intros z. unnw; split.
    - intros [[i c_u] z_eq_u_c]. simpl in *...
    - intros [i [c_u z_eq_u_c]]. exists (existT _ i c_u)...
  Qed.

  End AczelSet_unions_i.

  Section AczelSet_unions.

  Definition unions (x : AczelSet) : AczelSet := @unions_i (getChildren x) (getChildTrees x).

  Theorem AczelSet_unions_spec (x : AczelSet)
    : forall z : AczelSet, z `elem` unions x <-> << IN_unions : exists y : AczelSet, z `elem` y /\ y `elem` x >>.
  Proof with eauto with *.
    intros z. unfold unions. rewrite AczelSet_unions_i_spec. unnw; split.
    - intros [i [c_x z_eq_x_c]]. exists (getChildTrees x i). split...
    - intros [y [z_in_y [c_x y_eq_x_c]]]. exists (c_x). rewrite <- y_eq_x_c...
  Qed.

  End AczelSet_unions.

  Section AczelSet_empty.

  Definition empty : AczelSet := Node (fun hyp_false : False => False_rect AczelSet hyp_false).

  Lemma AczelSet_empty_spec
    : forall z : AczelSet, z `elem` empty <-> (False).
  Proof. intros z. unfold empty. split; [intros [c z_eq_c] | tauto]; eauto with *. Qed.

  End AczelSet_empty.

  Section AczelSet_union.

  Definition union (x1 : AczelSet) (x2 : AczelSet) : AczelSet := unions_i (fun b : bool => if b then x1 else x2).

  Lemma AczelSet_union_spec (x1 : AczelSet) (x2 : AczelSet)
    : forall z : AczelSet, z `elem` union x1 x2 <-> (z `elem` x1 \/ z `elem` x2).
  Proof.
    intros z. unfold union. rewrite AczelSet_unions_i_spec. unnw.
    split; [intros [[ | ] z_in] | intros [z_in | z_in]; [exists (true) | exists (false)]]; eauto with *.
  Qed.

  End AczelSet_union.

  Section AczelSet_singleton.

  Definition singleton (x : AczelSet) : AczelSet := fromList (cons x nil).

  Lemma AczelSet_singleton_spec (x : AczelSet)
    : forall z : AczelSet, z `elem` singleton x <-> (z == x).
  Proof.
    intros z. unfold singleton. rewrite AczelSet_fromList_spec. unnw; cbn; unfold_eqTree; split.
    - intros [i z_eq]. revert i z_eq. now introFinS i.
    - intros z_eq_x. now exists (FZ).
  Qed.

  End AczelSet_singleton.

  Section AczelSet_Nat.

  Definition Suc (x : AczelSet) : AczelSet := union x (singleton x).

  Fixpoint natToAczelSet (n : nat) {struct n} : AczelSet :=
    match n with
    | O => empty
    | S n' => Suc (natToAczelSet n')
    end
  .

  Definition Nat : AczelSet := unions_i natToAczelSet.

  End AczelSet_Nat.

  Section AczelSet_fromWf.

  Definition fromAcc {A : Type} {wfRel : A -> A -> Prop} : forall root : A, Acc wfRel root -> AczelSet :=
    fix fromAcc_fix (tree : A) (tree_acc : Acc wfRel tree) {struct tree_acc} : AczelSet :=
    match tree_acc with
    | Acc_intro _ hyp_acc => Node (fun child : {subtree : A | wfRel subtree tree} => fromAcc_fix (proj1_sig child) (hyp_acc (proj1_sig child) (proj2_sig child)))
    end
  .

  Lemma fromAcc_unfold {A : Type} {wfRel : A -> A -> Prop} (tree : A) (tree_acc : Acc wfRel tree)
    : forall z : AczelSet, z `elem` fromAcc tree tree_acc <-> << EXPANDED : exists child : {subtree : A | wfRel subtree tree}, z == fromAcc (proj1_sig child) (Acc_inv tree_acc (proj2_sig child)) >>.
  Proof.
    intros z. destruct tree_acc as [hyp_acc]. unnw; split.
    all: intros [[c hyp_wf] z_eq_c]; cbn in *; unfold_eqTree; now exists (exist _ c hyp_wf).
  Qed.

  Definition fromWf (A : Type) {requiresWellFounded : isWellFounded A} : AczelSet := unions_i (fun root : A => fromAcc root (wfRel_well_founded root)).

  End AczelSet_fromWf.

  Section AczelSet_STRONG_COLLECTION.

  (* << A Sketch of the Proof of Strong Collection >>
    -- Advise of "Hanul Jeon"
    > Aczel의 Strong Collection의 증명을 스케치해보면
      Let's sketch the Aczel's proof of Strong Collection.
    > 우선 forall x:X, exists y phi(x,y)가 성립한다고 합시다
      First, assume that $forall x \in X, exists y, phi(x, y)$.
    > 여기서 AC를 적용해서 f : forall x:X, phi(x,f(x))인 f를 찾고
      By applying AC, find $f$ such that $forall x \in X, phi(x, f(x))$.
    > base set을 X의 base와 똑같이 잡을 겁니다
      Now, take the base set as that of $X$.
    > 그리고 원소는 f(x)에 대응하게끔 잡을 거고요
      And set the elements corresponding to $f(x)$.
    > 문제는 AC가 Coq에서 작동할 것 같지 않다는 거네요
      Although, the problem is that AC may not work on Coq.
  *)

  Hypothesis AxiomOfChoice : forall A : Type, forall B : Type, forall phi : A -> B -> Prop, << NONEMPTY : forall x : A, exists y : B, phi x y >> -> << CHOICE : exists f : A -> B, forall x : A, phi x (f x) >>.

  Theorem AxiomOfChoice_implies_StrongCollection (X : AczelSet) (phi : AczelSet -> AczelSet -> Prop)
    (phi_compatWith_eqTree_on_1st_arg : forall y : AczelSet, compatWith_eqTree (fun x : AczelSet => phi x y))
    (phi_compatWith_eqTree_on_2nd_arg : forall x : AczelSet, compatWith_eqTree (fun y : AczelSet => phi x y))
    (NONEMPTY : forall x : AczelSet, x `elem` X -> exists y : AczelSet, phi x y)
    : exists Y : AczelSet, ⟪ FST_COLLECTION : forall x : AczelSet, x `elem` X -> exists y : AczelSet, y `elem` Y /\ phi x y ⟫ /\ ⟪ SND_COLLECTION : forall y : AczelSet, elem y Y -> exists x : AczelSet, elem x X /\ phi x y ⟫.
  Proof with eauto with *.
    set (base_set := getChildren X). unnw.
    assert (claim1 : exists f : base_set -> AczelSet, forall x : base_set, phi (getChildTrees X x) (f x)).
    { eapply AxiomOfChoice with (phi := fun x : base_set => fun y : AczelSet => phi (getChildTrees X x) y)... }
    destruct claim1 as [f claim1]. exists (@Node base_set (fun x : base_set => f x)). split.
    - intros x [c_X x_eq_X_c]. exists (f c_X). split... eapply phi_compatWith_eqTree_on_1st_arg...
    - intros x [c_X x_eq_X_c]. exists (getChildTrees X c_X). split... eapply phi_compatWith_eqTree_on_2nd_arg...
  Qed.

  End AczelSet_STRONG_COLLECTION.

(** "Ordinals" *)

  Definition isTransitiveSet (x : AczelSet) : Prop :=
    forall y : AczelSet, y `elem` x ->
    forall z : AczelSet, z `elem` y ->
    z `elem` x
  .

  Inductive isOrdinal (alpha : AczelSet) : Prop :=
  | transitive_set_of_transitive_sets_isOrdinal
    (IS_TRANSITIVE_SET : isTransitiveSet alpha)
    (every_member_IS_TRANSITIVE_SET : forall beta, beta `elem` alpha -> isTransitiveSet beta)
    : isOrdinal alpha
  .

  Local Hint Constructors isOrdinal : khan_hints.

  Lemma every_member_of_Ordinal_isOrdinal (alpha : AczelSet)
    (alpha_isOrdinal : isOrdinal alpha)
    : forall beta : AczelSet, beta `elem` alpha -> isOrdinal beta.
  Proof. inversion alpha_isOrdinal; eauto with *. Qed.

  Definition Ordinals : Univ.t := @sig AczelSet isOrdinal.

  Definition unliftOrdinalsToAczelSet : Ordinals -> AczelSet := @proj1_sig AczelSet isOrdinal.

  Global Coercion unliftOrdinalsToAczelSet : Ordinals >-> AczelSet.

End AczelSet.
