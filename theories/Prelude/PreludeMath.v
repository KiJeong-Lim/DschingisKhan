Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module MathProps.

  Class preserves_eqProp1 {dom : Hask.t} {cod : Hask.t} {dom_isSetoid : isSetoid dom} {cod_isSetoid : isSetoid cod} (unary_op : dom -> cod) : Prop :=
    eqProp_lifted1 (lhs1 : dom) (rhs1 : dom)
      (H_EQ1 : lhs1 == rhs1)
      : unary_op lhs1 == unary_op rhs1
  .

  Global Add Parametric Morphism {dom : Hask.t} {cod : Hask.t} {dom_isSetoid : isSetoid dom} {cod_isSetoid : isSetoid cod} (unary_op : dom -> cod) {preserves_eqProp : preserves_eqProp1 unary_op} :
    unary_op with signature (eqProp ==> eqProp)
    as congruence_guarantees_eqProp_lifted1.
  Proof. intros x1 x2 H_x_eq; exact (eqProp_lifted1 x1 x2 H_x_eq). Defined.

  Class preserves_eqProp2 {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isSetoid : isSetoid dom1} {dom2_isSetoid : isSetoid dom2} {cod_isSetoid : isSetoid cod} (binary_op : dom1 -> dom2 -> cod) : Prop :=
    eqProp_lifted2 (lhs1 : dom1) (rhs1 : dom1) (lhs2 : dom2) (rhs2 : dom2)
      (H_EQ1 : lhs1 == rhs1)
      (H_EQ2 : lhs2 == rhs2)
      : binary_op lhs1 lhs2 == binary_op rhs1 rhs2
  .

  Global Add Parametric Morphism {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isSetoid : isSetoid dom1} {dom2_isSetoid : isSetoid dom2} {cod_isSetoid : isSetoid cod} (binary_op : dom1 -> dom2 -> cod) {preserves_eqProp : preserves_eqProp2 binary_op} :
    binary_op with signature (eqProp ==> eqProp ==> eqProp)
    as congruence_guaranteeseqProp_lifted2.
  Proof. intros x1 x2 H_x_eq y1 y2 H_y_eq; exact (eqProp_lifted2 x1 x2 y1 y2 H_x_eq H_y_eq). Defined.

  Class preserves_leProp1 {dom : Hask.t} {cod : Hask.t} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (unary_op : dom -> cod) : Prop :=
    leProp_lifted1 (lhs1 : dom) (rhs1 : dom)
      (H_LE1 : lhs1 =< rhs1)
      : unary_op lhs1 =< unary_op rhs1
  .

  Global Add Parametric Morphism {dom : Hask.t} {cod : Hask.t} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (unary_op : dom -> cod) {preserves_leProp : preserves_leProp1 unary_op} :
    unary_op with signature (leProp ==> leProp)
    as monotonic_guarantees_leProp_lifted1.
  Proof. intros x1 x2 H_x_le; exact (leProp_lifted1 x1 x2 H_x_le). Defined.

  Global Add Parametric Morphism {dom : Hask.t} {cod : Hask.t} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (unary_op : dom -> cod) {preserves_leProp : preserves_leProp1 unary_op} :
    unary_op with signature (eqProp ==> eqProp)
    as monotonic_guarantees_eqProp_lifted1.
  Proof. ii. eapply leProp_Antisymmetric; eapply preserves_leProp; now eapply eqProp_implies_leProp. Qed.

  Class preserves_leProp2 {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isPoset : isPoset dom1} {dom2_isPoset : isPoset dom2} {cod_isPoset : isPoset cod} (binary_op : dom1 -> dom2 -> cod) : Prop :=
    leProp_lifted2 (lhs1 : dom1) (rhs1 : dom1) (lhs2 : dom2) (rhs2 : dom2)
      (H_LE1 : lhs1 =< rhs1)
      (H_LE2 : lhs2 =< rhs2)
      : binary_op lhs1 lhs2 =< binary_op rhs1 rhs2
  .

  Global Add Parametric Morphism {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isPoset : isPoset dom1} {dom2_isPoset : isPoset dom2} {cod_isPoset : isPoset cod} (binary_op : dom1 -> dom2 -> cod) {preserves_leProp : preserves_leProp2 binary_op} :
    binary_op with signature (leProp ==> leProp ==> leProp)
    as monotonic_guarantees_leProp_lifted2.
  Proof. intros x1 x2 H_x_le y1 y2 H_y_le; exact (leProp_lifted2 x1 x2 y1 y2 H_x_le H_y_le). Defined.

  Global Add Parametric Morphism {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isPoset : isPoset dom1} {dom2_isPoset : isPoset dom2} {cod_isSetoid : isPoset cod} (binary_op : dom1 -> dom2 -> cod) {preserves_leProp : preserves_leProp2 binary_op} :
    binary_op with signature (eqProp ==> eqProp ==> eqProp)
    as monotonic_guarantees_eqProp_lifted2.
  Proof. ii. eapply leProp_Antisymmetric; eapply preserves_leProp; now eapply eqProp_implies_leProp. Qed.

  Section STATEMENTS_FOR_OPERATION_PROPERTIES.

  Context {A : Hask.t} {requiresSetoid : isSetoid A}.

  Class Assoc (bin_op : A -> A -> A) : Prop :=
    associativity (x : A) (y : A) (z : A)
      : bin_op x (bin_op y z) == bin_op (bin_op x y) z
  .

  Class Comm (bin_op : A -> A -> A) : Prop :=
    commutativity (x : A) (y : A)
      : bin_op x y == bin_op y x
  .

  Class Idem (bin_op : A -> A -> A) : Prop :=
    idemponence (x : A)
      : bin_op x x == x
  .

  Class Distr (bin_op1 : A -> A -> A) (bin_op2 : A -> A -> A) : Prop :=
    { left_distr (x : A) (y : A) (z : A)
      : bin_op1 x (bin_op2 y z) == bin_op2 (bin_op1 x y) (bin_op1 x z)
    ; right_distr (x : A) (y : A) (z : A)
      : bin_op1 (bin_op2 y z) x == bin_op2 (bin_op1 y x) (bin_op1 z x)
    }
  .

  Class IdElemOf (e : A) (bin_op : A -> A -> A) : Prop :=
    { left_id (x : A)
      : bin_op e x == x
    ; right_id (x : A)
      : bin_op x e == x
    }
  .

  Class InvOpOf (inv : A -> A) (bin_op : A -> A -> A) {e : A} {e_id_bin_op : IdElemOf e bin_op} : Prop :=
    { left_inv (x : A)
      : bin_op (inv x) x == e
    ; right_inv (x : A)
      : bin_op x (inv x) == e
    }
  .

  Class Absorption (bin_op1 : A -> A -> A) (bin_op2 : A -> A -> A) : Prop :=
    { abosortion_left (x : A) (y : A)
      : bin_op1 x (bin_op2 x y) == x
    ; abosortion_right (x : A) (y : A)
      : bin_op2 x (bin_op1 x y) == x
    }
  .

  Class Annihilator (a : A) (bin_op : A -> A -> A) : Prop :=
    { leftAnnihilator : forall x : A, bin_op a x == a
    ; rightAnnihilator : forall x : A, bin_op x a == a
    }
  .

  End STATEMENTS_FOR_OPERATION_PROPERTIES.

  Global Infix " `distributesOver` " := Distr (at level 70, no associativity) : type_scope.
  Global Infix " `isIdentityOf` " := IdElemOf (at level 70, no associativity) : type_scope.
  Global Infix " `isInverseOpFor` " := InvOpOf (at level 70, no associativity) : type_scope.
  Global Infix " `isAnnihilatorFor` " := Annihilator (at level 70, no associativity) : type_scope.

  Definition isInjective {dom : Hask.t} {cod : Hask.t} (f : Hask.arrow dom cod) : Prop :=
    forall x1 : dom, forall x2 : dom, << f_x1_eq_f_x2 : f x1 = f x2 >> -> << x1_eq_x2 : x1 = x2 >>
  .

  Definition isSurjection {dom : Hask.t} {cod : Hask.t} (f : Hask.arrow dom cod) : Type :=
    forall y : cod, {x : dom | << y_is_f_x : y = f x >>}
  .

  Definition isSurjective {dom : Hask.t} {cod : Hask.t} (f : Hask.arrow dom cod) : Prop :=
    forall y : cod, exists x : dom, << y_is_f_x : y = f x >>
  .

  Class Equipotent (dom : Hask.t) (cod : Hask.t) : Type :=
    { bijection : dom -> cod
    ; bijectionInjective : isInjective bijection
    ; bijectionSurjective : isSurjection bijection
    }
  .

  Section CARDINALITY_EQUIVALENCE.

  Definition haveSameCard (lhs : Hask.t) (rhs : Hask.t) : Prop := inhabited (Equipotent lhs rhs).

  Local Instance Equipotent_Equivalence
    : Equivalence haveSameCard.
  Proof.
    split.
    - intros A.
      econstructor. exists (fun x : A => x).
      + intros x1 x2 H_x_EQ. congruence.
      + intros x. exists (x). exact (@eq_refl A x).
    - intros A B [[bijection_A_to_B bijection_A_to_B_inj bijection_A_to_B_surj]].
      econstructor. exists (fun y : B => proj1_sig (bijection_A_to_B_surj y)).
      + intros y1 y2 H_EQ. destruct (bijection_A_to_B_surj y1) as [x1 y1_is]. destruct (bijection_A_to_B_surj y2) as [x2 y2_is]. unnw. subst y1 y2. simpl in *. congruence.
      + intros x. exists (bijection_A_to_B x). destruct (bijection_A_to_B_surj (bijection_A_to_B x)) as [x' H_x_EQ]. unnw. simpl in *. exact (bijection_A_to_B_inj x x' H_x_EQ).
    - intros A B C [[bijection_A_to_B bijection_A_to_B_inj bijection_A_to_B_surj]] [[bijection_B_to_C bijection_B_to_C_inj bijection_B_to_C_surj]].
      econstructor. exists (fun x : A => bijection_B_to_C (bijection_A_to_B x)).
      + intros x1 x2 H_EQ. eapply bijection_A_to_B_inj, bijection_B_to_C_inj. exact (H_EQ).
      + intros z. destruct (bijection_B_to_C_surj z) as [y z_is]. destruct (bijection_A_to_B_surj y) as [x y_is]. unnw. exists (x). congruence.
  Qed.

  Global Instance Hask_isSetoid : isSetoid Hask.t :=
    { eqProp := haveSameCard
    ; eqProp_Equivalence := Equipotent_Equivalence
    }
  .

  End CARDINALITY_EQUIVALENCE.

  Class isCountable (dom : Hask.t) : Type :=
    { enum : nat -> dom
    ; enum_isSurjective : isSurjective enum
    }
  .

  Class isRecursivelyEnumerable (dom : Hask.t) : Type :=
    { RecursivelyEnumerable_requiresCountable :> isCountable dom
    ; enum_isSurjection : isSurjection enum
    }
  .

  Definition isDecidable {X : Hask.t} (Y : ensemble X) : Type :=
    forall y : X, {member y Y} + {~ member y Y}
  .

  Class EqDec (dom : Hask.t) : Type := eq_dec (x : dom) : isDecidable (@eq dom x).

  Global Arguments eq_dec {dom} {EqDec} (x) (y) : simpl nomatch.

  Global Instance boolEqDec : EqDec bool :=
    { eq_dec (x : bool) (y : bool) :=
      match x as lhs, y as rhs return {lhs = rhs} + {lhs <> rhs} with
      | true, true => left (@eq_refl bool true)
      | true, false => right (fun H_EQ : true = false => @eq_ind bool true (fun b : bool => if b then True else False) I false H_EQ)
      | false, true => right (fun H_EQ : false = true => @eq_ind bool false (fun b : bool => if b then False else True) I true H_EQ)
      | false, false => left (@eq_refl bool false)
      end
    }
  .

  Section ORDER_THEORIC_CONCEPTS.

  Local Notation " x '>=' y " := (leProp y x) (only parsing) : type_scope.

  Context {D : Type}.

  Definition PrefixedPoints {requiresPoset : isPoset D} (f : D -> D) : ensemble D :=
    fun x : D => (x >= f x)%type
  .

  Definition FixedPoints {requiresSetoid : isSetoid D} (f : D -> D) : ensemble D :=
    fun x : D => (x == f x)%type
  .

  Definition PostfixedPoints {requiresPoset : isPoset D} (f : D -> D) : ensemble D :=
    fun x : D => (x =< f x)%type
  .

  Definition UpperBoundsOf {requiresPoset : isPoset D} (X : ensemble D) : ensemble D :=
    fun upper_bound : D => forall x : D, << H_IN : member x X >> -> (x =< upper_bound)%type
  .

  Definition LowerBoundsOf {requiresPoset : isPoset D} (X : ensemble D) : ensemble D :=
    fun lower_bound : D => forall x : D, << H_IN : member x X >> -> (x >= lower_bound)%type
  .

  Definition isSupremumOf {requiresPoset : isPoset D} (sup_X : D) (X : ensemble D) : Prop :=
    forall upper_bound : D, << SUPREMUM_LE_UPPER_BOUND : (sup_X =< upper_bound)%type >> <-> << UPPER_BOUND : member upper_bound (UpperBoundsOf X) >>
  .

  Definition isInfimumOf {requiresPoset : isPoset D} (inf_X : D) (X : ensemble D) : Prop :=
    forall lower_bound : D, << LOWER_BOUND_LE_INFIMUM : (inf_X >= lower_bound)%type >> <-> << LOWER_BOUND : member lower_bound (LowerBoundsOf X) >>
  .

  End ORDER_THEORIC_CONCEPTS.

End MathProps.

Export MathProps.

Module Ensembles.

  Import ListNotations.

  Global Infix " \in " := member (at level 70, no associativity) : type_scope.

  Inductive union {A : Hask.t} (X1 : ensemble A) (X2 : ensemble A) (z : A) : Prop :=
  | In_union_l
    (z_in_X1 : z \in X1)
    : z \in union X1 X2
  | In_union_r
    (z_in_X2 : z \in X2)
    : z \in union X1 X2
  .

  Inductive unions_i {A : Hask.t} {I : Hask.t} (Xs : Hask.arrow I (ensemble A)) (z : A) : Prop :=
  | In_unions_i (i : I)
    (z_in_Xs_i : z \in Xs i)
    : z \in unions_i Xs
  .

  Inductive unions {A : Hask.t} (Xs : ensemble (ensemble A)) (z : A) : Prop :=
  | In_unions (X : ensemble A)
    (z_in_X : z \in X)
    (X_in_Xs : X \in Xs)
    : z \in unions Xs
  .

  Inductive image {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (X : ensemble A) (y : B) : Prop :=
  | In_image (x : A)
    (x_in_X : x \in X)
    (y_eq_f_x : y = f x)
    : y \in image f X
  .

  Inductive preimage {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (Y : ensemble B) (x : A) : Prop :=
  | In_preimage
    (f_x_in_Y : f x \in Y)
    : x \in preimage f Y
  .

  Inductive finite {A : Hask.t} (xs : list A) (z : A) : Prop :=
  | In_finite
    (z_in_xs : In z xs)
    : z \in finite xs
  .

  Inductive intersection {A : Hask.t} (X1 : ensemble A) (X2 : ensemble A) (z : A) : Prop :=
  | In_intersection
    (z_in_X1 : z \in X1)
    (z_in_X2 : z \in X2)
    : z \in intersection X1 X2
  .

  Inductive full {A : Hask.t} (z : A) : Prop :=
  | In_full
    : z \in full
  .

  Inductive empty {A : Hask.t} (z : A) : Prop :=
  .

  Local Hint Constructors union unions_i unions image preimage finite intersection full empty : core.

  Definition complement {A : Hask.t} (X : ensemble A) : ensemble A := fun z : A => ~ z \in X.

  Definition setminus {A : Hask.t} (X1 : ensemble A) (X2 : ensemble A) : ensemble A := intersection X1 (complement X2).

  Definition singleton {A : Hask.t} (x : A) : ensemble A := fun z : A => x = z.

  Definition delete {A : Hask.t} (x : A) (X : ensemble A) : ensemble A := setminus X (singleton x).

  Definition insert {A : Hask.t} (x : A) (X : ensemble A) : ensemble A := union (singleton x) X.

  Lemma in_union_iff {A : Hask.t} (X1 : ensemble A) (X2 : ensemble A)
    : forall z : A, z \in union X1 X2 <-> (z \in X1 \/ z \in X2).
  Proof. intros z; split; intros [H_l | H_r]; eauto. Qed.

  Lemma in_unions_i_iff {A : Hask.t} {I : Hask.t} (Xs : Hask.arrow I (ensemble A))
    : forall z : A, z \in unions_i Xs <-> (exists i : I, z \in Xs i).
  Proof. intros z; split; intros [i H_i]; eauto. Qed.

  Lemma in_unions_iff {A : Hask.t} (Xs : ensemble (ensemble A))
    : forall z : A, z \in unions Xs <-> (exists X : ensemble A, z \in X /\ X \in Xs).
  Proof. intros z; split; [intros [X H_X H_Xs] | intros [X [H_X H_Xs]]]; eauto. Qed.

  Lemma in_image_iff {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (X : ensemble A)
    : forall y : B, y \in image f X <-> (exists x : A, y = f x /\ x \in X).
  Proof. intros y; split; [intros [x H_x H_y] | intros [x [H_x H_y]]]; eauto. Qed.

  Lemma in_preimage_iff {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (Y : ensemble B)
    : forall x : A, x \in preimage f Y <-> (exists y : B, y = f x /\ y \in Y).
  Proof. intros x; split; [intros [H_x] | intros [y [H_x H_y]]; subst]; eauto. Qed.

  Lemma in_finite_iff {A : Hask.t} (xs : list A)
    : forall z : A, z \in finite xs <-> (In z xs).
  Proof. intros z; split; [intros [H_x] | intros H_x]; eauto. Qed.

  Lemma in_intersection_iff {A : Hask.t} (X1 : ensemble A) (X2 : ensemble A)
    : forall z : A, z \in intersection X1 X2 <-> (z \in X1 /\ z \in X2).
  Proof. intros z; split; intros [H_l H_r]; eauto. Qed.

  Lemma in_full_iff {A : Hask.t}
    : forall z : A, z \in full <-> (True).
  Proof. intros z; split; eauto. Qed.

  Lemma in_empty_iff {A : Hask.t}
    : forall z : A, z \in empty <-> (False).
  Proof. intros z; split; intros []. Qed.

  Lemma in_complement_iff {A : Hask.t} (X : ensemble A)
    : forall z : A, z \in complement X <-> (~ z \in X).
  Proof. reflexivity. Qed.

  Lemma in_setminus_iff {A : Hask.t} (X1 : ensemble A) (X2 : ensemble A)
    : forall z : A, z \in setminus X1 X2 <-> (z \in X1 /\ ~ z \in X2).
  Proof. intros z. unfold setminus. rewrite in_intersection_iff, in_complement_iff. tauto. Qed.

  Lemma in_singleton_iff {A : Hask.t} (x : A)
    : forall z : A, z \in singleton x <-> (x = z).
  Proof. intros z. reflexivity. Qed.

  Lemma in_delete_iff {A : Hask.t} (x : A) (X : ensemble A)
    : forall z : A, z \in delete x X <-> (x <> z /\ z \in X).
  Proof. intros z. unfold delete. rewrite in_setminus_iff, in_singleton_iff. tauto. Qed.

  Lemma in_insert_iff {A : Hask.t} (x : A) (X : ensemble A)
    : forall z : A, z \in insert x X <-> (x = z \/ z \in X).
  Proof. intros z. unfold insert. rewrite in_union_iff, in_singleton_iff. tauto. Qed.

  Local Instance Powerset_isCovariantFunctor : isCovariantFunctor ensemble := { fmap {A : Hask.t} {B : Hask.t} := image (A := A) (B := B) }.
  Local Instance Powerset_isContravariantFunctor : isContravariantFunctor ensemble := { contramap {B : Hask.t} {A : Hask.t} := preimage (A := A) (B := B) }.

  Create HintDb ensemble_hints.
  Global Hint Rewrite @in_union_iff @in_unions_i_iff @in_image_iff @in_preimage_iff @in_finite_iff @in_intersection_iff @in_full_iff @in_empty_iff @in_complement_iff @in_setminus_iff @in_singleton_iff @in_delete_iff @in_insert_iff using eauto : ensemble_hints.

  Global Add Parametric Morphism (A : Type) :
    (@member A) with signature (eq ==> leProp ==> impl)
    as member_eq_leProp_with_impl.
  Proof. ii. cbv in *. eauto. Qed.

  Global Add Parametric Morphism (A : Type) :
    (@member A) with signature (eq ==> eqProp ==> iff)
    as member_eq_eqProp_with_iff.
  Proof. ii. cbv in *. eauto. Qed.

  Section POWERSET_MONAD.

  Definition ensemble_pure {A : Hask.t} (x : A) : ensemble A := fun z : A => x = z.

  Definition ensemble_bind {A : Hask.t} {B : Hask.t} (X : ensemble A) (k : A -> ensemble B) : ensemble B := fun z : B => exists x : A, member x X /\ member z (k x).

  Global Instance ensemble_isMonad : isMonad ensemble :=
    { pure {A : Hask.t} := ensemble_pure (A := A)
    ; bind {A : Hask.t} {B : Hask.t} := ensemble_bind (A := A) (B := B)
    }
  .

  Local Instance ensemble_isSetoid1 : isSetoid1 ensemble :=
    { liftSetoid1 {X : Hask.t} (X_isSetoid : isSetoid X) := @ensemble_isSetoid X
    }
  .

  Global Instance ensemble_obeyMonadLaws
    : LawsOfMonad ensemble.
  Proof with try now firstorder. split; vm_compute... all: des... Qed.

  End POWERSET_MONAD.

  Section WITH_LIST.

  Definition isFiniteSubsetOf {A : Type} (xs : list A) (X : ensemble A) : Prop := forall z : A, In z xs -> member z X.

  Definition isListRepOf {A : Type} (xs : list A) (X : ensemble A) : Prop := forall z : A, In z xs <-> member z X.

  Context {A : Type}.

  Lemma isFiniteSubsetOf_nil
    : isFiniteSubsetOf [] (@empty A).
  Proof. unfold isFiniteSubsetOf in *. simpl. tauto. Qed.

  Lemma isListRepOf_nil
    : isListRepOf [] (@empty A).
  Proof.
    unfold isListRepOf in *. intro. simpl.
    rewrite in_empty_iff. tauto.
  Qed.

  Lemma isFiniteSubsetOf_cons (x : A) (xs : list A) (X : ensemble A)
    (xs_isFiniteSubsetOf_X : isFiniteSubsetOf xs X)
    : isFiniteSubsetOf (x :: xs) (insert x X).
  Proof. unfold isFiniteSubsetOf in *. simpl. now firstorder. Qed.

  Lemma isListRepOf_cons (x : A) (xs : list A) (X : ensemble A)
    (xs_isListRepOf_X : isListRepOf xs X)
    : isListRepOf (x :: xs) (insert x X).
  Proof. unfold isListRepOf in *. simpl. now firstorder. Qed.

  Lemma isFiniteSubsetOf_append (xs1 : list A) (xs2 : list A) (X : ensemble A)
    (xs1_isFiniteSubsetOf_X : isFiniteSubsetOf xs1 X)
    (xs2_isFiniteSubsetOf_X : isFiniteSubsetOf xs2 X)
    : isFiniteSubsetOf (xs1 ++ xs2) X.
  Proof.
    unfold isFiniteSubsetOf in *. intro.
    rewrite in_app_iff. now firstorder.
  Qed.

  Lemma isListRepOf_append (xs1 : list A) (xs2 : list A) (X1 : ensemble A) (X2 : ensemble A)
    (xs1_isListRepOf_X : isListRepOf xs1 X1)
    (xs2_isListRepOf_X : isListRepOf xs2 X2)
    : isListRepOf (xs1 ++ xs2) (union X1 X2).
  Proof.
    unfold isListRepOf in *. intro.
    rewrite in_app_iff. now firstorder.
  Qed.

  Lemma isFiniteSubsetOf_remove {requireEqDec : EqDec A} (x : A) (xs : list A) (X : ensemble A)
    (xs_isFiniteSubsetOf_insert_x_X : isFiniteSubsetOf xs (insert x X))
    : isFiniteSubsetOf (remove eq_dec x xs) X.
  Proof.
    unfold isListRepOf in *. intros z z_in.
    exploit (in_remove eq_dec xs z x z_in) as [z_in_xs z_ne_x].
    pose proof (xs_isFiniteSubsetOf_insert_x_X z z_in_xs) as claim1.
    eapply in_insert_iff in claim1. destruct claim1 as [x_eq_z | z_in_X].
    - now contradiction (z_ne_x).
    - now firstorder.
  Qed.

  Lemma isListRepOf_remove {requireEqDec : EqDec A} (x : A) (xs : list A) (X : ensemble A)
    (xs_isListRepOf_insert_x_X : isListRepOf xs X)
    : isListRepOf (remove eq_dec x xs) (delete x X).
  Proof.
    unfold isListRepOf in *. intros z.
    pose proof (in_remove eq_dec xs z x) as claim1.
    pose proof (in_in_remove eq_dec xs) as claim2.
    rewrite in_delete_iff. now firstorder.
  Qed.

  End WITH_LIST.

  Global Hint Unfold isFiniteSubsetOf isListRepOf : khan_hints.

  Section SUBSET_INTRO.

  Context {A : Type}.

  Lemma isSubsetOf_insert_if (x : A) (X1 : ensemble A) (X2 : ensemble A)
    (X1_isSubsetOf_X2 : isSubsetOf X1 X2)
    : isSubsetOf (insert x X1) (insert x X2).
  Proof. intros z. rewrite in_insert_iff. unfold isSubsetOf in *. now firstorder. Qed.

  Lemma isSubsetOf_singleton_if (x : A) (X : ensemble A)
    (x_in_X : member x X)
    : isSubsetOf (singleton x) X.
  Proof. intros z. rewrite in_singleton_iff. des. now firstorder. Qed.

  Lemma isSubsetOf_empty_if (X : ensemble A)
    : isSubsetOf empty X.
  Proof. intros z. rewrite in_empty_iff. tauto. Qed.

  End SUBSET_INTRO.

  Global Hint Resolve isSubsetOf_insert_if isSubsetOf_singleton_if isSubsetOf_empty_if : ensemble_hints.

  Definition isFilterReprOf {A : Hask.t} (phi : A -> Prop) (X_repr : ensemble (@sig A phi)) (X : ensemble A) : Prop :=
    forall z : @sig A phi, member (proj1_sig z) X <-> member z X_repr
  .

  Global Hint Unfold isFilterReprOf : khan_hints.

  Theorem isFilterReprOf_iff {A : Hask.t} (phi : A -> Prop) (X : ensemble A)
    : forall X_repr : ensemble (@sig A phi), << FILTER_REPR : isFilterReprOf phi X_repr X >> <-> << REPR_IS_PREIMAGE : X_repr == preimage (@proj1_sig A phi) X >>.
  Proof with eauto with *.
    iis.
    { intros H_REPR z; desnw. rewrite <- FILTER_REPR, in_preimage_iff. des... }
    { intros H_preimage z; desnw. rewrite REPR_IS_PREIMAGE, in_preimage_iff; des... }
  Qed.

  Corollary isFilterReprOf_implies {A : Hask.t} (phi : A -> Prop) (X_repr : ensemble (@sig A phi)) (X : ensemble A)
    (X_repr_isFilterReprOf_X : isFilterReprOf phi X_repr X)
    : image (@proj1_sig A phi) X_repr == intersection X phi.
  Proof with eauto with *.
    intros z. split.
    - intros z_in. inversion z_in; subst. econstructor.
      + eapply X_repr_isFilterReprOf_X...
      + exact (@proj2_sig A phi x).
    - intros z_in. apply in_intersection_iff in z_in. destruct z_in as [z_in_X phi_z]. 
      pose proof (proj1 (X_repr_isFilterReprOf_X (exist _ z phi_z)) z_in_X) as z_in_X_repr...
  Qed.

  Definition fromSequence {I : Type} {A : Type} (x_i : I -> A) : ensemble A :=
    fun x : A => exists i : I, x = x_i i
  .

  Definition Rel_id {A : Type} : ensemble (A * A) :=
    fun '(lhs, rhs) => lhs = rhs
  .

  Definition Rel_flip {A : Type} {B : Type} (X : ensemble (A * B)) : ensemble (B * A) :=
    fun '(lhs, rhs) => member (rhs, lhs) X
  .

  Definition Rel_compose {A : Type} {B : Type} {C : Type} (X : ensemble (A * B)) (X' : ensemble (B * C)) : ensemble (A * C) :=
    fun '(lhs, rhs) => exists x : B, member (lhs, x) X /\ member (x, rhs) X'
  .

  Global Add Parametric Morphism (A : Type) :
    (@union A) with signature (eqProp ==> eqProp ==> eqProp)
    as union_lifts_eqProp.
  Proof.
    intros X X' X_eq_X' Y Y' Y_eq_Y' z.
    do 2 rewrite in_union_iff.
    do 3 red in X_eq_X', Y_eq_Y'. now firstorder.
  Qed.

  Global Add Parametric Morphism (A : Type) :
    (@insert A) with signature (eq ==> eqProp ==> eqProp)
    as insert_lifts_eqProp.
  Proof.
    intros x X X' X_eq_X' z.
    do 2 rewrite in_insert_iff.
    do 3 red in X_eq_X'. now firstorder.
  Qed.

  Global Add Parametric Morphism (A : Type) :
    (@intersection A) with signature (eqProp ==> eqProp ==> eqProp)
    as intersection_lifts_eqProp.
  Proof.
    intros X X' X_eq_X' Y Y' Y_eq_Y' z.
    do 2 rewrite in_intersection_iff.
    do 3 red in X_eq_X', Y_eq_Y'. now firstorder.
  Qed.

(** "Ensemble Tactics" *)

  Ltac ensemble_rewrite := autorewrite with ensemble_hints using eauto.

End Ensembles.

Module E := Ensembles.

Export Ensembles.

Module MathNotations.

  Global Declare Custom Entry math_term_scope.
  Global Declare Custom Entry math_form_scope.
  Global Declare Scope math_scope.
  Global Bind Scope math_scope with Funclass Sortclass.
  Global Open Scope math_scope.

(** "Auxiliary Symbols" *)
  Global Notation " t " := t (t ident, in custom math_term_scope at level 0).
  Global Notation " '(' t ')' " := t (in custom math_term_scope at level 0, t custom math_term_scope at level 11).
  Global Notation " x '↦' t " := (fun x => t) (x pattern, in custom math_term_scope at level 11, right associativity).
  Global Notation " '⟦' t '⟧' " := t (t constr, in custom math_term_scope at level 0).
  Global Notation " P " := P (P custom math_term_scope at level 11, in custom math_form_scope at level 0).
  Global Notation " '(' P ')' " := P (in custom math_form_scope at level 0, P custom math_form_scope at level 11).
  Global Notation " '⟪' '_' '⋯' P '⟫' " := << P >> (P custom math_form_scope at level 11, in custom math_form_scope at level 0).
  Global Notation " '⟪' H_P '⋯' P '⟫' " := ⟪ H_P : P ⟫ (H_P name, P custom math_form_scope at level 11, in custom math_form_scope at level 0).
  Global Notation " '⟪' P '⟫' " := P (P custom math_form_scope at level 11, in custom math_term_scope at level 0).

(** "Terms" *)
  (* Data Constructor *)
  Global Notation " '()' " := (tt)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝐓' " := (true)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝐅' " := (false)
    (in custom math_term_scope at level 0, no associativity).
  (* Bool *)
  Global Notation " 'if' b 'then' t 'else' s 'end' " := (if b then t else s)
    (in custom math_term_scope at level 0, no associativity, format "'[v' 'if'  b '//' '[' 'then'  t ']' '//' '[' 'else'  s ']' '//' 'end' ']'").
  Global Notation " s '≟' t " := (MathProps.eq_dec s t)
    (in custom math_term_scope at level 6, no associativity).
  (* Category *)
  Global Notation " s '∘' t " := (Cat.compose s t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " 'id' " := (Cat.id)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " s '→' t " := (Cat.hom s t)
    (in custom math_term_scope at level 10, right associativity).
  Global Notation " '★' " := (Hask.t)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " 'ℍ𝕒𝕤𝕜' " := (Hask.cat)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " s '----->' t " := (Cat.Functor_t s t)
    (in custom math_term_scope at level 10, no associativity).
  Global Notation " s '=====>' t " := (Cat.isNaturalTransformation s t)
    (in custom math_term_scope at level 10, no associativity).
  (* Ensemble *)
  Global Notation " s '∪' t " := (union s t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " '⋃_{' i '∈' t  '}' s " := (unions_i (fun i : t => s))
    (i pattern, in custom math_term_scope at level 1, no associativity).
  Global Notation " '⋃' s " := (unions s)
    (in custom math_term_scope at level 1, no associativity).
  Global Notation " f '^{→}' '[' X ']' " := (image f X)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " f '^{←}' '[' X ']' " := (preimage f X)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " '\{' s ',' t ',' .. ',' u '\}' " := (finite (cons s (cons t .. (cons u nil) ..)))
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " s '∩' t " := (intersection s t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " 'Univ_{' A  '}' " := (@full A)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '∅' " := (empty)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " s '^{c}' " := (complement s)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " s '∖' t " := (setminus s t)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '\{' s '\}' " := (singleton s)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " t `Set.delete` s " := (delete t s)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " t `Set.insert` s " := (insert t s)
    (in custom math_term_scope at level 1, left associativity).

(** "Atomic Formulas" *)
  (* Setoid *)
  Global Notation " t '≡' s " := (eqProp t s)
    (t custom math_term_scope at level 6, s custom math_term_scope at level 6, in custom math_form_scope at level 7, no associativity).
  (* Poset *)
  Global Notation " t '≦' s " := (leProp t s)
    (t custom math_term_scope at level 6, s custom math_term_scope at level 6, in custom math_form_scope at level 7, no associativity).
  (* Ensemble *)
  Global Notation " t '∈' s " := (member t s)
    (t custom math_term_scope at level 6, s custom math_term_scope at level 6, in custom math_form_scope at level 7, no associativity).
  Global Notation " t '⊆' s " := (isSubsetOf t s)
    (t custom math_term_scope at level 6, s custom math_term_scope at level 6, in custom math_form_scope at level 7, no associativity).

(** "Logical Connectives" *)
  (* Propositional logic *)
  Global Notation " '⊤' " := (True)
    (in custom math_form_scope at level 0, no associativity).
  Global Notation " '⊥' " := (False)
    (in custom math_form_scope at level 0, no associativity).
  Global Notation " '¬' P " := (not P)
    (P custom math_form_scope, in custom math_form_scope at level 7, right associativity).
  Global Notation " P '∧' Q " := (and P Q)
    (P custom math_form_scope, Q custom math_form_scope, in custom math_form_scope at level 8, right associativity).
  Global Notation " P '∨' Q " := (or P Q)
    (P custom math_form_scope, Q custom math_form_scope, in custom math_form_scope at level 9, right associativity).
  Global Notation " P '⟶' Q " := (impl P Q)
    (P custom math_form_scope, Q custom math_form_scope, in custom math_form_scope at level 10, right associativity).
  Global Notation " P '⟷' Q " := (iff P Q)
    (P custom math_form_scope, Q custom math_form_scope, in custom math_form_scope at level 10, no associativity).
  (* First-order logic *)
  Global Notation " '(∀' x '∈' A ')'  '⟪' P '⟫' " := (forall x : A, P)
    (x binder, A custom math_term_scope at level 0, P custom math_form_scope at level 11, in custom math_form_scope at level 1, no associativity).
  Global Notation " '(∃' x '∈' A ')'  '⟪' P '⟫' " := (exists x : A, P)
    (x binder, A custom math_term_scope at level 0, P custom math_form_scope at level 11, in custom math_form_scope at level 1, no associativity).
  Global Notation " t '=' s " := (t = s)
    (t custom math_term_scope at level 6, s custom math_term_scope at level 6, in custom math_form_scope at level 7, no associativity).
  Global Notation " t '≠' s " := (t <> s)
    (t custom math_term_scope at level 6, s custom math_term_scope at level 6, in custom math_form_scope at level 7, no associativity).

(** "Type" *)
  Global Notation " '𝟘' " := (Empty_set)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝟙' " := (unit)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝟚' " := (bool)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " A '×' B " := (prod A B)
    (in custom math_term_scope at level 6, no associativity).
  Global Notation " A '⊔' B " := (sum A B)
    (in custom math_term_scope at level 6, no associativity).
  Global Notation " '⨆_{' x '∈' A  '}' B " := (@sigT A (fun x => B))
    (x pattern, A custom math_term_scope at level 6, B custom math_term_scope at level 1, in custom math_term_scope at level 1).
  Global Notation " '\{' x '∈' A '|' B '\}' " := (@sig A (fun x => B))
    (x pattern, A custom math_term_scope at level 6, B custom math_form_scope at level 11, in custom math_term_scope at level 0).
  Global Notation " 'ℕ' " := (nat)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝐏𝐫𝐨𝐩' " := (Prop)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝐒𝐞𝐭' " := (Set)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝐓𝐲𝐩𝐞' " := (Type)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '℘' A " := (ensemble A)
    (A constr, in custom math_term_scope at level 1, no associativity).
  Global Notation " P '->' Q " := (forall _ : P, Q)
    (P custom math_form_scope, Q custom math_form_scope, in custom math_term_scope at level 11, right associativity).

(** "Entry Points" *)
  Global Notation " '$' t '$' " := t (only printing, t custom math_term_scope at level 11, at level 0, no associativity) : math_scope.
  Global Notation " '$$' P '$$' " := P (only printing, P custom math_form_scope at level 11, at level 0, no associativity) : math_scope.

(** "MathNotations Test #1" *)
(* Check (Cat.compose (fun x : nat => x) (fun x : nat => x)). *)
(* "$ (x ↦ x) ∘ (x ↦ x) $ : $ ℕ → ℕ $" *)

(** "MathNotations Test #2" *)
(* Check (Cat.compose Cat.id (fun x : nat => x + 1)). *)
(* "$ id ∘ (x ↦ ⟦ x + 1 ⟧) $ : $ ℕ → ℕ $" *)

(** "MathNotations Test #3" *)
(* Check (fun x : nat => x + 1 = 2). *)
(* "$ x ↦ ⟪ ⟦ x + 1 ⟧ = ⟦ 2 ⟧ ⟫ $ : $ ℕ -> 𝐏𝐫𝐨𝐩 $" *)

(** "MathNotations Test #4" *)
(* Check (fun x : nat => exists y : nat, x + 1 = y + 1). *)
(* "$ x ↦ ⟪ (∃y ∈ ℕ) ⟪ ⟦ x + 1 ⟧ = ⟦ y + 1 ⟧ ⟫ ⟫ $ : $ ℕ -> 𝐏𝐫𝐨𝐩 $" *)

(** "MathNotations Test #5" *)
(* Check (fun x : nat => {y : nat | x + 1 = y + 1}). *)
(* "$ x ↦ \{ y ∈ ℕ | ⟦ x + 1 ⟧ = ⟦ y + 1 ⟧ \} $ : $ ℕ -> 𝐒𝐞𝐭 $" *)

(** "MathNotations Test #6" *)
(* Check (fun x : nat => {'(z, y) : nat * nat | x + 1 = y + 1 /\ z = 1}). *)
(* "$ x ↦ \{ (z, y) ∈ ℕ × ℕ | ⟦ x + 1 ⟧ = ⟦ y + 1 ⟧ ∧ z = ⟦ 1 ⟧ \} $ : $ ℕ -> 𝐒𝐞𝐭 $" *)

(** "MathNotations Test #7" *)
(* Check (forall x : nat, x = 1 -> x = 1). *)
(* "$$ (∀x ∈ ℕ) ⟪ x = ⟦ 1 ⟧ -> x = ⟦ 1 ⟧ ⟫ $$ : $ 𝐏𝐫𝐨𝐩 $" *)

End MathNotations.

Module MathClasses.

  Import MathProps.  

  Section AXIOMS.

  Context (S : Hask.t) {requireSetoid : isSetoid S}.

  Class Magma_axiom (bin_op : S -> S -> S) : Prop := Magma_requiresCongruence :> preserves_eqProp2 bin_op.

  Class Semigroup_axiom (add : S -> S -> S) : Prop :=
    { Semigroup_requiresMagma :> Magma_axiom add
    ; Semigroup_requiresAssoc :> Assoc add
    }
  .

  Class Monoid_axiom (add : S -> S -> S) (zero : S) : Prop :=
    { Monoid_requiresSemigroup :> Semigroup_axiom add
    ; Monoid_requiresIdElem :> zero `isIdentityOf` add
    }
  .

  Class Group_axiom (add : S -> S -> S) (zero : S) (neg : S -> S) : Prop :=
    { Group_requiresMonoid :> Monoid_axiom add zero
    ; Group_requiresInvOp :> neg `isInverseOpFor` add
    }
  .

  Global Instance neg_preserves_eqProp_inGroup {add : S -> S -> S} {zero : S} {neg : S -> S}
    (requiresGroup : Group_axiom add zero neg)
    : preserves_eqProp1 neg.
  Proof.
    ii. destruct requiresGroup as [requiresMonoid [neg_left_inv_add neg_right_inv_add]].
    rewrite <- right_id. rewrite <- neg_right_inv_add with (x := rhs1).
    assert (claim1 : add (neg lhs1) rhs1 == zero) by now rewrite <- H_EQ1.
    now rewrite associativity, claim1, left_id.
  Qed.

  End AXIOMS.

  Class Has_add (S : Hask.t) : Type := add : S -> S -> S.

  Class Has_zero (M : Hask.t) : Type := zero : M.

  Class Has_neg (G : Hask.t) : Type := neg : G -> G.

  Class Has_mul (R : Hask.t) : Type := mul : R -> R -> R.

  Class Has_unity (R : Hask.t) : Type := unity : R.

  Global Notation " x '+' y " := (add x y) (in custom math_term_scope at level 4, left associativity).
  Global Notation " '0' " := (zero) (in custom math_term_scope at level 0, no associativity).
  Global Notation " '-' x " := (neg x) (in custom math_term_scope at level 2, right associativity).
  Global Notation " x '-' y " := (add x (neg y)) (in custom math_term_scope at level 4, left associativity).
  Global Notation " x '*' y " := (mul x y) (in custom math_term_scope at level 3, left associativity).
  Global Notation " '1' " := (unity) (in custom math_term_scope at level 0, no associativity).

  Definition nonzero {K : Hask.t} {requireSetoid : isSetoid K} {requires_zero : Has_zero K} (x : K) : Prop := ~ x == zero.

  Definition zero_removed (K : Hask.t) {requireSetoid : isSetoid K} {requires_zero : Has_zero K} : Hask.t := @sig K nonzero.

  Class isSemigroup (S : Hask.t) {requireSetoid : isSetoid S} : Type :=
    { Semigroup_has_add :> Has_add S
    ; Semigroup_add_congru :> preserves_eqProp2 add
    ; Semigroup_add_assoc :> Assoc add
    }
  .

  Class isMonoid (M : Hask.t) {requireSetoid : isSetoid M} : Type :=
    { Monoid_hasSemigroup :> isSemigroup M
    ; Monoid_has_zero :> Has_zero M
    ; Monoid_zero_id_add :> zero `isIdentityOf` add
    }
  .

  Class isGroup (G : Hask.t) {requireSetoid : isSetoid G} : Type :=
    { Group_hasMonoid :> isMonoid G
    ; Group_has_neg :> Has_neg G
    ; Group_neg_inv_add :> neg `isInverseOpFor` add
    }
  .

  Class isRig (R : Hask.t) {requireSetoid : isSetoid R} : Type :=
    { Rig_hasAdditiveMonoid :> isMonoid R
    ; Rig_has_mul :> Has_mul R
    ; Rig_has_unity :> Has_unity R
    ; Rig_add_comm :> Comm add
    ; Rig_hasMultiplicateMonoid :> Monoid_axiom R mul unity
    ; Rig_mul_distr_add :> mul `distributesOver` add
    }
  .

  Class isRng (R : Hask.t) {requireSetoid : isSetoid R} : Type :=
    { Rng_hasAdditiveGroup :> isGroup R
    ; Rng_has_mul :> Has_mul R
    ; Rng_add_comm :> Comm add
    ; Rng_hasMultiplicateSemigroup :> Semigroup_axiom R mul
    ; Rng_mul_distr_add :> mul `distributesOver` add
    }
  .

  Class isRing (R : Hask.t) {requireSetoid : isSetoid R} : Type :=
    { Ring_hasRng :> isRng R
    ; Ring_has_unity :> Has_unity R
    ; Ring_unity_id_mul :> unity `isIdentityOf` mul
    }
  .

  Class isField (K : Hask.t) {requireSetoid : isSetoid K} : Type :=
    { Field_hasRing :> isRing K
    ; recip : zero_removed K -> zero_removed K
    ; Field_unity_nonzero : nonzero unity
    ; Field_absenceOfZeroDivisor
      : forall x : zero_removed K, forall y : zero_removed K, nonzero (mul (proj1_sig x) (proj1_sig y))
    ; Field_hasMultiplicateGroup :> Group_axiom (zero_removed K) (fun x : zero_removed K => fun y : zero_removed K => @exist K nonzero (mul (proj1_sig x) (proj1_sig y)) (Field_absenceOfZeroDivisor x y)) (@exist K nonzero unity Field_unity_nonzero) recip
    ; Field_mul_comm :> Comm mul
    }
  .

End MathClasses.
