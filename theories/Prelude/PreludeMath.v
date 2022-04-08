Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.

Module MathProps.

  Local Open Scope program_scope.

  Class preserves_eqProp1 {dom : Hask.t} {cod : Hask.t} {dom_isSetoid : isSetoid dom} {cod_isSetoid : isSetoid cod} (unary_op : dom -> cod) : Prop :=
    eqProp_lifted1 (lhs1 : dom) (rhs1 : dom)
    (H_EQ1 : lhs1 == rhs1)
    : unary_op lhs1 == unary_op rhs1
  .

  Global Add Parametric Morphism {dom : Hask.t} {cod : Hask.t} {dom_isSetoid : isSetoid dom} {cod_isSetoid : isSetoid cod} (unary_op : dom -> cod) {preserves_eqProp : preserves_eqProp1 unary_op} :
    unary_op with signature (eqProp ==> eqProp)
    as congruence_if_eqProp_lifted1.
  Proof. intros x1 x2 H_x_eq; exact (eqProp_lifted1 x1 x2 H_x_eq). Defined.

  Class preserves_eqProp2 {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isSetoid : isSetoid dom1} {dom2_isSetoid : isSetoid dom2} {cod_isSetoid : isSetoid cod} (binary_op : dom1 -> dom2 -> cod) : Prop :=
    eqProp_lifted2 (lhs1 : dom1) (rhs1 : dom1) (lhs2 : dom2) (rhs2 : dom2)
    (H_EQ1 : lhs1 == rhs1)
    (H_EQ2 : lhs2 == rhs2)
    : binary_op lhs1 lhs2 == binary_op rhs1 rhs2
  .

  Global Add Parametric Morphism {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isSetoid : isSetoid dom1} {dom2_isSetoid : isSetoid dom2} {cod_isSetoid : isSetoid cod} (binary_op : dom1 -> dom2 -> cod) {preserves_eqProp : preserves_eqProp2 binary_op} :
    binary_op with signature (eqProp ==> eqProp ==> eqProp)
    as congruence_if_eqProp_lifted2.
  Proof. intros x1 x2 H_x_eq y1 y2 H_y_eq; exact (eqProp_lifted2 x1 x2 y1 y2 H_x_eq H_y_eq). Defined.

  Class preserves_leProp1 {dom : Hask.t} {cod : Hask.t} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (unary_op : dom -> cod) : Prop :=
    leProp_lifted1 (lhs1 : dom) (rhs1 : dom)
    (H_LE1 : lhs1 =< rhs1)
    : unary_op lhs1 =< unary_op rhs1
  .

  Global Add Parametric Morphism {dom : Hask.t} {cod : Hask.t} {dom_isPoset : isPoset dom} {cod_isPoset : isPoset cod} (unary_op : dom -> cod) {preserves_leProp : preserves_leProp1 unary_op} :
    unary_op with signature (leProp ==> leProp)
    as monotonic_if_eqProp_lifted1.
  Proof. intros x1 x2 H_x_le; exact (leProp_lifted1 x1 x2 H_x_le). Defined.

  Class preserves_leProp2 {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isPoset : isPoset dom1} {dom2_isPoset : isPoset dom2} {cod_isSetoid : isPoset cod} (binary_op : dom1 -> dom2 -> cod) : Prop :=
    leProp_lifted2 (lhs1 : dom1) (rhs1 : dom1) (lhs2 : dom2) (rhs2 : dom2)
    (H_LE1 : lhs1 =< rhs1)
    (H_LE2 : lhs2 =< rhs2)
    : binary_op lhs1 lhs2 =< binary_op rhs1 rhs2
  .

  Global Add Parametric Morphism {dom1 : Hask.t} {dom2 : Hask.t} {cod : Hask.t} {dom1_isPoset : isPoset dom1} {dom2_isPoset : isPoset dom2} {cod_isSetoid : isPoset cod} (binary_op : dom1 -> dom2 -> cod) {preserves_leProp : preserves_leProp2 binary_op} :
    binary_op with signature (leProp ==> leProp ==> leProp)
    as monotonic_if_eqProp_lifted2.
  Proof. intros x1 x2 H_x_le y1 y2 H_y_le; exact (leProp_lifted2 x1 x2 y1 y2 H_x_le H_y_le). Defined.

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

  End STATEMENTS_FOR_OPERATION_PROPERTIES.

  Global Infix " `distributesOver` " := Distr (at level 70, no associativity) : type_scope.
  Global Infix " `isIdentityOf` " := IdElemOf (at level 70, no associativity) : type_scope.
  Global Infix " `isInverseOpFor` " := InvOpOf (at level 70, no associativity) : type_scope.

  Definition isInjective {dom : Hask.t} {cod : Hask.t} (f : Hask.arrow dom cod) : Prop :=
    forall x1 : dom, forall x2 : dom, ⟪ f_x1_eq_f_x2 : f x1 = f x2 ⟫ -> ⟪ x1_eq_x2 : x1 = x2 ⟫
  .

  Definition isSurjective {dom : Hask.t} {cod : Hask.t} (f : Hask.arrow dom cod) : Type :=
    forall y : cod, {x : dom | ⟪ y_is_f_x : y = f x ⟫}
  .

  Class HasSameCardinality (dom : Hask.t) (cod : Hask.t) : Type :=
    { bijection : dom -> cod
    ; bijectionInjective : isInjective bijection
    ; bijectionSurjective : isSurjective bijection
    }
  .

  Class Countable (dom : Hask.t) : Type :=
    { enum : nat -> dom
    ; requiresRecursivelyEnumerable : isSurjective enum
    }
  .

  Definition isDecidable {X : Hask.t} (Y : ensemble X) : Type :=
    forall y : X, {member y Y} + {~ member y Y}
  .

  Class EqDec (dom : Hask.t) : Type := eq_dec (x : dom) : isDecidable (@eq dom x).

  Global Arguments eq_dec {dom} {EqDec} (x) (y) : simpl nomatch.

  Global Instance natEqDec : EqDec nat := { eq_dec := Nat.eq_dec }.

  Class ToBool (B : Hask.t) : Type := to_bool (b : B) : bool.

  Global Arguments to_bool {B} {ToBool} (b) : simpl nomatch.

  Global Instance boolToBool : ToBool bool := { to_bool := id_{ bool } }.

  Global Instance sumboolToBool (P : Prop) (Q : Prop) : ToBool ({P} + {Q}) := { to_bool := fun b : {P} + {Q} => if b then true else false }.

End MathProps.

Module Ensembles.

  Import ListNotations.

  Local Open Scope program_scope.

  Inductive _union {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) (x : A) : Prop :=
  | In_union_l
    (x_in_Xl : member x Xl)
    : member x (_union Xl Xr)
  | In_union_r
    (x_in_Xr : member x Xr)
    : member x (_union Xl Xr)
  .

  Inductive _unions_i {A : Hask.t} {I : Hask.t} (Xs : Hask.arrow I (ensemble A)) (x : A) : Prop :=
  | In_unions_i (i : I)
    (x_in_Xs_i : member x (Xs i))
    : member x (_unions_i Xs)
  .

  Inductive _unions {A : Hask.t} (Xs : ensemble (ensemble A)) (x : A) : Prop :=
  | In_unions (X : ensemble A)
    (x_in_X : member x X)
    (X_in_Xs : member X Xs)
    : member x (_unions Xs)
  .

  Inductive _image {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (X : ensemble A) (y : B) : Prop :=
  | In_image (x : A)
    (x_in_X : member x X)
    (y_eq_f_x : y = f x)
    : member y (_image f X)
  .

  Inductive _preimage {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (Y : ensemble B) (x : A) : Prop :=
  | In_preimage
    (f_x_in_Y : member (f x) Y)
    : member x (_preimage f Y)
  .

  Inductive _finite {A : Hask.t} (xs : list A) (x : A) : Prop :=
  | In_finite
    (x_in_xs : In x xs)
    : member x (_finite xs)
  .

  Inductive _intersection {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) (x : A) : Prop :=
  | In_intersection
    (x_in_Xl : member x Xl)
    (x_in_Xr : member x Xr)
    : member x (_intersection Xl Xr)
  .

  Inductive _full {A : Hask.t} (x : A) : Prop :=
  | In_full
    : member x (_full)
  .

  Inductive _empty {A : Hask.t} (x : A) : Prop :=
  .

  Local Hint Constructors _union _unions_i _unions _image _preimage _finite _intersection _full _empty : core.

  Global Infix " \in " := member (at level 70, no associativity) : type_scope.

  Definition union {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) : ensemble A := _union Xl Xr.

  Lemma in_union_iff {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A)
    : forall x : A, x \in union Xl Xr <-> (x \in Xl \/ x \in Xr).
  Proof. intros x; split; intros [H_l | H_r]; eauto. Qed.

  Definition unions_i {A : Hask.t} {I : Hask.t} (Xs : Hask.arrow I (ensemble A)) : ensemble A := _unions_i Xs.

  Lemma in_unions_i_iff {A : Hask.t} {I : Hask.t} (Xs : Hask.arrow I (ensemble A))
    : forall x : A, x \in unions_i Xs <-> (exists i : I, x \in Xs i).
  Proof. intros x; split; intros [i H_i]; eauto. Qed.

  Definition unions {A : Hask.t} (Xs : ensemble (ensemble A)) : ensemble A := _unions Xs.

  Lemma in_unions_iff {A : Hask.t} (Xs : ensemble (ensemble A))
    : forall x : A, x \in unions Xs <-> (exists X : ensemble A, x \in X /\ X \in Xs).
  Proof. intros x; split; [intros [X H_X H_Xs] | intros [X [H_X H_Xs]]]; eauto. Qed.

  Definition image {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (X : ensemble A) : ensemble B := _image f X.

  Lemma in_image_iff {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (X : ensemble A)
    : forall y : B, y \in image f X <-> (exists x : A, y = f x /\ x \in X).
  Proof. intros y; split; [intros [x H_x H_y] | intros [x [H_x H_y]]]; eauto. Qed.

  Definition preimage {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (Y : ensemble B) : ensemble A := _preimage f Y.

  Lemma in_preimage_iff {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) (Y : ensemble B)
    : forall x : A, x \in preimage f Y <-> (exists y : B, y = f x /\ y \in Y).
  Proof. intros y; split; [intros [H_x] | intros [x [H_x H_y]]; subst]; eauto. Qed.

  Definition finite {A : Hask.t} (xs : list A) : ensemble A := _finite xs.

  Lemma in_finite_iff {A : Hask.t} (xs : list A)
    : forall x : A, x \in finite xs <-> (In x xs).
  Proof. intros x; split; [intros [H_x] | intros H_x]; eauto. Qed.

  Definition intersection {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A) : ensemble A := _intersection Xl Xr.

  Lemma in_intersection_iff {A : Hask.t} (Xl : ensemble A) (Xr : ensemble A)
    : forall x : A, x \in intersection Xl Xr <-> (x \in Xl /\ x \in Xr).
  Proof. intros x; split; intros [H_l H_r]; eauto. Qed.

  Definition full {A : Hask.t} : ensemble A := _full.

  Lemma in_full_iff {A : Hask.t}
    : forall x : A, x \in full <-> (True).
  Proof. intros x; split; eauto. Qed.

  Definition empty {A : Hask.t} : ensemble A := _empty.

  Lemma in_empty_iff {A : Hask.t}
    : forall x : A, x \in empty <-> (False).
  Proof. intros x; split; intros []. Qed.

  Definition complement {A : Hask.t} (X : ensemble A) : ensemble A := fun x : A => ~ x \in X.

  Lemma in_complement_iff {A : Hask.t} (X : ensemble A)
    : forall x : A, x \in complement X <-> (~ x \in X).
  Proof. reflexivity. Qed.

  Definition setminus {A : Hask.t} (X1 : ensemble A) (X2 : ensemble A) : ensemble A := intersection X1 (complement X2).

  Lemma in_setminus_iff {A : Hask.t} (X1 : ensemble A) (X2 : ensemble A)
    : forall x : A, x \in setminus X1 X2 <-> (x \in X1 /\ ~ x \in X2).
  Proof. intros x. unfold setminus. rewrite in_intersection_iff, in_complement_iff. tauto. Qed.

  Definition singleton {A : Hask.t} (z : A) : ensemble A := finite [z].

  Lemma in_singleton_iff {A : Hask.t} (z : A)
    : forall x : A, x \in singleton z <-> (x = z).
  Proof. intros x. unfold singleton. rewrite in_finite_iff. split; [intros [H | []] | intros []; left]; eauto. Qed.

  Definition delete {A : Hask.t} (z : A) (X : ensemble A) : ensemble A := setminus X (singleton z).

  Lemma in_delete_iff {A : Hask.t} (z : A) (X : ensemble A)
    : forall x : A, x \in delete z X <-> (x <> z /\ x \in X).
  Proof. intros x. unfold delete. rewrite in_setminus_iff, in_singleton_iff. tauto. Qed.

  Definition insert {A : Hask.t} (z : A) (X : ensemble A) : ensemble A := union (singleton z) X.

  Lemma in_insert_iff {A : Hask.t} (z : A) (X : ensemble A)
    : forall x : A, x \in insert z X <-> (x = z \/ x \in X).
  Proof. intros x. unfold insert. rewrite in_union_iff, in_singleton_iff. tauto. Qed.

  Global Opaque union unions_i unions image preimage finite intersection full empty complement setminus singleton delete insert.

  Local Instance Powerset_isCovariantFunctor : isCovariantFunctor ensemble :=
    { fmap {A : Hask.t} {B : Hask.t} := image (A := A) (B := B)
    }
  .

  Local Instance Powerset_isContravariantFunctor : isContravariantFunctor ensemble :=
    { contramap {B : Hask.t} {A : Hask.t} := preimage (A := A) (B := B)
    }
  .

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
  Global Notation " x '↦' t " := (fun x => t) (x as pattern, in custom math_term_scope at level 11, right associativity).
  Global Notation " '⟦' t '⟧' " := t (t constr, in custom math_term_scope at level 0).
  Global Notation " P " := P (P custom math_term_scope at level 11, in custom math_form_scope at level 0).
  Global Notation " '(' P ')' " := P (in custom math_form_scope at level 0, P custom math_form_scope at level 11).
  Global Notation " '⟪' '_' '⋯' P '⟫' " := ⟪ P ⟫ (P custom math_form_scope at level 11, in custom math_form_scope at level 0).
  Global Notation " '⟪' H '⋯' P '⟫' " := << H : P >> (H name, P custom math_form_scope at level 11, in custom math_form_scope at level 0).

(** "Terms" *)
  (* Type *)
  Global Notation " 'ℕ' " := (nat)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝟘' " := (Empty_set)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝟙' " := (unit)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝟚' " := (bool)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " 'Prop' " := (Prop)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " 'Set' " := (Set)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " 'Type' " := (Type)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " '𝕋𝕪𝕡𝕖' " := (Hask.t)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " 'ℍ𝕒𝕤𝕜' " := (Hask.cat)
    (in custom math_term_scope at level 0, no associativity).
  (* Bool *)
  Global Notation " 'if' b 'then' t 'else' s 'end' " := (if b then t else s)
    (in custom math_term_scope at level 0, no associativity, format "'[v' 'if'  b '//' '[' 'then'  t ']' '//' '[' 'else'  s ']' '//' 'end' ']'").
  Global Notation " t '.asbool' " := (MathProps.to_bool t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " t '≟' s " := (MathProps.eq_dec t s)
    (in custom math_term_scope at level 6, no associativity).
  (* Category *)
  Global Notation " t '∘' s " := (Cat.compose t s)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " 'id' " := (Cat.id)
    (in custom math_term_scope at level 0, no associativity).
  Global Notation " t '→' s " := (Cat.hom t s)
    (in custom math_term_scope at level 10, right associativity).
  Global Notation " t '⟹' s " := (Cat.isNaturalTransformation t s)
    (in custom math_term_scope at level 10, right associativity).
  (* Projection *)
  Global Notation " t '.unlift' " := (@proj1_sig _ _ t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " t '.property' " := (@proj2_sig _ _ t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " t '.fst' " := (@fst _ _ t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " t '.snd' " := (@snd _ _ t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " t '.1' " := (@projT1 _ _ t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " t '.2' " := (projT2 _ _ t)
    (in custom math_term_scope at level 1, left associativity).
  (* Ensemble *)
  Global Notation " s '∪' t " := (union s t)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " '⋃_{' i  '}' s " := (unions_i (fun i => s))
    (i as pattern, in custom math_term_scope at level 1, no associativity).
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
  Global Notation " s '.delete' t " := (delete t s)
    (in custom math_term_scope at level 1, left associativity).
  Global Notation " s '.insert' t " := (insert t s)
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
    (P custom math_form_scope, Q custom math_form_scope, in custom math_form_scope at level 10, no associativity).
  Global Notation " P '⟷' Q " := (iff P Q)
    (P custom math_form_scope, Q custom math_form_scope, in custom math_form_scope at level 10, no associativity).
  Global Notation " P '->' Q " := (P -> Q)
    (P custom math_form_scope, Q custom math_form_scope, in custom math_form_scope at level 10, no associativity).
  (* First-order logic *)
  Global Notation " '(∀' x ')' P " := (forall x: _, P)
    (x as pattern, P custom math_form_scope, in custom math_form_scope at level 7, right associativity).
  Global Notation " '(∃' x ')' P " := (exists x: _, P)
    (x as pattern, P custom math_form_scope, in custom math_form_scope at level 7, right associativity).
  Global Notation " t '=' s " := (t = s)
    (t custom math_term_scope at level 6, s custom math_term_scope at level 6, in custom math_form_scope at level 7, no associativity).

(** "Entry Points" *)
  Global Notation " '$' t '$' " := t (t custom math_term_scope at level 11, at level 0, no associativity, only printing) : math_scope.
  Global Notation " '$$' P '$$' " := P (P custom math_form_scope at level 11, at level 0, no associativity, only printing) : math_scope.

(* Notation Test #1 *)
(* Check (Cat.compose (fun x : nat => x) (fun x : nat => x)). *)
(* "$ (x ↦ x) ∘ (x ↦ x) $ : $ ℕ → ℕ $" *)

(* Notation Test #2 *)
(* Check (Cat.compose Cat.id (fun x : nat => x + 1)). *)
(* "$ id ∘ (x ↦ ⟦ x + 1 ⟧) $ : $ ℕ → ℕ $" *)

(* Notation Test #3 *)
(* Check (fun x : nat => x + 1 = 2). *)
(* "$ x ↦ ⟦ $$ ⟦ x + 1 ⟧ = ⟦ 2 ⟧ $$ ⟧ $ : $$ ℕ -> Prop $$" *)

End MathNotations.

Module MathClasses.

  Import MathProps.  

  Local Open Scope program_scope.

  Section AXIOMS.

  Context (S : Hask.t) {requireSetoid : isSetoid S}.

  Class Magma_axiom (plus : S -> S -> S) : Prop := Magma_requiresCongruence :> preserves_eqProp2 plus.

  Class Semigroup_axiom (plus : S -> S -> S) : Prop :=
    { Semigroup_requiresMagma :> Magma_axiom plus
    ; Semigroup_requiresAssoc :> Assoc plus
    }
  .

  Class Monoid_axiom (plus : S -> S -> S) (zero : S) : Prop :=
    { Monoid_requiresSemigroup :> Semigroup_axiom plus
    ; Monoid_requiresIdElem :> zero `isIdentityOf` plus
    }
  .

  Class Group_axiom (plus : S -> S -> S) (zero : S) (neg : S -> S) : Prop :=
    { Group_requiresMonoid :> Monoid_axiom plus zero
    ; Group_requiresInvOp :> neg `isInverseOpFor` plus
    }
  .

  Global Instance neg_preserves_eqProp_inGroup (plus : S -> S -> S) (zero : S) (neg : S -> S)
    (requiresGroup : Group_axiom plus zero neg)
    : preserves_eqProp1 neg.
  Proof.
    ii. destruct requiresGroup as [requiresMonoid [neg_left_inv_plus neg_right_inv_plus]].
    rewrite <- right_id. rewrite <- neg_right_inv_plus with (x := rhs1).
    assert (claim1 : plus (neg lhs1) rhs1 == zero) by now rewrite <- H_EQ1.
    now rewrite Semigroup_requiresAssoc, claim1, left_id.
  Qed.

  End AXIOMS.

  Class Has_add (S : Hask.t) : Type := add : S -> S -> S.

  Class Has_zero (M : Hask.t) : Type := zero : M.

  Class Has_neg (G : Hask.t) : Type := neg : G -> G.

  Class Has_mul (R : Hask.t) : Type := mul : R -> R -> R.

  Class Has_unity (R : Hask.t) : Type := unity : R.

  Class Has_recip (K : Hask.t) : Type := recip : K -> K.

  Global Notation " x '+' y " := (add x y) (in custom math_term_scope at level 4, left associativity).
  Global Notation " '0' " := (zero) (in custom math_term_scope at level 0, no associativity).
  Global Notation " x '-' y " := (add x (neg y)) (in custom math_term_scope at level 4, left associativity).
  Global Notation " '-' x " := (neg x) (in custom math_term_scope at level 2, right associativity).
  Global Notation " x '*' y " := (mul x y) (in custom math_term_scope at level 3, left associativity).
  Global Notation " '1' " := (unity) (in custom math_term_scope at level 0, no associativity).

  Definition nonzero {K : Hask.t} {requireSetoid : isSetoid K} {requires_zero : Has_zero K} (x : K) : Prop := ~ x == zero.

  Definition zero_removed (K : Hask.t) {requireSetoid : isSetoid K} {requires_zero : Has_zero K} : Hask.t := @sig K nonzero.

  Class isSemigroup (S : Hask.t) {requireSetoid : isSetoid S} : Type :=
    { Semigroup_has_add :> Has_add S
    ; Semigroup_add_assoc :> Semigroup_axiom S add
    }
  .

  Class isMonoid (M : Hask.t) {requireSetoid : isSetoid M} : Type :=
    { Monoid_hasSemigroup :> isSemigroup M
    ; Monoid_has_zero :> Has_zero M
    ; Monoid_zero_id_add :> Monoid_axiom M add zero
    }
  .

  Class isGroup (G : Hask.t) {requireSetoid : isSetoid G} : Type :=
    { Group_hasMonoid :> isMonoid G
    ; Group_has_neg :> Has_neg G
    ; Group_neg_inv_add :> Group_axiom G add zero neg
    }
  .

  Class isRig (R : Hask.t) {requireSetoid : isSetoid R} : Type :=
    { Rig_hasMonoid :> isMonoid R
    ; Rig_has_mul :> Has_mul R
    ; Rig_has_unity :> Has_unity R
    ; Rig_add_comm :> Comm add
    ; Rig_unity_id_mul :> Monoid_axiom R mul unity
    ; Rig_mul_distr_add :> mul `distributesOver` add
    }
  .

  Class isRng (R : Hask.t) {requireSetoid : isSetoid R} : Type :=
    { Rng_hasGroup :> isGroup R
    ; Rng_has_mul :> Has_mul R
    ; Rng_add_comm :> Comm add
    ; Rng_mul_assoc :> Semigroup_axiom R mul
    ; Rng_mul_distr_add :> mul `distributesOver` add
    }
  .

  Class isRing (R : Hask.t) {requireSetoid : isSetoid R} : Type :=
    { Ring_hasRng :> isRng R
    ; Ring_has_unity :> Has_unity R
    ; Ring_unity_id_mul :> Monoid_axiom R mul unity
    }
  .

  Class isField (K : Hask.t) {requireSetoid : isSetoid K} : Type :=
    { Field_hasRing :> isRing K
    ; Field_has_recip :> Has_recip (zero_removed K)
    ; Field_unity_nonzero : nonzero unity
    ; Field_absenceOfZeroDivisor (x : zero_removed K) (y : zero_removed K) : nonzero (mul (proj1_sig x) (proj1_sig y))
    ; Field_recip_inv_mul :> Group_axiom (zero_removed K) (fun x : zero_removed K => fun y : zero_removed K => @exist K nonzero (mul (proj1_sig x) (proj1_sig y)) (Field_absenceOfZeroDivisor x y)) (@exist K nonzero unity Field_unity_nonzero) recip
    ; Field_mul_comm :> Comm mul
    }
  .

End MathClasses.
