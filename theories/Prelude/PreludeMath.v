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

  Class InvOpOf (inv : A -> A) (bin_op : A -> A -> A) : Prop :=
    { left_inv (x : A)
      : bin_op (inv x) x == x
    ; right_inv (x : A)
      : bin_op x (inv x) == x
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

  Class Countable (A : Hask.t) : Type :=
    { enum : nat -> A
    ; requiresRecursivelyEnumerable
      : forall x : A, exists n : nat, enum n = x
    }
  .

  Definition isSurjective {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) : Type :=
    forall y : B, {x : A | y = f x}
  .

  Definition isInjective {A : Hask.t} {B : Hask.t} (f : Hask.arrow A B) : Prop :=
    forall x1 : A, forall x2 : A, f x1 = f x2 -> x1 = x2
  .

  Class HasSameCardinality (A : Hask.t) (B : Hask.t) : Type :=
    { bijection : A -> B
    ; bijectionSurjective : isSurjective bijection
    ; bijectionInjective : isInjective bijection
    }
  .

  Class EqDec (A : Hask.t) : Type := eq_dec (lhs : A) (rhs : A) : {lhs = rhs} + {lhs <> rhs}.

  Global Arguments eq_dec {A} {EqDec} (lhs) (rhs) : simpl nomatch.

  Global Instance natEqDec : EqDec nat := { eq_dec := Nat.eq_dec }.

  Class ToBool (B : Hask.t) : Type := to_bool (b : B) : bool.

  Global Arguments to_bool {B} {ToBool} (b) : simpl nomatch.

  Global Instance boolToBool : ToBool bool := { to_bool := id_{ bool } }.

  Global Instance sumboolToBool (P : Prop) (Q : Prop) : ToBool ({P} + {Q}) := { to_bool := fun b : {P} + {Q} => if b then true else false }.

End MathProps.

Module E.

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

  Definition singleton {A : Hask.t} (z : A) : ensemble A := finite [z].

  Lemma in_singleton_iff {A : Hask.t} (z : A)
    : forall x : A, x \in singleton z <-> (x = z).
  Proof. intros x. unfold singleton. rewrite in_finite_iff. split; [intros [H | []] | intros []; left]; eauto. Qed.

  Definition delete {A : Hask.t} (z : A) (X : ensemble A) : ensemble A := intersection (complement (singleton z)) X.

  Lemma in_delete_iff {A : Hask.t} (z : A) (X : ensemble A)
    : forall x : A, x \in delete z X <-> (x <> z /\ x \in X).
  Proof. intros x. unfold delete. rewrite in_intersection_iff, in_complement_iff, in_singleton_iff. tauto. Qed.

  Definition insert {A : Hask.t} (z : A) (X : ensemble A) : ensemble A := union (singleton z) X.

  Lemma in_insert_iff {A : Hask.t} (z : A) (X : ensemble A)
    : forall x : A, x \in insert z X <-> (x = z \/ x \in X).
  Proof. intros x. unfold insert. rewrite in_union_iff, in_singleton_iff. tauto. Qed.

  Global Opaque union unions_i unions image preimage finite intersection full empty complement singleton delete insert.

  Local Instance Powerset_isCovariantFunctor : isCovariantFunctor ensemble :=
    { fmap {A : Hask.t} {B : Hask.t} := image (A := A) (B := B)
    }
  .

  Local Instance Powerset_isContravariantFunctor : isContravariantFunctor ensemble :=
    { contramap {B : Hask.t} {A : Hask.t} := preimage (A := A) (B := B)
    }
  .

End E.

Module MathNotations.

  Import E MathProps.

  Global Declare Scope math_scope.
  Global Declare Custom Entry math_form_entry.
  Global Declare Custom Entry math_term_entry.

(** "Auxiliary Symbols" *)
  Global Notation " '(' P ')' " := P (in custom math_form_entry at level 0, P custom math_form_entry at level 11).
  Global Notation " x '↦' P " := (fun x => P) (x as pattern, in custom math_form_entry at level 0, right associativity).
  Global Notation " P " := P (P constr, in custom math_form_entry at level 0).
  Global Notation " '(' t ')' " := t (in custom math_term_entry at level 0, t custom math_term_entry at level 11).
  Global Notation " x '↦' t " := (fun x => t) (x as pattern, in custom math_term_entry at level 0, right associativity).
  Global Notation " t " := t (t constr, in custom math_term_entry at level 0).
  Global Notation " '⟪' H '⋯' P '⟫' " := (REFERENCE_HOLDER (fun H : unit => match H with tt => P end)) (H name, P custom math_form_entry at level 11, in custom math_form_entry at level 0).

(** "Logical Connectives" *)
  (* Of propositional logic *)
  Global Notation " '⊤' " := (True)
    (in custom math_form_entry at level 0, no associativity).
  Global Notation " '⊥' " := (False)
    (in custom math_form_entry at level 0, no associativity).
  Global Notation " '¬' P " := (not P)
    (P custom math_form_entry, in custom math_form_entry at level 7, right associativity).
  Global Notation " P '∧' Q " := (and P Q)
    (P custom math_form_entry, Q custom math_form_entry, in custom math_form_entry at level 8, right associativity).
  Global Notation " P '∨' Q " := (or P Q)
    (P custom math_form_entry, Q custom math_form_entry, in custom math_form_entry at level 9, right associativity).
  Global Notation " P '⟶' Q " := (impl P Q)
    (P custom math_form_entry, Q custom math_form_entry, in custom math_form_entry at level 10, no associativity).
  Global Notation " P '⟷' Q " := (iff P Q)
    (P custom math_form_entry, Q custom math_form_entry, in custom math_form_entry at level 10, no associativity).
  Global Notation " P '->' Q " := (P -> Q)
    (P custom math_form_entry, Q custom math_form_entry, in custom math_form_entry at level 10, no associativity).
  (* Of 1st-order logic *)
  Global Notation " '(∀' x ')' P " := (forall x: _, P)
    (x as pattern, P custom math_form_entry, in custom math_form_entry at level 7, right associativity).
  Global Notation " '(∃' x ')' P " := (exists x: _, P)
    (x as pattern, P custom math_form_entry, in custom math_form_entry at level 7, right associativity).
  Global Notation " t '=' s " := (t = s)
    (t custom math_term_entry at level 6, s custom math_term_entry at level 6, in custom math_form_entry at level 7, no associativity).

(** "Atomic Formulas" *)
  (* Setoid *)
  Global Notation " t '≡' s " := (eqProp t s)
    (t custom math_term_entry at level 6, s custom math_term_entry at level 6, in custom math_form_entry at level 7, no associativity).
  (* Poset *)
  Global Notation " t '≦' s " := (leProp t s)
    (t custom math_term_entry at level 6, s custom math_term_entry at level 6, in custom math_form_entry at level 7, no associativity).
  (* Ensemble *)
  Global Notation " t '∈' s " := (member t s)
    (t custom math_term_entry at level 6, s custom math_term_entry at level 6, in custom math_form_entry at level 7, no associativity).
  Global Notation " t '⊆' s " := (isSubsetOf t s)
    (t custom math_term_entry at level 6, s custom math_term_entry at level 6, in custom math_form_entry at level 7, no associativity).

(** "Terms" *)
  (* Bool *)
  Global Notation " 'if' b 'then' t 'else' s 'end' " := (if b then t else s)
    (in custom math_term_entry at level 0, no associativity, format "'[v' 'if'  b '//' '[' 'then'  t ']' '//' '[' 'else'  s ']' '//' 'end' ']'").
  Global Notation " t '.asbool' " := (to_bool t)
    (in custom math_term_entry at level 1, left associativity).
  Global Notation " t '≟' s " := (eq_dec t s)
    (in custom math_term_entry at level 6, no associativity).
  (* Projection *)
  Global Notation " t '.unlift' " := (@proj1_sig _ _ t)
    (in custom math_term_entry at level 1, left associativity).
  Global Notation " t '.property' " := (@proj2_sig _ _ t)
    (in custom math_term_entry at level 1, left associativity).
  Global Notation " t '.fst' " := (@fst _ _ t)
    (in custom math_term_entry at level 1, left associativity).
  Global Notation " t '.snd' " := (@snd _ _ t)
    (in custom math_term_entry at level 1, left associativity).
  Global Notation " t '.1' " := (@projT1 _ _ t)
    (in custom math_term_entry at level 1, left associativity).
  Global Notation " t '.2' " := (projT2 _ _ t)
    (in custom math_term_entry at level 1, left associativity).
  (* Ensemble *)
  Global Notation " s '∪' t " := (union s t)
    (in custom math_term_entry at level 1, no associativity).
  Global Notation " '⋃_{' i  '}' s " := (unions_i (fun i => s))
    (i as pattern, in custom math_term_entry at level 1, no associativity).
  Global Notation " '⋃' s " := (unions s)
    (in custom math_term_entry at level 1, no associativity).
  Global Notation " f '^{→}' '[' X ']' " := (image f X)
    (in custom math_term_entry at level 1, left associativity).
  Global Notation " f '^{←}' '[' X ']' " := (preimage f X)
    (in custom math_term_entry at level 1, left associativity).
  Global Notation " '\{' s ',' t ',' .. ',' u '\}' " := (finite (cons s (cons t .. (cons u nil) ..)))
    (in custom math_term_entry at level 0, no associativity).
  Global Notation " s '∩' t " := (intersection s t)
    (in custom math_term_entry at level 1, no associativity).
  Global Notation " 'Univ_{' A  '}' " := (@full A)
    (in custom math_term_entry at level 0, no associativity).
  Global Notation " ∅ " := (empty)
    (in custom math_term_entry at level 0, no associativity).
  Global Notation " '{'  s '}^c' " := (complement s)
    (in custom math_term_entry at level 0, no associativity).
  Global Notation " '\{' s '\}' " := (singleton s)
    (in custom math_term_entry at level 0, no associativity).
  Global Notation " ∅ " := (empty)
    (in custom math_term_entry at level 0, no associativity).
  Global Notation " s '.delete' t " := (delete t s)
    (in custom math_term_entry at level 1, left associativity).
  Global Notation " s '.insert' t " := (insert t s)
    (in custom math_term_entry at level 1, left associativity).

(** "Entry Points" *)
  Global Notation " '$$' P '$$' " := P (P custom math_form_entry at level 11, at level 0, no associativity) : math_scope.
  Global Notation " '$' t '$' " := t (t custom math_term_entry at level 11, at level 0, no associativity) : math_scope.

End MathNotations.

Module MathClasses.

  Import MathNotations MathProps.  

  Local Open Scope program_scope.
  Local Open Scope math_scope.

  Section AXIOMS.

  Variable S : Hask.t.

  Context {requireSetoid : isSetoid S}.

  Class Magma_ax (plus : S -> S -> S) : Prop :=
    { Magma_requiresCongruence :> preserves_eqProp2 plus
    }
  .

  Class Semigroup_ax (plus : S -> S -> S) : Prop :=
    { Semigroup_requiresAssoc :> Assoc plus
    ; Semigroup_requiresMagma :> Magma_ax plus
    }
  .

  Class Monoid_ax (plus : S -> S -> S) (zero : S) : Prop :=
    { Monoid_requiresIdElem :> zero `isIdentityOf` plus
    ; Monoid_requiresSemigroup :> Semigroup_ax plus
    }
  .

  Class Group_ax (plus : S -> S -> S) (zero : S) (neg : S -> S) : Prop :=
    { Group_requiresInvOp :> neg `isInverseOpFor` plus
    ; Group_requiresMonoid :> Monoid_ax plus zero
    }
  .

  End AXIOMS.

  Section SIGNATURES.

  Class Add_sig (S : Hask.t) : Type := add : S -> S -> S.

  Class AddId_sig (M : Hask.t) : Type := zero : M.

  Class AddInv_sig (G : Hask.t) : Type := neg : G -> G.

  Class Mul_sig (R : Hask.t) : Type := mul : R -> R -> R.

  Class MulId_sig (R : Hask.t) : Type := unity : R.

  Class MulInv_sig (R : Hask.t) : Type := recip : R -> R.

  End SIGNATURES.

  Definition nonzero {K : Hask.t} {requireSetoid : isSetoid K} {requiresMonoid : AddId_sig K} (x : K) : Prop := ~ x == zero.

  Definition zero_removed (K : Hask.t) {requireSetoid : isSetoid K} {requiresMonoid : AddId_sig K} : Hask.t := @sig K nonzero.

  Class isSemigroup (S : Hask.t) {requireSetoid : isSetoid S} : Type :=
    { sigOfSemigroup :> Add_sig S
    ; axOfSemigroup :> Semigroup_ax S add
    }
  .

  Class isMonoid (M : Hask.t) {requireSetoid : isSetoid M} : Type :=
    { Monoid_hasSemigroup_asSelf :> isSemigroup M
    ; sigOfMonoid :> AddId_sig M
    ; axOfMonoid :> Monoid_ax M add zero
    }
  .

  Class isGroup (G : Hask.t) {requireSetoid : isSetoid G} : Type :=
    { Group_hasMonoid_asSelf :> isMonoid G
    ; sigOfGroup :> AddInv_sig G
    ; axOfGroup :> Group_ax G add zero neg
    }
  .

  Class isAbelianGroup (G : Hask.t) {requireSetoid : isSetoid G} : Type :=
    { AbelianGroup_isGroup :> isGroup G
    ; AbelianGroup_add_comm :> Comm add
    }
  .

  Class isRng (R : Hask.t) {requireSetoid : isSetoid R} : Type :=
    { Rng_hasAbelianGroup_asAdditivePart :> isAbelianGroup R
    ; sigOfRngMultiplicativePart :> Mul_sig R
    ; axOfRngMultiplicativePart :> Semigroup_ax R mul
    ; Rng_distr :> mul `distributesOver` add
    }
  .

  Class isRing (R : Hask.t) {requireSetoid : isSetoid R} : Type :=
    { Ring_hasRng_asSelf :> isRng R
    ; sigOfRingMultiplicativePart :> MulId_sig R
    ; axOfRingMultiplicativePart :> Monoid_ax R mul unity
    }
  .

  Class isField (K : Hask.t) {requireSetoid : isSetoid K} : Type :=
    { Field_hasRing_asSelf :> isRing K
    ; sigOfFieldMultiplicativePart :> MulInv_sig (zero_removed K)
    ; Field_unity_nonzero : nonzero unity
    ; Field_absenceOfZeroDivisor (x : zero_removed K) (y : zero_removed K) : nonzero (mul (proj1_sig x) (proj1_sig y))
    ; axOfFieldMultiplicativePart :> Group_ax (zero_removed K) (fun x : zero_removed K => fun y : zero_removed K => @exist K nonzero (mul (proj1_sig x) (proj1_sig y)) (Field_absenceOfZeroDivisor x y)) (@exist K nonzero unity Field_unity_nonzero) recip
    ; Field_mul_comm :> Comm mul
    }
  .

  Global Notation " x '+' y " := (add x y) (in custom math_term_entry at level 4, left associativity).
  Global Notation " '0' " := (zero) (in custom math_term_entry at level 0, no associativity).
  Global Notation " x '-' y " := (add x (neg y)) (in custom math_term_entry at level 4, left associativity).
  Global Notation " '-' x " := (neg x) (in custom math_term_entry at level 2, right associativity).
  Global Notation " x '*' y " := (mul x y) (in custom math_term_entry at level 3, left associativity).
  Global Notation " '1' " := (unity) (in custom math_term_entry at level 0, no associativity).

End MathClasses.
