Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module FirstOrderModalLogic.

  Import ListNotations MyUtilities MyEnsemble.

  Record language_arity_env : Set :=
    MkArityEnv
    { func_arity : forall fsym_id : nat, nat
    ; pred_arity : forall psym_id : nat, nat
    }
  .

  Definition ivar : Set :=
    nat
  .

  Variant symbol : Set :=
  | CONTRADICTION : symbol
  | NEGATION : symbol
  | CONJUNCTION : symbol
  | DISJUNCTION : symbol
  | IMPLICATION : symbol
  | BICONDITIONAL : symbol 
  | FORALL : symbol
  | EXISTS : symbol
  | EQUAL : symbol
  | BOX : symbol
  | DIA : symbol
  | FuncSym (fsym_id : nat) : symbol
  | PredSym (psym_id : nat) : symbol
  .

  Inductive tm : Set :=
  | VAR (x : ivar) : tm
  | CON (c : symbol) : tm
  | APP (t1 : tm) (t2 : tm) : tm
  | LAM (y : ivar) (t1 : tm) : tm
  .

  Inductive ty : Set :=
  | TyI : ty
  | TyO : ty
  | ARR (arg_ty : ty) (ret_ty : ty) : ty
  .

  Global Declare Custom Entry object_level_ty.

  Global Notation " 'i' " := (TyI) (in custom object_level_ty at level 0, no associativity).

  Global Notation " 'o' " := (TyO) (in custom object_level_ty at level 0, no associativity).

  Global Notation " ty1 '->' ty2 " := (ARR ty1 ty2) (in custom object_level_ty at level 1, right associativity).

  Global Notation " ty1 " := (ty1) (in custom object_level_ty, ty1 ident).

  Global Notation " '(' ty1 ')' " := (ty1) (in custom object_level_ty at level 0, no associativity).

  Global Declare Scope object_level_ty_scope.

  Global Notation " '\ty(' ty_expr ')' " := (ty_expr) (ty_expr custom object_level_ty at level 1, at level 0, no associativity) : object_level_ty_scope.

  Local Open Scope object_level_ty_scope.

  Definition ivar_eq_dec :
    forall x : ivar,
    forall y : ivar,
    {x = y} + {x <> y}.
  Proof.
    exact (fun x y => Nat.eq_dec x y).
  Defined.

  Definition ty_eq_dec :
    forall ty1 : ty,
    forall ty2 : ty,
    {ty1 = ty2} + {ty1 <> ty2}.
  Proof.
    induction ty1 as [ | | ty1_1 IH1 ty1_2 IH2]; destruct ty2 as [ | | ty2_1 ty2_2].
    - left; congruence.
    - right; congruence.
    - right; congruence.
    - right; congruence.
    - left; congruence.
    - right; congruence.
    - right; congruence.
    - right; congruence.
    - destruct (IH1 ty2_1); destruct (IH2 ty2_2).
      + left; congruence.
      + right; congruence.
      + right; congruence.
      + right; congruence.
  Defined.

  Section EVALUATION.

  Definition get_ty_of_symbol (arity_env : language_arity_env) (c : symbol) : ty :=
    match c with
    | CONTRADICTION => \ty( o )
    | NEGATION => \ty( o -> o )
    | CONJUNCTION => \ty( o -> o -> o )
    | DISJUNCTION => \ty( o -> o -> o )
    | IMPLICATION => \ty( o -> o -> o )
    | BICONDITIONAL => \ty( o -> o -> o )
    | FORALL => \ty( (i -> o) -> o )
    | EXISTS => \ty( (i -> o) -> o )
    | EQUAL => \ty( i -> i -> o )
    | BOX => \ty( o -> o )
    | DIA => \ty( o -> o )
    | FuncSym fsym_id => nat_rec (fun _ => ty) \ty( i ) (fun _ ty1 => \ty( i -> ty1 )) (arity_env.(func_arity) fsym_id)
    | PredSym psym_id => nat_rec (fun _ => ty) \ty( o ) (fun _ ty1 => \ty( i -> ty1 )) (arity_env.(pred_arity) psym_id)
    end
  .

  Variable Univ : Type.

  Fixpoint interprete0_ty (ty_expr : ty) {struct ty_expr} : Type :=
    match ty_expr with
    | \ty( i ) => Univ
    | \ty( o ) => Prop
    | \ty( arg_ty -> ret_ty ) => interprete0_ty arg_ty -> interprete0_ty ret_ty
    end
  .

  Variable Worlds : Type.

  Let wUniv : Type :=
    Worlds -> Univ
  .

  Let wProp : Type :=
    Worlds -> Prop
  .

  Fixpoint interpreteW_ty (ty_expr : ty) {struct ty_expr} : Type :=
    match ty_expr with
    | \ty( i ) => wUniv
    | \ty( o ) => wProp
    | \ty( arg_ty -> ret_ty ) => interpreteW_ty arg_ty -> interpreteW_ty ret_ty
    end
  .

  Variable arity_env : language_arity_env.

  Inductive typeOf : tm -> ty -> Type :=
  | VAR_typeOf (x : ivar) : typeOf (VAR x) \ty( i )
  | CON_typeOf (c : symbol) : typeOf (CON c) (get_ty_of_symbol arity_env c)
  | APP_typeOf (t1 : tm) (t2 : tm) (ty1 : ty) (ty2 : ty) (H_typeOf_t1 : typeOf t1 \ty( ty1 -> ty2 )) (H_typeOf_t2 : typeOf t2 \ty( ty1 )) : typeOf (APP t1 t2) ty2
  | LAM_typeOf (y : ivar) (t1 : tm) (ty1 : ty) (H_typeOf_t1 : typeOf t1 \ty( ty1 )) : typeOf (LAM y t1) \ty( i -> ty1 )
  .

  Section EVALUATION_FOR_FUNC.

  Variable interprete0_func : forall fsym_id : nat, Worlds -> interprete0_ty (get_ty_of_symbol arity_env (FuncSym fsym_id)).

  Definition interpreteW_func (fsym_id : nat) : interpreteW_ty (get_ty_of_symbol arity_env (FuncSym fsym_id)) :=
    nat_rect
    (fun arity => (Worlds -> interprete0_ty (nat_rec (fun _ => ty) \ty( i ) (fun _ ty1 => \ty( i -> ty1 )) arity)) -> interpreteW_ty (nat_rec (fun _ => ty) \ty( i ) (fun _ ty1 => \ty( i -> ty1 )) arity))
    (fun var_w => var_w)
    (fun arity IH fun_by_w arg_by_w => IH (fun w => fun_by_w w (arg_by_w w)))
    (func_arity arity_env fsym_id)
    (interprete0_func fsym_id)
  .

  End EVALUATION_FOR_FUNC.

  Section EVALUATION_FOR_PRED.

  Variable interprete0_pred : forall psym_id : nat, Worlds -> interprete0_ty (get_ty_of_symbol arity_env (PredSym psym_id)).

  Definition interpreteW_pred (psym_id : nat) : interpreteW_ty (get_ty_of_symbol arity_env (PredSym psym_id)) :=
    nat_rect
    (fun arity => (Worlds -> interprete0_ty (nat_rec (fun _ => ty) \ty( o ) (fun _ ty1 => \ty( i -> ty1 )) arity)) -> interpreteW_ty (nat_rec (fun _ => ty) \ty( o ) (fun _ ty1 => \ty( i -> ty1 )) arity))
    (fun var_w => var_w)
    (fun arity IH fun_by_w arg_by_w => IH (fun w => fun_by_w w (arg_by_w w)))
    (pred_arity arity_env psym_id)
    (interprete0_pred psym_id)
  .

  End EVALUATION_FOR_PRED.

  Variable accessibility_relation : ensemble (Worlds * Worlds).

  Local Notation " w1 '`is_accessible_to`' w2 " := (accessibility_relation (w1, w2)) (at level 70, no associativity) : type_scope.

  Variable func_env : forall fsym_id : nat, Worlds -> interprete0_ty (get_ty_of_symbol arity_env (FuncSym fsym_id)).

  Variable pred_env : forall psym_id : nat, Worlds -> interprete0_ty (get_ty_of_symbol arity_env (PredSym psym_id)).

  Definition interpreteW_symbol (c : symbol) : interpreteW_ty (get_ty_of_symbol arity_env c) :=
    match c with
    | CONTRADICTION => fun w => False
    | NEGATION => fun wP1 w => ~ wP1 w
    | CONJUNCTION => fun wP1 wP2 w => wP1 w /\ wP2 w
    | DISJUNCTION => fun wP1 wP2 w => wP1 w \/ wP2 w
    | IMPLICATION => fun wP1 wP2 w => wP1 w -> wP2 w
    | BICONDITIONAL => fun wP1 wP2 w => wP1 w <-> wP2 w
    | FORALL => fun wP1' w => forall y_val : wUniv, wP1' y_val w
    | EXISTS => fun wP1' w => exists y_val : wUniv, wP1' y_val w
    | EQUAL => fun x_val y_val w => x_val w = y_val w
    | BOX => fun wP1 w => forall w' : Worlds, w `is_accessible_to` w' -> wP1 w'
    | DIA => fun wP1 w => exists w' : Worlds, w `is_accessible_to` w' /\ wP1 w'
    | FuncSym fsym_id => interpreteW_func func_env fsym_id
    | PredSym psym_id => interpreteW_pred pred_env psym_id
    end
  .

  Fixpoint interpreteW_tm (ivar_env : ivar -> wUniv) (tm_expr : tm) (ty_expr : ty) (H : typeOf tm_expr ty_expr) {struct H} : interpreteW_ty ty_expr :=
    match H with
    | VAR_typeOf x => ivar_env x
    | CON_typeOf c => interpreteW_symbol c
    | APP_typeOf t1 t2 ty1 ty2 H1 H2 => (interpreteW_tm ivar_env t1 \ty( ty1 -> ty2 ) H1) (interpreteW_tm ivar_env t2 \ty( ty1 ) H2)
    | LAM_typeOf y t1 ty1 H1 => (fun y_val => interpreteW_tm (fun z => if ivar_eq_dec y z then y_val else ivar_env z) t1 \ty( ty1 ) H1)
    end
  .

  End EVALUATION.

End FirstOrderModalLogic.
