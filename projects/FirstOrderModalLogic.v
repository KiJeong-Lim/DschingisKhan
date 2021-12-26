Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module FirstOrderModalLogic.

  Import ListNotations MyUtilities MyEnsemble.

  Definition ivar : Set :=
    nat
  .

  Definition ivar_eq_dec :
    forall x : ivar,
    forall y : ivar,
    {x = y} + {x <> y}.
  Proof.
    exact (fun x y => Nat.eq_dec x y).
  Defined.

  Variant logical_symbol : Set :=
  | CONTRADICTION : logical_symbol
  | NEGATION : logical_symbol
  | CONJUNCTION : logical_symbol
  | DISJUNCTION : logical_symbol
  | IMPLICATION : logical_symbol
  | BICONDITIONAL : logical_symbol 
  | FORALL : logical_symbol
  | EXISTS : logical_symbol
  | EQUAL : logical_symbol
  | BOX : logical_symbol
  | DIA : logical_symbol
  .

  Definition logical_symbol_eq_dec :
    forall s1 : logical_symbol,
    forall s2 : logical_symbol,
    {s1 = s2} + {s1 <> s2}.
  Proof.
    induction s1; destruct s2; ((left; congruence) || (right; congruence)).
  Defined.

  Inductive ty : Set :=
  | TyI : ty
  | TyO : ty
  | ARR (arg_ty : ty) (ret_ty : ty) : ty
  .

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

  Global Declare Custom Entry object_level_ty.
  Global Notation " 'i' " := (TyI) (in custom object_level_ty at level 0, no associativity).
  Global Notation " 'o' " := (TyO) (in custom object_level_ty at level 0, no associativity).
  Global Notation " ty1 '->' ty2 " := (ARR ty1 ty2) (in custom object_level_ty at level 1, right associativity).
  Global Notation " ty1 " := (ty1) (in custom object_level_ty, ty1 ident).
  Global Notation " '(' ty1 ')' " := (ty1) (in custom object_level_ty at level 0, no associativity).

  Global Declare Scope object_level_ty_scope.
  Global Notation " '\ty(' ty_expr ')' " := (ty_expr) (ty_expr custom object_level_ty at level 1, at level 0, no associativity) : object_level_ty_scope.

  Local Open Scope object_level_ty_scope.

  Definition get_ty_of_logical_symbol (s : logical_symbol) : ty :=
    match s with
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
    end
  .

  Definition arity : Set :=
    nat
  .

  Record language_signature : Set :=
    { func_arity_env : forall f_id : nat, option arity
    ; pred_arity_env : forall p_id : nat, option arity
    }
  .

  Variant symbol (lsig : language_signature) : Set :=
  | PrimSym (s : logical_symbol) : symbol lsig
  | FuncSym (fsym_id : {f_id : nat | lsig.(func_arity_env) f_id <> None}) : symbol lsig
  | PredSym (psym_id : {p_id : nat | lsig.(pred_arity_env) p_id <> None}) : symbol lsig
  .

  Arguments PrimSym {lsig}.
  Arguments FuncSym {lsig}.
  Arguments PredSym {lsig}.

  Inductive tm (lsig : language_signature) : Set :=
  | VAR (x : ivar) : tm lsig
  | CON (c : symbol lsig) : tm lsig
  | APP (t1 : tm lsig) (t2 : tm lsig) : tm lsig
  | LAM (y : ivar) (t1 : tm lsig) : tm lsig
  .

  Arguments VAR {lsig}.
  Arguments CON {lsig}.
  Arguments APP {lsig}.
  Arguments LAM {lsig}.

  Section SEMANTICS_OF_FIRST_ORDER_MODAL_LOGIC.

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

  Section SEMANTICS_OF_LOGICAL_SYMBOLS_IN_FIRST_ORDER_MODAL_LOGIC.

  Variable accessibility_relation : ensemble (Worlds * Worlds).

  Local Notation " w1 '`is_accessible_to`' w2 " := (member (w1, w2) accessibility_relation) (at level 70, no associativity) : type_scope.

  Definition interpreteW_logical (s : logical_symbol) : interpreteW_ty (get_ty_of_logical_symbol s) :=
    match s with
    | CONTRADICTION => fun _ => False
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
    end
  .

  End SEMANTICS_OF_LOGICAL_SYMBOLS_IN_FIRST_ORDER_MODAL_LOGIC.

  Variable lsig : language_signature.

  Definition get_ty_of_symbol (c : symbol lsig) : ty :=
    match c with
    | PrimSym s => get_ty_of_logical_symbol s
    | FuncSym fsym_id => nat_rec (fun _ => ty) \ty( o ) (fun _ ty1 => \ty( i -> ty1 )) (fromJust (lsig.(func_arity_env) (proj1_sig fsym_id)) (proj2_sig fsym_id))
    | PredSym psym_id => nat_rec (fun _ => ty) \ty( o ) (fun _ ty1 => \ty( i -> ty1 )) (fromJust (lsig.(pred_arity_env) (proj1_sig psym_id)) (proj2_sig psym_id))
    end
  .

  Inductive typeOf : tm lsig -> ty -> Type :=
  | VAR_typeOf (x : ivar) : typeOf (VAR x) \ty( i )
  | CON_typeOf (c : symbol lsig) : typeOf (CON c) (get_ty_of_symbol c)
  | APP_typeOf (t1 : tm lsig) (t2 : tm lsig) (ty1 : ty) (ty2 : ty) (H_typeOf_t1 : typeOf t1 \ty( ty1 -> ty2 )) (H_typeOf_t2 : typeOf t2 \ty( ty1 )) : typeOf (APP t1 t2) ty2
  | LAM_typeOf (y : ivar) (t1 : tm lsig) (ty1 : ty) (H_typeOf_t1 : typeOf t1 \ty( ty1 )) : typeOf (LAM y t1) \ty( i -> ty1 )
  .

  Definition interpreteW_func (fsym_id : {f_id : nat | lsig.(func_arity_env) f_id <> None}) :
    (Worlds -> interprete0_ty (get_ty_of_symbol (FuncSym fsym_id))) ->
    interpreteW_ty (get_ty_of_symbol (FuncSym fsym_id)).
  Proof.
    simpl.
    generalize (fromJust (lsig.(func_arity_env) (proj1_sig fsym_id)) (proj2_sig fsym_id)).
    induction a as [| a IH].
    - exact (fun val_w => val_w).
    - exact (fun fun_w arg_w => IH (fun w => fun_w w (arg_w w))).
  Defined.

  Definition interpreteW_pred (psym_id : {p_id : nat | lsig.(pred_arity_env) p_id <> None}) :
    (Worlds -> interprete0_ty (get_ty_of_symbol (PredSym psym_id))) ->
    interpreteW_ty (get_ty_of_symbol (PredSym psym_id)).
  Proof.
    simpl.
    generalize (fromJust (lsig.(pred_arity_env) (proj1_sig psym_id)) (proj2_sig psym_id)).
    induction a as [| a IH].
    - exact (fun val_w => val_w).
    - exact (fun fun_w arg_w => IH (fun w => fun_w w (arg_w w))).
  Defined.

  Variable func_env : forall fsym_id : {f_id : nat | lsig.(func_arity_env) f_id <> None}, Worlds -> interprete0_ty (get_ty_of_symbol (FuncSym fsym_id)).

  Variable pred_env : forall psym_id : {p_id : nat | lsig.(pred_arity_env) p_id <> None}, Worlds -> interprete0_ty (get_ty_of_symbol (PredSym psym_id)).

  Variable accessibility_relation : ensemble (Worlds * Worlds).

  Definition interpreteW_symbol (c : symbol lsig) : interpreteW_ty (get_ty_of_symbol c) :=
    match c with
    | PrimSym s => interpreteW_logical accessibility_relation s
    | FuncSym fsym_id => interpreteW_func fsym_id (func_env fsym_id) 
    | PredSym psym_id => interpreteW_pred psym_id (pred_env psym_id)
    end
  .

  Fixpoint interpreteW_tm (ivar_env : ivar -> wUniv) (tm_expr : tm lsig) (ty_expr : ty) (H : typeOf tm_expr ty_expr) {struct H} : interpreteW_ty ty_expr :=
    match H with
    | VAR_typeOf x => ivar_env x
    | CON_typeOf c => interpreteW_symbol c
    | APP_typeOf t1 t2 ty1 ty2 H1 H2 => (interpreteW_tm ivar_env t1 \ty( ty1 -> ty2 ) H1) (interpreteW_tm ivar_env t2 \ty( ty1 ) H2)
    | LAM_typeOf y t1 ty1 H1 => (fun y_val => interpreteW_tm (fun z => if ivar_eq_dec y z then y_val else ivar_env z) t1 \ty( ty1 ) H1)
    end
  .

  End SEMANTICS_OF_FIRST_ORDER_MODAL_LOGIC.

End FirstOrderModalLogic.
