Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module FirstOrderModalLogicSyntax.

  Import ListNotations MyUtilities MyEnsemble.

  Record first_order_modal_language : Set :=
    FOML
    { func_arity : forall f_id : nat, nat
    ; pred_arity : forall p_id : nat, nat
    }
  .

  Definition ivar : Set :=
    nat
  .

  Variant ctor : Set :=
  | CONTRADICTION : ctor
  | NEGATION : ctor
  | CONJUNCTION : ctor
  | DISJUNCTION : ctor
  | IMPLICATION : ctor
  | BICONDITIONAL : ctor 
  | FORALL : ctor
  | EXISTS : ctor
  | EQUAL : ctor
  | BOX : ctor
  | DIA : ctor
  | FuncSym : forall f_id : nat, ctor
  | PredSym : forall p_id : nat, ctor
  .

  Inductive tm : Set :=
  | VAR : forall x : ivar, tm
  | CON : forall c : ctor, tm
  | APP : forall t1 : tm, forall t2 : tm, tm
  | LAM : forall y : ivar, forall t1 : tm, tm
  .

  Inductive ty : Set :=
  | TyI : ty
  | TyO : ty
  | ARR : forall arg_ty : ty, forall ret_ty : ty, ty
  .

  Definition ivar_eq_dec :
    forall x : ivar,
    forall y : ivar,
    {x = y} + {x <> y}.
  Proof.
    exact (Nat.eq_dec).
  Defined.

  Definition ty_eq_dec :
    forall ty1 : ty,
    forall ty2 : ty,
    {ty1 = ty2} + {ty1 <> ty2}.
  Proof.
    induction ty1; destruct ty2.
    - left; congruence.
    - right; congruence.
    - right; congruence.
    - right; congruence.
    - left; congruence.
    - right; congruence.
    - right; congruence.
    - right; congruence.
    - destruct (IHty1_1 ty2_1); destruct (IHty1_2 ty2_2).
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

  Definition view_ty (ty_expr : ty) : ty :=
    ty_expr
  .

  Global Declare Scope object_level_ty_scope.

  Global Notation " 'Ty<' ty_expr '>' " := (view_ty ty_expr) (ty_expr custom object_level_ty at level 1, no associativity) : object_level_ty_scope.

  Section WELL_FORMED.

  Local Open Scope object_level_ty_scope.

  Variable lang : first_order_modal_language.

  Definition get_ty_of_ctor : ctor -> ty :=
    fun c : ctor =>
    match c with
    | CONTRADICTION => Ty< o >
    | NEGATION => Ty< o -> o >
    | CONJUNCTION => Ty< o -> o -> o >
    | DISJUNCTION => Ty< o -> o -> o >
    | IMPLICATION => Ty< o -> o -> o >
    | BICONDITIONAL => Ty< o -> o -> o >
    | FORALL => Ty< (i -> o) -> o >
    | EXISTS => Ty< (i -> o) -> o >
    | EQUAL => Ty< i -> i -> o >
    | BOX => Ty< o -> o >
    | DIA => Ty< o -> o >
    | FuncSym f_id => nat_rec _ (Ty< i >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(func_arity) f_id)
    | PredSym p_id => nat_rec _ (Ty< o >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(pred_arity) p_id) 
    end
  .

  Definition bindMaybe {A : Type} {B : Type} : option A -> (A -> option B) -> option B :=
    fun option_A : option A =>
    fun A_to_option_B : A -> option B =>
    match option_A with
    | None => None
    | Some a => A_to_option_B a
    end
  .

  Definition pureMaybe {A : Type} : A -> option A :=
    Some
  .

  Definition lookup (x : ivar) : list (ivar * ty) -> option ty :=
    fix lookup_fix (ty_ctx : list (ivar * ty)) : option ty :=
    match ty_ctx with
    | [] => None
    | ty_ctx_item :: ty_ctx' =>
      if ivar_eq_dec (fst ty_ctx_item) x
      then Some (snd ty_ctx_item)
      else lookup_fix ty_ctx'
    end
  .

  Definition modus_ponens : ty -> ty -> option ty :=
    fun ty1 : ty =>
    fun ty2 : ty =>
    match ty1 with
    | TyI => None
    | TyO => None
    | ARR arg_ty ret_ty =>
      if ty_eq_dec arg_ty ty2
      then Some ret_ty
      else None
    end
  .

  Fixpoint typing (ty_ctx : list (ivar * ty)) (t : tm) {struct t} : option ty :=
    match t with
    | VAR x => lookup x ty_ctx
    | CON c => pureMaybe (get_ty_of_ctor c)
    | APP t1 t2 => bindMaybe (typing ty_ctx t1) (fun ty1 : ty => bindMaybe (typing ty_ctx t2) (fun ty2 : ty => modus_ponens ty1 ty2))
    | LAM y t1 => typing ((y, Ty< i >) :: ty_ctx) t1
    end
  .

  End WELL_FORMED.

  Global Notation " ty_ctx '\vdash_{' lang  '}' tm_expr '\isof' ty_expr " := (typing lang ty_ctx tm_expr = Some ty_expr) (at level 70, no associativity) : type_scope.

End FirstOrderModalLogicSyntax.

Module FirstOrderModalLogicSemantics.

  Import MyEnsemble FirstOrderModalLogicSyntax.

  Local Open Scope object_level_ty_scope.

  Section EVALUATION.

  Variable Univ : Type.

  Definition interprete_ty : ty -> Type :=
    fix interprete_ty_fix (ty_expr : ty) {struct ty_expr} : Type :=
    match ty_expr with
    | TyI => Univ
    | TyO => Prop
    | ARR arg_ty ret_ty => interprete_ty_fix arg_ty -> interprete_ty_fix ret_ty
    end
  .

  Variable Worlds : Type.

  Let wUniv : Type :=
    Worlds -> Univ
  .

  Let wProp : Type :=
    Worlds -> Prop
  .

  Definition interpretew_ty : ty -> Type :=
    fix interpretew_ty_fix (ty_expr : ty) {struct ty_expr} : Type :=
    match ty_expr with
    | TyI => wUniv
    | TyO => wProp
    | ARR arg_ty ret_ty => interpretew_ty_fix arg_ty -> interpretew_ty_fix ret_ty
    end
  .

  Variable lang : first_order_modal_language.

  Inductive typeOf : tm -> ty -> Type :=
  | VAR_wt :
    forall x : ivar,
    typeOf (VAR x) (Ty< i >)
  | CON_wt :
    forall c : ctor,
    typeOf (CON c) (get_ty_of_ctor lang c)
  | APP_wt :
    forall t1 : tm,
    forall t2 : tm,
    forall ty1 : ty,
    forall ty2 : ty,
    typeOf t1 (Ty< ty1 -> ty2 >) ->
    typeOf t2 ty1 ->
    typeOf (APP t1 t2) ty2
  | LAM_wt :
    forall y : ivar,
    forall t1 : tm,
    forall ty1 : ty,
    typeOf t1 ty1 ->
    typeOf (LAM y t1) (Ty< i -> ty1 >)
  .

  Section EVALUATION_FOR_FUNC.

  Variable interprete_func : forall f_id : nat, Worlds -> interprete_ty (nat_rec _ (Ty< i >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(func_arity) f_id)).

  Definition interpretew_func :
    forall f_id : nat,
    interpretew_ty (nat_rec _ (Ty< i >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(func_arity) f_id)).
  Proof.
    intros f_id.
    assert (f_val := interprete_func f_id).
    revert f_val.
    generalize (func_arity lang f_id).
    induction n as [| n IH]; simpl.
    - intros con_w w.
      exact (con_w w).
    - intros fun_by_w arg_by_w.
      apply IH.
      intros w.
      exact (fun_by_w w (arg_by_w w)).
  Defined.

  End EVALUATION_FOR_FUNC.

  Section EVALUATION_FOR_PRED.

  Variable interprete_pred : forall p_id : nat, Worlds -> interprete_ty (nat_rec _ (Ty< o >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(pred_arity) p_id)).

  Definition interpretew_pred :
    forall p_id : nat,
    interpretew_ty (nat_rec _ (Ty< o >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(pred_arity) p_id)).
  Proof.
    intros p_id.
    assert (p_val := interprete_pred p_id).
    revert p_val.
    generalize (pred_arity lang p_id).
    induction n as [| n IH]; simpl.
    - intros val_w w.
      exact (val_w w).
    - intros fun_by_w arg_by_w.
      apply IH.
      intros w.
      exact (fun_by_w w (arg_by_w w)).
  Defined.

  End EVALUATION_FOR_PRED.

  Variable accessibility_relation : Worlds -> Worlds -> Prop.

  Local Notation " w1 `is_accessible_to` w2 " := (accessibility_relation w1 w2) (at level 70, no associativity) : type_scope.

  Variable func_env : forall f_id : nat, Worlds -> interprete_ty (nat_rec _ (Ty< i >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(func_arity) f_id)).

  Variable pred_env : forall p_id : nat, Worlds -> interprete_ty (nat_rec _ (Ty< o >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(pred_arity) p_id)).

  Definition interpretew_ctor (c : ctor) : interpretew_ty (get_ty_of_ctor lang c) :=
    match c as c0 return
      interpretew_ty
      match c0 with
      | CONTRADICTION => Ty< o >
      | NEGATION => Ty< o -> o >
      | CONJUNCTION => Ty< o -> o -> o >
      | DISJUNCTION => Ty< o -> o -> o >
      | IMPLICATION => Ty< o -> o -> o >
      | BICONDITIONAL => Ty< o -> o -> o >
      | FORALL => Ty< (i -> o) -> o >
      | EXISTS => Ty< (i -> o) -> o >
      | EQUAL => Ty< i -> i -> o >
      | BOX => Ty< o -> o >
      | DIA => Ty< o -> o >
      | FuncSym f_id => (nat_rec _ (Ty< i >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(func_arity) f_id))
      | PredSym p_id => (nat_rec _ (Ty< o >) (fun _ : nat => fun ty1 : ty => Ty< i -> ty1 >) (lang.(pred_arity) p_id))
      end
    with
    | CONTRADICTION => fun w : Worlds => False
    | NEGATION => fun wP1 : wProp => fun w : Worlds => ~ wP1 w
    | CONJUNCTION => fun wP1 : wProp => fun wP2 : wProp => fun w : Worlds => wP1 w /\ wP2 w
    | DISJUNCTION => fun wP1 : wProp => fun wP2 : wProp => fun w : Worlds => wP1 w \/ wP2 w
    | IMPLICATION => fun wP1 : wProp => fun wP2 : wProp => fun w : Worlds => wP1 w -> wP2 w
    | BICONDITIONAL => fun wP1 : wProp => fun wP2 : wProp => fun w : Worlds => wP1 w <-> wP2 w
    | FORALL => fun wP1' : wUniv -> wProp => fun w : Worlds => forall y_val : wUniv, wP1' y_val w
    | EXISTS => fun wP1' : wUniv -> wProp => fun w : Worlds => exists y_val : wUniv, wP1' y_val w
    | EQUAL => fun x_val : wUniv => fun y_val : wUniv => fun w : Worlds => x_val w = y_val w
    | BOX => fun wP1 : wProp => fun w : Worlds => forall w' : Worlds, w `is_accessible_to` w' -> wP1 w'
    | DIA => fun wP1 : wProp => fun w : Worlds => exists w' : Worlds, w `is_accessible_to` w' /\ wP1 w'
    | FuncSym f_id => interpretew_func func_env f_id
    | PredSym p_id => interpretew_pred pred_env p_id
    end
  .

  Definition interpretew_tm (tm_expr : tm) (ty_expr : ty) (tm_expr_isof_ty_expr : typeOf tm_expr ty_expr) :
    forall interpretew_ivar : ivar -> wUniv,
    interpretew_ty ty_expr.
  Proof.
    induction tm_expr_isof_ty_expr as [x | c | t1 t2 ty1 ty2 H1 IH1 H2 IH2 | y t1 ty1 H1 IH1]; intros var_env.
    - exact (var_env x).
    - exact (interpretew_ctor c).
    - exact (IH1 var_env (IH2 var_env)).
    - exact (fun y_val : wUniv => IH1 (fun z : ivar => if ivar_eq_dec y z then y_val else var_env z)).
  Defined.

  End EVALUATION.

End FirstOrderModalLogicSemantics.
