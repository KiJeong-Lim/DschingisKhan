Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.
Require Import DschingisKhan.Prelude.PreludeClassic.

Module PeanoArithmetic.

  Import ListNotations.

  Definition ivar : Set := nat.

  Inductive term : Set :=
  | IVarT (x : ivar) : term
  | ZeroT : term
  | SuccT (t1 : term) : term
  | PlusT (t1 : term) (t2 : term) : term
  | MultT (t1 : term) (t2 : term) : term
  .

  Inductive formula : Set :=
  | EqnF (t1 : term) (t2 : term) : formula
  | LeqF (t1 : term) (t2 : term) : formula
  | NegF (f1 : formula) : formula
  | ImpF (f1 : formula) (f2 : formula) : formula
  | AllF (y : ivar) (f1 : formula) : formula
  .

  Section SEMANTICS.

  Fixpoint eval_term (env : ivar -> nat) (t : term) {struct t} : nat :=
    match t with
    | IVarT x => env x
    | ZeroT => O
    | SuccT t1 => S (eval_term env t1)
    | PlusT t1 t2 => eval_term env t1 + eval_term env t2
    | MultT t1 t2 => eval_term env t1 * eval_term env t2
    end
  .

  Fixpoint eval_formula (env : ivar -> nat) (f : formula) {struct f} : Prop :=
    match f with
    | EqnF t1 t2 => eval_term env t1 = eval_term env t2
    | LeqF t1 t2 => eval_term env t1 <= eval_term env t2
    | NegF f1 => ~ eval_formula env f1
    | ImpF f1 f2 => eval_formula env f1 -> eval_formula env f2
    | AllF y f1 => forall n : nat, eval_formula (fun z : ivar => if eq_dec y z then n else env z) f1
    end
  .

  End SEMANTICS.

  Section SUBSTITUTION.

  Definition Subst : Set := ivar -> term.

  Definition nilSubst : Subst :=
    fun z : ivar => IVarT z
  .

  Definition consSubst (y : ivar) (t : term) (sigma : Subst) : Subst :=
    fun z : ivar => if eq_dec y z then t else sigma z
  .

  Fixpoint fvs_term (t : term) {struct t} : list ivar :=
    match t with
    | IVarT x => [x]
    | ZeroT => []
    | SuccT t1 => fvs_term t1
    | PlusT t1 t2 => fvs_term t1 ++ fvs_term t2
    | MultT t1 t2 => fvs_term t1 ++ fvs_term t2
    end
  .

  Fixpoint fvs_formula (f : formula) {struct f} : list ivar :=
    match f with
    | EqnF t1 t2 => fvs_term t1 ++ fvs_term t2
    | LeqF t1 t2 => fvs_term t1 ++ fvs_term t2
    | NegF f1 => fvs_formula f1
    | ImpF f1 f2 => fvs_formula f1 ++ fvs_formula f2
    | AllF y f1 => remove eq_dec y (fvs_formula f1)
    end
  .

  Definition chi (sigma : Subst) (f : formula) : ivar :=
    suc (maxs (map (fun z : ivar => maxs (fvs_term (sigma z))) (fvs_formula f)))
  .

  Fixpoint subst_term (sigma : Subst) (t : term) {struct t} : term :=
    match t with
    | IVarT x => sigma x
    | ZeroT => ZeroT
    | SuccT t1 => SuccT (subst_term sigma t1)
    | PlusT t1 t2 => PlusT (subst_term sigma t1) (subst_term sigma t2)
    | MultT t1 t2 => MultT (subst_term sigma t1) (subst_term sigma t2)
    end
  .

  Fixpoint subst_formula (sigma : Subst) (f : formula) {struct f} : formula :=
    match f with
    | EqnF t1 t2 => EqnF (subst_term sigma t1) (subst_term sigma t2)
    | LeqF t1 t2 => LeqF (subst_term sigma t1) (subst_term sigma t2)
    | NegF f1 => NegF (subst_formula sigma f1)
    | ImpF f1 f2 => ImpF (subst_formula sigma f1) (subst_formula sigma f2)
    | AllF y f1 =>
      let z : ivar := chi sigma f in
      let sigma' : Subst := consSubst y (IVarT z) sigma in
      AllF z (subst_formula sigma' f1)
    end
  .

  End SUBSTITUTION.

End PeanoArithmetic.
