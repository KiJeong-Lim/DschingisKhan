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
Require Import DschingisKhan.Data.Vector.
Require Import DschingisKhan.Data.InteractionTree.
Require Import DschingisKhan.Logic.PeanoArithmetic.
Require Import DschingisKhan.Logic.InteractionTreeTheory.

Module GIT.

  Import ListNotations InteractionTrees.

  Local Existing Instances freeSetoidFromSetoid1.

  Definition isPartialFunctionGraph {arity : nat} (fun_graph : ensemble (vector nat arity * nat)) : Prop :=
    forall x : vector nat arity, forall y : nat, forall y' : nat, (x, y) \in fun_graph -> (x, y') \in fun_graph -> y = y'
  .

  Definition converges_to {arity : nat} (computer : vector nat arity -> itree void1 nat) (arg : vector nat arity) (rv : nat) : Prop :=
    exists fuel : nat, burnTau_nat fuel (computer arg) == Ret rv
  .

  Record muPartial {arity : nat} (fun_graph : ensemble (vector nat arity * nat)) : Type :=
    { computer : vector nat arity -> itree void1 nat
    ; computer_repr
      : forall arg : vector nat arity, forall rv : nat, converges_to computer arg rv <-> member (arg, rv) fun_graph
    ; partialness
      : isPartialFunctionGraph fun_graph
    }
  .

End GIT.
