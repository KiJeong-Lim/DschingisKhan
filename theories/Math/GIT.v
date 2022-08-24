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

  Record muPartial {arity : nat} (funGraph : ensemble (vector nat arity * nat)) : Type :=
    { computer : vector nat arity -> itree void1 nat
    ; computer_repr (arg : vector nat arity) (rv : nat)
      (CONVERGES : exists fuel : nat, burnTau_nat fuel (computer arg) == Ret rv)
      : forall result : nat, rv = result <-> member (arg, result) funGraph
    ; funGraph_unique (arg : vector nat arity) (result : nat) (result' : nat)
      (H_result : member (arg, result) funGraph)
      (H_result' : member (arg, result') funGraph)
      : result = result'
    }
  .

End GIT.
