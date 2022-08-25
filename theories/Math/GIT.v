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

  Definition converges_to {arity : nat} (computer : vector nat arity -> itree void1 nat) (arg : vector nat arity) (rv : nat) : Prop :=
    exists fuel : nat, burnTau_nat fuel (computer arg) == Ret rv
  .

End GIT.
