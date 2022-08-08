Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeUtil.

Module BinaryTree.

  Inductive bintree (A : Type) : Type :=
  | BTnull : bintree A
  | BTnode (t_l : bintree A) (x : A) (t_r : bintree A) : bintree A
  .

End BinaryTree.
