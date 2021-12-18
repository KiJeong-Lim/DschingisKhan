Require Import Coq.Bool.Bool.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module Prelude.

  Import BasicPosetTheory.

  Class Ord (A : Type) `{Ord_requiresPoset : isPoset A} : Type :=
    { lt : A -> A -> bool
    ; leProp_total : forall x : A, forall y : A, x =< y \/ y =< x
    ; lt_spec : forall x : A, forall y : A, lt x y = false <-> y =< x
    }
  .

  Definition compare {A : Type} `{A_isPoset : isPoset A} `{A_isOrd : @Ord A A_isPoset} : A -> A -> comparison :=
    fun lhs : A =>
    fun rhs : A =>
    if lt lhs rhs then Lt
    else if lt rhs lhs then Gt
    else Eq
  .

End Prelude.

Module RedBlackTree. (* Reference: https://abhiroop.github.io/Haskell-Red-Black-Tree/ *)

  Import BasicPosetTheory Prelude.

  Inductive Color : Set :=
  | R : Color
  | B : Color
  .

  Inductive Tree (Key : Type) (Val : Type) : Type :=
  | E : Tree Key Val
  | T : Color -> Tree Key Val -> Key -> Val -> Tree Key Val -> Tree Key Val
  .

  Section RBT_theory.

  Context {MyKey : Type} {MyVal : Type}.

  Let MyTree : Type :=
    Tree MyKey MyVal
  .

  Let MyE : MyTree :=
    E MyKey MyVal
  .

  Let MyT : Color -> MyTree -> MyKey -> MyVal -> MyTree -> MyTree :=
    T MyKey MyVal
  .

  Definition balance (clr : Color) (t1 : MyTree) (key : MyKey) (val : MyVal) (t2 : MyTree) : MyTree :=
    match clr, t1, key, val, t2 with
    | R, T _ _ R (T _ _ R a x vx b) y vy c, z, vz, d => MyT R (MyT B a x vx b) y vy (MyT B c z vz d)
    | R, T _ _ R a x vx (T _ _ R b y vy c), z, vz, d => MyT R (MyT B a x vx b) y vy (MyT B c z vz d)
    | R, a, x, vx, T _ _ R (T _ _ R b y vy c) z vz d => MyT R (MyT B a x vx b) y vy (MyT B c z vz d)
    | R, a, x, vx, T _ _ R b y vy (T _ _ R c z vz d) => MyT R (MyT B a x vx b) y vy (MyT B c z vz d)
    | color, a, x, vx, b => MyT color a x vx b
    end
  .

  Definition makeBlack (t : MyTree) : MyTree :=
    match t with
    | E _ _ => MyE
    | T _ _ clr t1 key val t2 => MyT B t1 key val t2
    end
  .

  Context `{MyKey_isPoset : isPoset MyKey} `{instance_of_Ord_for_MyKey : @Ord MyKey MyKey_isPoset}.

  Fixpoint lookup (key_q : MyKey) (t : MyTree) {struct t} : option MyVal :=
    match t with
    | E _ _ => None
    | T _ _ clr t1 key val t2 =>
      match compare key_q key with
      | Lt => lookup key_q t1
      | Eq => Some val
      | Gt => lookup key_q t2
      end
    end
  .

  End RBT_theory.

End RedBlackTree.
