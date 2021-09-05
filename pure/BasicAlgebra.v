Require Import Coq.Arith.Plus.
Require Import Coq.Bool.Bool.
Require Import Coq.Program.Basics.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module BasicGroupTheory.

  Import BasicSetoidTheory.

  Class isMonoid (M : Type) `{M_isSetoid : isSetoid M} : Type :=
    { pl : M -> M -> M
    ; ze : M
    ; pl_assoc :
      forall m1 : M,
      forall m2 : M,
      forall m3 : M,
      pl m1 (pl m2 m3) == pl (pl m1 m2) m3
    ; ze_left_id_pl :
      forall m1 : M,
      pl ze m1 == m1
    ; ze_right_id_pl :
      forall m1 : M,
      pl m1 ze == m1
    }
  .

  Class isCommutativeMonoid (M : Type) `{M_isSetoid : isSetoid M} `{M_isMonoid : @isMonoid M M_isSetoid} : Prop :=
    { pl_comm :
      forall m1 : M,
      forall m2 : M,
      pl m1 m2 == pl m2 m1
    }
  .

  Class isGroup (G : Type) `{G_isSetoid : isSetoid G} `{G_isMonoid : @isMonoid G G_isSetoid} : Type :=
    { ne : G -> G
    ; ne_left_inv_pl :
      forall g1 : G,
      pl (ne g1) g1 == ze
    ; ne_right_inv_pl :
      forall g1 : G,
      pl g1 (ne g1) == ze
    }
  .

  Class isAbelianGroup (G : Type) `{G_isSetoid : isSetoid G} `{G_isMonoid : @isMonoid G G_isSetoid} `{G_isGroup : @isGroup G G_isSetoid G_isMonoid} : Prop :=
    { AbelianGroup_requiresCommutative :> @isCommutativeMonoid G G_isSetoid G_isMonoid
    }
  .

  Global Instance nat_isMonoid : @isMonoid nat nat_isSetoid :=
    { pl := plus
    ; ze := 0
    ; pl_assoc := plus_assoc
    ; ze_left_id_pl := plus_0_l
    ; ze_right_id_pl := plus_0_r
    }
  .

  Global Instance nat_isCommutativeMonoid : @isCommutativeMonoid nat nat_isSetoid nat_isMonoid :=
    { pl_comm := plus_comm
    }
  .

  Lemma xorb_assoc :
    forall b1 : bool,
    forall b2 : bool,
    forall b3 : bool,
    xorb b1 (xorb b2 b3) = xorb (xorb b1 b2) b3.
  Proof.
    intros [|] [|] [|]; reflexivity.
  Qed.

  Lemma xorb_b_false_eq_b :
    forall b1 : bool,
    xorb b1 false = b1.
  Proof.
    intros [|]; reflexivity.
  Qed.

  Lemma xorb_false_b_eq_b :
    forall b1 : bool,
    xorb false b1 = b1.
  Proof.
    intros [|]; reflexivity.
  Qed.

  Global Instance bool_isMonoid : @isMonoid bool bool_isSetoid :=
    { pl := xorb
    ; ze := false
    ; pl_assoc := xorb_assoc
    ; ze_left_id_pl := xorb_b_false_eq_b
    ; ze_right_id_pl := xorb_false_b_eq_b
    }
  .

  Global Instance bool_isCommutativeMonoid : @isCommutativeMonoid bool bool_isSetoid bool_isMonoid :=
    { pl_comm := xorb_comm
    }
  .

  Lemma xorb_b_b_eq_false :
    forall b1 : bool,
    xorb b1 b1 = false.
  Proof.
    intros [|]; reflexivity.
  Qed.

  Global Instance bool_isGroup : @isGroup bool bool_isSetoid bool_isMonoid :=
    { ne := @id bool
    ; ne_left_inv_pl := xorb_b_b_eq_false
    ; ne_right_inv_pl := xorb_b_b_eq_false
    }
  .

  Global Instance bool_isAbelianGroup : @isAbelianGroup bool bool_isSetoid bool_isMonoid bool_isGroup :=
    { AbelianGroup_requiresCommutative := bool_isCommutativeMonoid
    }
  .

End BasicGroupTheory.
