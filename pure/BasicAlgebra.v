Require Import Coq.Arith.Plus.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import DschingisKhan.pure.MyStructures.
Require Import DschingisKhan.pure.MyUtilities.

Module BasicGroupTheory.

  Import ListNotations ProperNotations EqFacts BasicSetoidTheory.

  Section BASIC_DEFINITIONS_RELATED_TO_GROUP.

  Local Open Scope signature_scope.

  Let MySet : Type :=
    Type
  .

  Definition isAssociative {A : MySet} `{A_isSetoid : isSetoid A} : (A -> A -> A) -> Prop :=
    fun binop : A -> A -> A =>
    forall x : A,
    forall y : A,
    forall z : A,
    @eqProp A A_isSetoid (binop x (binop y z)) (binop (binop x y) z)
  .

  Definition isCommutative {A : MySet} `{A_isSetoid : isSetoid A} : (A -> A -> A) -> Prop :=
    fun binop : A -> A -> A =>
    forall x : A,
    forall y : A,
    @eqProp A A_isSetoid (binop x y) (binop y x)
  .

  Definition isLeftIdOf {A : MySet} `{A_isSetoid : isSetoid A} : A -> (A -> A -> A) -> Prop :=
    fun e : A =>
    fun binop : A -> A -> A =>
    forall x : A,
    @eqProp A A_isSetoid (binop e x) x
  .

  Definition isRightIdOf {A : MySet} `{A_isSetoid : isSetoid A} : A -> (A -> A -> A) -> Prop :=
    fun e : A =>
    fun binop : A -> A -> A =>
    forall x : A,
    @eqProp A A_isSetoid (binop x e) x
  .

  Class isMonoid (M : MySet) `{M_isSetoid : isSetoid M} : MySet :=
    { pl : M -> M -> M
    ; ze : M
    ; pl_preserves_eq : Proper (@eqProp M M_isSetoid ==> @eqProp M M_isSetoid ==> @eqProp M M_isSetoid) pl
    ; pl_assoc : @isAssociative M M_isSetoid pl
    ; ze_left_id_pl : @isLeftIdOf M M_isSetoid ze pl
    ; ze_right_id_pl : @isRightIdOf M M_isSetoid ze pl
    }
  .

  Definition isLeftInverseOf {M : MySet} `{M_isSetoid : isSetoid M} `{M_isMonoid : @isMonoid M M_isSetoid} : M -> M -> Prop :=
    fun inv_x : M =>
    fun x : M =>
    @eqProp M M_isSetoid (@pl M M_isSetoid M_isMonoid inv_x x) (@ze M M_isSetoid M_isMonoid)
  .

  Definition isRightInverseOf {M : MySet} `{M_isSetoid : isSetoid M} `{M_isMonoid : @isMonoid M M_isSetoid} : M -> M -> Prop :=
    fun inv_x : M =>
    fun x : M =>
    @eqProp M M_isSetoid (@pl M M_isSetoid M_isMonoid x inv_x) (@ze M M_isSetoid M_isMonoid)
  .

  Class isGroup (G : MySet) `{G_isSetoid : isSetoid G} `{G_isMonoid : @isMonoid G G_isSetoid} : MySet :=
    { ne : G -> G
    ; ne_preseves_eq : Proper (@eqProp G G_isSetoid ==> @eqProp G G_isSetoid) ne
    ; ne_left_inv_pl :
      forall x : G,
      @isLeftInverseOf G G_isSetoid G_isMonoid (ne x) x
    ; ne_right_inv_pl :
      forall x : G,
      @isRightInverseOf G G_isSetoid G_isMonoid (ne x) x
    }
  .

  Class isAbelianGroup {G : MySet} `{G_isSetoid : isSetoid G} `{G_isMonoid : @isMonoid G G_isSetoid} (G_requiresGroup : @isGroup G G_isSetoid G_isMonoid) : Prop :=
    { AbelianGroup_requiresCommutative : @isCommutative G G_isSetoid (@pl G G_isSetoid G_isMonoid)
    }
  .

  End BASIC_DEFINITIONS_RELATED_TO_GROUP.

  Global Instance nat_isMonoid : @isMonoid nat nat_isSetoid :=
    { pl := plus
    ; ze := 0
    ; pl_preserves_eq := eq_congruence2 plus
    ; pl_assoc := plus_assoc
    ; ze_left_id_pl := plus_0_l
    ; ze_right_id_pl := plus_0_r
    }
  .

  Lemma xorb_isAssociative :
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
    ; pl_preserves_eq := eq_congruence2 xorb
    ; pl_assoc := xorb_isAssociative
    ; ze_left_id_pl := xorb_b_false_eq_b
    ; ze_right_id_pl := xorb_false_b_eq_b
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
    ; ne_preseves_eq := eq_congruence (@id bool)
    ; ne_left_inv_pl := xorb_b_b_eq_false
    ; ne_right_inv_pl := xorb_b_b_eq_false
    }
  .

  Lemma xorb_isCommutative :
    forall b1 : bool,
    forall b2 : bool,
    xorb b1 b2 = xorb b2 b1.
  Proof.
    intros [|] [|]; reflexivity.
  Qed.

  Global Instance bool_isAbelianGroup : @isAbelianGroup bool bool_isSetoid bool_isMonoid bool_isGroup :=
    { AbelianGroup_requiresCommutative := xorb_isCommutative
    }
  .

  Global Instance arrow_isMonoid {S : Type} {M : Type} `{M_isSetoid : isSetoid M} (M_requiresMonoid : @isMonoid M M_isSetoid) : @isMonoid (arrow S M) (@arrow_isSetoid S M M_isSetoid) :=
    { pl :=
      fun f1 : arrow S M =>
      fun f2 : arrow S M =>
      fun x : S =>
      @pl M M_isSetoid M_requiresMonoid (f1 x) (f2 x)
    ; ze :=
      fun x : S =>
      @ze M M_isSetoid M_requiresMonoid
    ; pl_preserves_eq :=
      fun f1 : arrow S M =>
      fun g1 : arrow S M =>
      fun Heq1 : arrow_eqProp S M M_isSetoid f1 g1 =>
      fun f2 : S -> M =>
      fun g2 : S -> M =>
      fun Heq2 : arrow_eqProp S M M_isSetoid f2 g2 =>
      fun x : S =>
      @pl_preserves_eq M M_isSetoid M_requiresMonoid (f1 x) (g1 x) (Heq1 x) (f2 x) (g2 x) (Heq2 x)
    ; pl_assoc :=
      fun f1 : arrow S M =>
      fun f2 : arrow S M =>
      fun f3 : arrow S M =>
      fun x : S =>
      @pl_assoc M M_isSetoid M_requiresMonoid (f1 x) (f2 x) (f3 x)
    ; ze_left_id_pl :=
      fun f1 : arrow S M =>
      fun x : S =>
      @ze_left_id_pl M M_isSetoid M_requiresMonoid (f1 x)
    ; ze_right_id_pl :=
      fun f1 : arrow S M =>
      fun x : S =>
      @ze_right_id_pl M M_isSetoid M_requiresMonoid (f1 x)
    }
  .

  Global Instance arrow_isGroup {S : Type} {G : Type} `{G_isSetoid : isSetoid G} `{G_isMonoid : @isMonoid G G_isSetoid} (G_requiresGroup : @isGroup G G_isSetoid G_isMonoid) : @isGroup (arrow S G) (@arrow_isSetoid S G G_isSetoid) (@arrow_isMonoid S G G_isSetoid G_isMonoid) :=
    { ne :=
      fun f1 : arrow S G =>
      fun x : S =>
      @ne G G_isSetoid G_isMonoid G_requiresGroup (f1 x)
    ; ne_preseves_eq :=
      fun f1 : arrow S G =>
      fun g1 : arrow S G =>
      fun Heq1 : arrow_eqProp S G G_isSetoid f1 g1 =>
      fun x : S =>
      @ne_preseves_eq G G_isSetoid G_isMonoid G_requiresGroup (f1 x) (g1 x) (Heq1 x)
    ; ne_left_inv_pl :=
      fun f1 : arrow S G =>
      fun x : S =>
      @ne_left_inv_pl G G_isSetoid G_isMonoid G_requiresGroup (f1 x)
    ; ne_right_inv_pl :=
      fun f1 : arrow S G =>
      fun x : S =>
      @ne_right_inv_pl G G_isSetoid G_isMonoid G_requiresGroup (f1 x)
    }
  .

  Global Instance arrow_isAbelianGroup {S : Type} {G : Type} `{G_isSetoid : isSetoid G} `{G_isMonoid : @isMonoid G G_isSetoid} `{G_isGroup : @isGroup G G_isSetoid G_isMonoid} (G_requiresAbelianGroup : @isAbelianGroup G G_isSetoid G_isMonoid G_isGroup) : @isAbelianGroup (arrow S G) (@arrow_isSetoid S G G_isSetoid) (@arrow_isMonoid S G G_isSetoid G_isMonoid) (@arrow_isGroup S G G_isSetoid G_isMonoid G_isGroup) :=
    { AbelianGroup_requiresCommutative :=
      fun f1 : arrow S G =>
      fun f2 : arrow S G =>
      fun x : S =>
      @AbelianGroup_requiresCommutative G G_isSetoid G_isMonoid G_isGroup G_requiresAbelianGroup (f1 x) (f2 x)
    }
  .

End BasicGroupTheory.
