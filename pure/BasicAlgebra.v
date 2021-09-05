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
      pl m1 (pl m2 m3) == pl m1 (pl m2 m3)
    ; ze_left_id_pl :
      forall m1 : M,
      pl ze m1 == m1
    ; ze_right_id_pl :
      forall m1 : M,
      pl m1 ze == m1
    }
  .

  Section BasicTheoriesOnMonoid.

  Context (M : Type) `{M_isSetoid : isSetoid M} `{M_isMonoid : @isMonoid M M_isSetoid}.

  End BasicTheoriesOnMonoid.

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

  Section BasicTheoriesOnGroup.

  Context (G : Type) `{G_isSetoid : isSetoid G} `{G_isMonoid : @isMonoid G G_isSetoid} `{G_isGroup : @isGroup G G_isSetoid G_isMonoid}.

  End BasicTheoriesOnGroup.

End BasicGroupTheory.
