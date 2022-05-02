Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import DschingisKhan.Prelude.PreludeInit.
Require Import DschingisKhan.Prelude.PreludeMath.
Require Import DschingisKhan.Prelude.PreludeUtil.
Require Import DschingisKhan.Math.BasicPosetTheory.
Require Import DschingisKhan.Math.BasicGeneralTopology.

Module BooleanAlgebra.

  Import ListNotations MathProps MathNotations MathClasses BasicPosetTheory.

  Create HintDb boolalg_hints.

  Class BooleanAlgebra_sig (BA : Type) : Type :=
    { andBA : BA -> BA -> BA
    ; orBA : BA -> BA -> BA
    ; notBA : BA -> BA
    ; trueBA : BA
    ; falseBA : BA
    }
  .

  Local Instance bool_hasBooleanAlgebraMethods : BooleanAlgebra_sig bool :=
    { andBA := andb
    ; orBA := orb
    ; notBA := negb
    ; trueBA := true
    ; falseBA := false
    }
  .

  Class BooleanAlgebra_axiom (BA : Type) {requiresSetoid : isSetoid BA} {requiresBooleanAlgebraMethods : BooleanAlgebra_sig BA} : Prop :=
    { andBA_congru :> preserves_eqProp2 andBA
    ; orBA_congru :> preserves_eqProp2 orBA
    ; notBA_congru :> preserves_eqProp1 notBA
    ; andBA_assoc :> Assoc andBA
    ; orBA_assoc :> Assoc orBA
    ; andBA_comm :> Comm andBA
    ; orBA_comm :> Comm orBA
    ; andBA_distr_orBA :> andBA `distributesOver` orBA
    ; orBA_distr_andBA :> orBA `distributesOver` andBA
    ; trueBA_id_andBA :> trueBA `isIdentityOf` andBA
    ; falseBA_id_orBA :> falseBA `isIdentityOf` orBA
    ; falseBA_ann_andBA :> falseBA `isAnnihilatorFor` andBA
    ; trueBA_ann_orBA :> falseBA `isAnnihilatorFor` andBA
    ; andBA_idem :> Idem andBA
    ; orBA_idem :> Idem orBA
    ; Absorption_andBA_orBA :> Absorption andBA orBA
    ; andBA_notBA_falseBA (b : BA)
      : andBA b (notBA b) == falseBA
    ; orBA_notBA_trueBA (b : BA)
      : orBA b (notBA b) == trueBA
    }
  .

  Class isBooleanAlgebra (BA : Type) {requiresSetoid : isSetoid BA} : Type :=
    { hasBooleanAlgebraMethods :> BooleanAlgebra_sig BA
    ; BooleanAlgebra_obeysBooleanAlgebra_axiom :> BooleanAlgebra_axiom BA (requiresSetoid := requiresSetoid) (requiresBooleanAlgebraMethods := hasBooleanAlgebraMethods)
    }
  .

  Section BooleanAlgebraAsPoset.

  Context {BA : Type} {requiresSetoid : isSetoid BA} {requiresBooleanAlgebra : isBooleanAlgebra BA (requiresSetoid := requiresSetoid)}.

  Definition leBA (lhs : BA) (rhs : BA) : Prop := andBA lhs rhs == lhs.

  Global Instance leBA_Reflexive
    : Reflexive leBA.
  Proof. intros x. eapply andBA_idem with (x := x). Qed.

  Global Instance leBA_Transitive
    : Transitive leBA.
  Proof. intros x y z x_le_y y_le_z. unfold leBA in *. rewrite <- x_le_y at 2. rewrite <- y_le_z. now rewrite andBA_assoc, x_le_y. Qed.

  Global Instance leBA_PreOrder : PreOrder leBA :=
    { PreOrder_Reflexive := leBA_Reflexive
    ; PreOrder_Transitive := leBA_Transitive
    }
  .

  Global Instance leBA_PartialOrder
    : PartialOrder eqProp leBA.
  Proof.
    intros lhs rhs. unfold leBA. split; unfold relation_conjunction, flip; cbn.
    - intros hyp_eq. rewrite hyp_eq. split; eapply leBA_Reflexive.
    - intros [hyp_le hyp_ge]. rewrite <- hyp_le. rewrite <- hyp_ge at 2. eapply andBA_comm.
  Qed.

  Global Instance BooleanAlgebra_isPoset : isPoset BA :=
    { leProp := leBA
    ; Poset_requiresSetoid := requiresSetoid
    ; leProp_PreOrder := leBA_PreOrder
    ; leProp_PartialOrder := leBA_PartialOrder
    }
  .

  End BooleanAlgebraAsPoset.

End BooleanAlgebra.

Module CountableBooleanAlgebra.

  Import ListNotations MathProps MathNotations MathClasses BasicPosetTheory BooleanAlgebra.

  Class isCBA (BA : Type) {requiresSetoid : isSetoid BA} : Type :=
    { CBA_requiresBooleanAlgebra :> isBooleanAlgebra BA
    ; CBA_requiresCountable :> isCountable BA
    }
  .

End CountableBooleanAlgebra.
