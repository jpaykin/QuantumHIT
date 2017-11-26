Require Import HoTT.
Require Import quotient1.
Require Import Groupoid.


Section QType.

  Inductive QType' :=
  | Qubit'
  | Tensor' (Q1 Q2 : QType')
  | Lolli' (Q1 Q2 : QType')
  | Lower' : forall (τ : Type) `{IsHSet τ}, QType'
  .  
  Instance QType'_HSet : IsHSet QType'.
  Admitted.


  (* These are axioms because I don't want to deal with actual vector spaces and
  unitary transformations quite yet. They should not be axiomatic in the end. *)

  Axiom UnitaryMatrix : QType' -> QType' -> Type.
  Axiom U_HSet : forall Q1 Q2, IsHSet (UnitaryMatrix Q1 Q2).
  Axiom U_refl : Reflexive UnitaryMatrix.
  Axiom U_trans : Transitive UnitaryMatrix.
  Axiom U_symm : Symmetric UnitaryMatrix.
  Axiom U_groupoid : groupoid _ UnitaryMatrix.

    Local Open Scope groupoid_scope.


    Axiom U_tensor : forall {x x' y y'} 
                        (U : UnitaryMatrix x x') (U' : UnitaryMatrix y y'),
                        UnitaryMatrix (Tensor' x y) (Tensor' x' y').
    Axiom U_tensor_compose : forall {x1 x2 x3 y1 y2 y3} 
                           (U1 : UnitaryMatrix x1 x2) (U2 : UnitaryMatrix x2 x3)
                           (V1 : UnitaryMatrix y1 y2) (V2 : UnitaryMatrix y2 y3),
        U_tensor (U2 o U1) (V2 o V1)
      = U_tensor U2 V2 o U_tensor U1 V1.

    Axiom U_lolli : forall {x x' y y'} 
                        (U : UnitaryMatrix x x') (U' : UnitaryMatrix y y'),
                        UnitaryMatrix (Lolli' x y) (Lolli' x' y').
    Axiom U_lolli_compose : forall {x1 x2 x3 y1 y2 y3} 
                           (U1 : UnitaryMatrix x1 x2) (U2 : UnitaryMatrix x2 x3)
                           (V1 : UnitaryMatrix y1 y2) (V2 : UnitaryMatrix y2 y3),
        U_lolli (U2 o U1) (V2 o V1)
      = U_lolli U2 V2 o U_lolli U1 V1.


    Definition QType := quotient1 U_groupoid.
    
    Definition Tensor : QType -> QType -> QType.
    Proof.
      apply quotient1_map2 with (f := Tensor') (map_cell := @U_tensor).
      apply @U_tensor_compose.
    Defined.
    Definition Lolli : QType -> QType -> QType.
    Proof.
      apply quotient1_map2 with (f := Lolli') (map_cell := @U_lolli).
      apply @U_lolli_compose.
    Defined.
    Definition Qubit : QType := point U_groupoid Qubit'.
    Definition Lower τ `{IsHSet τ} : QType := point U_groupoid (Lower' τ).


Lemma QUnitary_eq : forall {Q1 Q2} (U1 U2 : UnitaryMatrix Q1 Q2),
                  U1 = U2 -> cell U_groupoid U1 = cell U_groupoid U2.
Proof.
  intros Q1 Q2 U1 U2 eq.
   rewrite eq. reflexivity.
Qed. (* Do we need to go the other way? Does that even make sense? *)
     (* No, we would need [U : QTy Q1 = QTy Q2] = ||UnitaryMatrix Q1 Q2|| *)

Definition toUnitary : QType -> QType'.
Proof.
  apply quotient1_rec_set with (C_point := fun Q => Q); [ | apply QType'_HSet].
  (* this is only true up to asssociativity/commutativity *)
  (* or maybe UnitaryMatrix can be more restrictive *)
Abort.

End QType.

Infix "⊗" := Tensor (at level 40).
Infix "⊸" := Lolli (at level 40).


