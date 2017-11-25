Require Import HoTT.
Require Import quotient1.
Require Import Groupoid.


Section QType.

  Inductive QType' :=
  | Qubit
  | Tensor (Q1 Q2 : QType')
  | Lolli (Q1 Q2 : QType')
  | Lower : forall (τ : Type) `{IsHSet τ}, QType'
  .  
  Instance QType'_HSet : IsHSet QType'.
  Admitted.

  Variable UnitaryMatrix : QType' -> QType' -> Type.
    Context 
          {U_HSet : forall Q1 Q2, IsHSet (UnitaryMatrix Q1 Q2)}
          {U_refl : Reflexive UnitaryMatrix}
          {U_trans : Transitive UnitaryMatrix}
          {U_symm : Symmetric UnitaryMatrix}
          (U_groupoid : groupoid _ UnitaryMatrix).

    Local Open Scope groupoid_scope.


    Variable U_tensor : forall {x x' y y'} 
                        (U : UnitaryMatrix x x') (U' : UnitaryMatrix y y'),
                        UnitaryMatrix (Tensor x y) (Tensor x' y').
    Variable U_tensor_compose : forall {x1 x2 x3 y1 y2 y3} 
                           (U1 : UnitaryMatrix x1 x2) (U2 : UnitaryMatrix x2 x3)
                           (V1 : UnitaryMatrix y1 y2) (V2 : UnitaryMatrix y2 y3),
        U_tensor _ _ _ _ (U2 o U1) (V2 o V1)
      = U_tensor _ _ _ _ U2 V2 o U_tensor _ _ _ _ U1 V1.



    Definition QType := quotient1 U_groupoid.
    
    Definition Tensor' : QType -> QType -> QType.
    Proof.
      apply quotient1_map2 with (f := Tensor) (map_cell := U_tensor).
      apply U_tensor_compose.
    Defined.

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

Section QType_map.
  Variable f : QType' -> QType'.
  Variable f_correct : forall Q1 Q2 (U : UnitaryMatrix Q1 Q2),
           f Q1 = f Q2.
  Definition QType_map : QType -> QType.
  Proof.
    set (C_point' := fun (Q : QType') => point U_groupoid (f Q)).
    transparent assert (C_cell' : (forall x y, UnitaryMatrix x y ->
        C_point' x = C_point' y)).
    { intros x y U.
      unfold C_point'.
      apply cell.
      admit (*???? *).
    }
    apply quotient1_rec with (C_point := C_point') (C_cell := C_cell'); 
    [ | apply quotient1_trunc ].
    intros x y z U1 U2. unfold C_cell'.
    admit.
  Admitted.
End QType_map.

(*Note: QType IS NOT an HSET.*)


(*Definition tensor : QType -> QType -> QType.
Proof.
  apply QType_rec2 with (C_QTy := fun Q1 Q2 => QTy (Tensor Q1 Q2)); auto.
  intros.
  set (dclass := fun Q1 Q2 =>  (Tensor Q1 Q2)).
  apply QType_rec2 with (dclass := dclass); auto.
  - apply quotient_set.
  - intros. unfold dclass.
    admit (* another property of UnitaryMatrix: classes must respect tensor...*).
Admitted.

*)
Infix "⊗" := Tensor' (at level 40).



End QType.