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

  Axiom Matrix : QType' -> QType' -> Type.
  Axiom U_HSet : forall Q1 Q2, IsHSet (Matrix Q1 Q2).
  Axiom U_refl : Reflexive Matrix.
  Axiom U_trans : Transitive Matrix.
  Axiom U_symm : Symmetric Matrix.
  Axiom U_groupoid : groupoid _ Matrix.

    Local Open Scope groupoid_scope.

    Axiom U_tensor : forall {x x' y y'} 
                        (U : Matrix x x') (U' : Matrix y y'),
                        Matrix (Tensor' x y) (Tensor' x' y').
    Axiom U_tensor_compose : forall {x1 x2 x3 y1 y2 y3} 
                           (U1 : Matrix x1 x2) (U2 : Matrix x2 x3)
                           (V1 : Matrix y1 y2) (V2 : Matrix y2 y3),
        U_tensor (U2 o U1) (V2 o V1)
      = U_tensor U2 V2 o U_tensor U1 V1.

    Axiom U_lolli : forall {x x' y y'} 
                        (U : Matrix x x') (U' : Matrix y y'),
                        Matrix (Lolli' x y) (Lolli' x' y').
    Axiom U_lolli_compose : forall {x1 x2 x3 y1 y2 y3} 
                           (U1 : Matrix x1 x2) (U2 : Matrix x2 x3)
                           (V1 : Matrix y1 y2) (V2 : Matrix y2 y3),
        U_lolli (U2 o U1) (V2 o V1)
      = U_lolli U2 V2 o U_lolli U1 V1.


    Definition QType := quotient1 U_groupoid.
    
    Definition Tensor : QType -> QType -> QType.
    Proof.
      apply quotient1_map2 with (f := Tensor') (map_cell := @U_tensor).
      apply @U_tensor_compose.
    Defined.
    Lemma Tensor_point : forall q r, 
          Tensor (point U_groupoid q) (point U_groupoid r) = point U_groupoid (Tensor' q r).
    Proof.
      intros q r.
      reflexivity.
    Qed. 

    Definition Lolli : QType -> QType -> QType.
    Proof.
      apply quotient1_map2 with (f := Lolli') (map_cell := @U_lolli).
      apply @U_lolli_compose.
    Defined.
    Lemma Lolli_point : forall q r,
          Lolli (point U_groupoid q) (point U_groupoid r) = point U_groupoid (Lolli' q r).
    Proof.
      intros q r.
      reflexivity.
    Qed.
    Definition Qubit : QType := point U_groupoid Qubit'.
    Definition Lower τ `{IsHSet τ} : QType := point U_groupoid (Lower' τ).


Lemma QUnitary_eq : forall {Q1 Q2} (U1 U2 : Matrix Q1 Q2),
                  U1 = U2 -> cell U_groupoid U1 = cell U_groupoid U2.
Proof.
  intros Q1 Q2 U1 U2 eq.
   rewrite eq. reflexivity.
Qed. (* Do we need to go the other way? Does that even make sense? *)
     (* No, we would need [U : QTy Q1 = QTy Q2] = ||Matrix Q1 Q2|| *)

Fixpoint to_classical' (q : QType') : QType' :=
  match q with
  | Qubit'        => Lower' Bool
  | Tensor' q1 q2 => Tensor' (to_classical' q1) (to_classical' q2)
  | Lolli'  q1 q2 => Lolli' (to_classical' q1) (to_classical' q2)
  | Lower' τ _    => Lower' τ
  end.

(* Note: to_classical' q should always correspond to a 1-dimensional vector
space, so the resuling matrix will always just be the identity matrix. *)
Axiom to_classical_map_cell : forall q r, 
      Matrix q r -> Matrix (to_classical' q) (to_classical' r).
Axiom to_classical_map_compose : 
      forall (x y z : QType') (f : Matrix x y) (g : Matrix y z),
  to_classical_map_cell x z (g o f) =
  to_classical_map_cell y z g o to_classical_map_cell x y f.
Definition to_classical : QType -> QType.
Proof.
  apply quotient1_map with (f := to_classical') 
                           (map_cell := to_classical_map_cell).
  apply to_classical_map_compose.
Defined.

Section to_classical_tensor.

  Let P0 := fun q r => 
             to_classical (Tensor q r) = Tensor (to_classical q) (to_classical r).
  Let P0_HSet : forall q r, IsHSet (P0 q r).
  Proof.
    intros q r.
    unfold P0.
    exact _.
  Defined.
  Let P0_point : forall q r, P0 (point _ q) (point _ r).
  Proof.
    intros q r.
    reflexivity. 
  Defined.

(*    
  Let P0_cell_l : forall q q' r (U : Matrix q q'),
                   transport P0 (cell U_groupoid U) (P0_point q r) = P0_point q' r.
  Let (P0_cell_r : forall q r r' (A : Matrix r r'),
                   cell f # P0_point q r = P0_point q r'.
*)
  Lemma to_classical_tensor : forall q r,
        to_classical (Tensor q r) = Tensor (to_classical q) (to_classical r).
  Proof.

    apply quotient1_ind2_set with (P_point := P0_point); auto.
    * intros. admit.
    * intros. unfold P0_point. admit.
  Admitted.

End to_classical_tensor.
 
  Lemma to_classical_lolli : forall q r,
        to_classical (Lolli q r) = Lolli (to_classical q) (to_classical r).
  Admitted.
  

(*
Instance to_classical_is_trunc `{Funext} : forall q, IsHSet (to_classical' q).
Proof.
  induction q; intros; auto.
  * simpl. apply hset_bool.
  * simpl. exact _. 
  * simpl. apply trunc_arrow. (* need Funext for this *)
Defined.

Definition to_classical_1type `{Funext} (q : QType') : TruncType 0 :=
  {| trunctype_type := to_classical' q |}.
    
(* Can't prove this from the axioms we have, but is reasonable *)
Axiom to_classical_cell : forall `{Funext} {q r} (U : Matrix q r), 
    to_classical_1type q = to_classical_1type r.
Axiom to_classical_linear : 
      forall `{Funext} {q r s} (U : Matrix q r) (V : Matrix r s),
      to_classical_cell (V o U) = to_classical_cell U @ to_classical_cell V.

(* need univalence to show that HSet is a 0-type (aka an hSet) *)
Definition to_classical_hSet `{Univalence} `{Funext} : QType -> hSet.
Proof.
  apply quotient1_rec with (C_point := @to_classical_1type _) 
                           (C_cell := @to_classical_cell _).
  -- apply @to_classical_linear.
  -- exact _.
Defined.
Definition to_classical `{Univalence} `{Funext} (q : QType) : Type :=
  to_classical_hSet q.
*)



Definition toUnitary : QType -> QType'.
Proof.
  apply quotient1_rec_set with (C_point := fun Q => Q); [ | apply QType'_HSet].
  (* this is only true up to asssociativity/commutativity *)
  (* or maybe Matrix can be more restrictive *)
Abort.

End QType.

Infix "⊗" := Tensor (at level 40).
Infix "⊸" := Lolli (at level 40).

(* I think this property should be true.. *)
Lemma lolli_inv : forall q q' r r',
      q ⊸ r = q' ⊸ r' ->
      q = q' /\ r = r'.
Admitted.
