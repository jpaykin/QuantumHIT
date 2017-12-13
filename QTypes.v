Require Import HoTT.
Require Import quotient1.
Require Import Groupoid.


Section QType.

  Inductive QType' :=
  | Qubit'
  | Tensor' (Q1 Q2 : QType')
  | Lolli' (Q1 Q2 : QType')
  | Lower' : forall (τ : Type), QType'
  .

Section QType_dec.


  Definition QType'_code (q1 q2 : QType') : Type :=
    match q1, q2 with
    | Qubit', Qubit' => True
    | Tensor' q11 q12, Tensor' q21 q22 => (q11 = q21) * (q12 = q22)
    | Lolli' q11 q12, Lolli' q21 q22 => (q11 = q21) * (q12 = q22)
    | Lower' τ1, Lower' τ2 => τ1 = τ2
    | _, _ => Empty
    end.

  Lemma Qubit_Tensor_inv : forall q1 q2, Qubit' <> Tensor' q1 q2.
  Proof.
    intros q1 q2 H.
    set (P := QType'_code Qubit').
    apply (transport P H tt).
  Qed.
  Lemma Qubit_Lolli_inv : forall q1 q2, Qubit' <> Lolli' q1 q2.
  Proof.
    intros q1 q2 H.
    set (P := QType'_code Qubit').
    apply (transport P H tt).
  Qed.
  Lemma Qubit_Lower_inv : forall τ, Qubit' <> Lower' τ.
  Proof.
    intros τ H.
    set (P := QType'_code Qubit').
    apply (transport P H tt).
  Qed.
  Lemma Tensor_Tensor_inv : forall q1 q2 q1' q2', Tensor' q1 q2 = Tensor' q1' q2' ->
    (q1 = q1') * (q2 = q2').
  Proof.
    intros q1 q2 q1' q2' H.
    apply (transport (QType'_code (Tensor' q1 q2)) H (1,1)%path).
  Qed.
  Lemma Tensor_Lolli_inv : forall q1 q2 q1' q2', Tensor' q1 q2 <> Lolli' q1' q2'.
  Proof.
    intros q1 q2 q1' q2' H.
    apply (transport (QType'_code (Tensor' q1 q2)) H (1,1)%path).
  Qed.
  Lemma Tensor_Lower_inv : forall q1 q2 τ, Tensor' q1 q2 <> Lower' τ.
  Proof.
    intros q1 q2 τ H.
    apply (transport (QType'_code (Tensor' q1 q2)) H (1,1)%path).
  Qed.
  Lemma Lolli_Lolli_inv : forall q1 q2 q1' q2', Lolli' q1 q2 = Lolli' q1' q2' ->
    (q1 = q1') * (q2 = q2').
  Proof.
    intros q1 q2 q1' q2' H.
    apply (transport (QType'_code (Lolli' q1 q2)) H (1,1)%path).
  Qed.
  Lemma Lolli_Lower_inv : forall q1 q2 τ, Lolli' q1 q2 <> Lower' τ.
  Proof.
    intros q1 q2 τ H.
    apply (transport (QType'_code (Lolli' q1 q2)) H (1,1)%path).
  Qed.
  Lemma Lower_Lower_inv : forall (τ1 τ2 : Type),
    Lower' τ1 = Lower' τ2 -> τ1 = τ2.
  Proof.
    intros τ1 τ2 H.
    apply (transport (QType'_code (Lower' τ1)) H 1%path).
  Qed.
    
(*
  Instance QType'_DecPaths  : DecidablePaths QType'.
  Proof.
    unfold DecidablePaths.
    intros q1.
    induction q1 as [ | q11 H11 q12 | q11 H11 q12 | τ1 H1];
    intros q2; destruct q2 as [ | q21 q22 | q21 q22 | τ2 H2].
    * left. exact 1%path.
    * right. apply Qubit_Tensor_inv.
    * right. apply Qubit_Lolli_inv.
    * right. apply Qubit_Lower_inv.
    * right. intros H; apply (Qubit_Tensor_inv _ _ H^).
    * destruct (H11 q21) as [eq1 | neq1], (IHq12 q22) as [eq2 | neq2].
      + left. transitivity (Tensor' q11 q22).
        - apply ap. exact eq2.
        - apply (ap (fun q => Tensor' q q22)). exact eq1.
      + right. intros H.
        apply Tensor_Tensor_inv in H.
        destruct H.
        contradiction.
      + right. intros H.
        apply Tensor_Tensor_inv in H.
        destruct H.
        contradiction.
      + right. intros H.
        apply Tensor_Tensor_inv in H.
        destruct H.
        contradiction.
    * right. apply Tensor_Lolli_inv.
    * right. apply Tensor_Lower_inv.
    * right. intros H. apply (Qubit_Lolli_inv _ _ H^).
    * right. intros H. apply (Tensor_Lolli_inv _ _ _ _ H^).
    * destruct (H11 q21) as [eq1 | neq1], (IHq12 q22) as [eq2 | neq2].
      + left. transitivity (Lolli' q11 q22).
        - apply ap. exact eq2.
        - apply (ap (fun q => Lolli' q q22)). exact eq1.
      + right. intros H.
        apply Lolli_Lolli_inv in H.
        destruct H.
        contradiction.
      + right. intros H.
        apply Lolli_Lolli_inv in H.
        destruct H.
        contradiction.
      + right. intros H.
        apply Lolli_Lolli_inv in H.
        destruct H.
        contradiction.
    * admit.
    * admit.
    * admit.
    * admit.
    *
*)
      
End QType_dec.

(*
  Global Instance QType'_HSet : IsHSet QType'.
  Proof.
    intros q1 q2. 
    destruct q1; destruct q2.
    * simpl. intros pf1 pf2. Search (IsTrunc _ (TruncType _))..
    intros. admit.
    
  Admitted.
*)

  Fixpoint size_QType' (q : QType') : nat :=
    match q with
    | Qubit' => 2
    | Tensor' Q1 Q2 => size_QType' Q1 * size_QType' Q2
    | Lolli' Q1 Q2  => size_QType' Q1 * size_QType' Q2
    | Lower' τ => 0
    end.

  (* These are axioms because I don't want to deal with actual vector spaces and
  unitary transformations quite yet. They should not be axiomatic in the end. *)

  Axiom Matrix : nat -> nat -> Type.
  Axiom M_HSet : forall n1 n2, IsHSet (Matrix n1 n2).
  Axiom Unitary_Prop : forall {m n}, Matrix m n -> Type.
  Axiom Uniary_Prop_Set : forall m n (A : Matrix m n),
      IsHProp (Unitary_Prop A).
  Axiom Unitary_Prop_size : forall {m n} (A : Matrix m n),
      Unitary_Prop A -> m = n.

  Definition UMatrix (q r : QType') := 
    { A : Matrix (size_QType' q) (size_QType' r) & Unitary_Prop A }.

  Axiom M_refl : Reflexive Matrix. (* identity matrices *)
  Axiom M_trans : Transitive Matrix. (* matrix multiplication *)
  Axiom M_symm : Symmetric Matrix. (* matrix (conjugate) transpose *)

  Axiom refl_Unitary : forall n, Unitary_Prop (M_refl n).
  Axiom trans_Unitary : forall m n p (A : Matrix m n) (B : Matrix n p),
    Unitary_Prop A ->
    Unitary_Prop B ->
    Unitary_Prop (transitivity A B).
  Axiom symm_Unitary : forall m n (A : Matrix m n),
    Unitary_Prop A ->
    Unitary_Prop (symmetry _ _ A).

  Axiom M_tensor : forall {x x' y y'} 
                      (U : Matrix x x') (U' : Matrix y y'),
                      Matrix (x * y) (x' * y').
  Axiom M_tensor_Unitary : forall {x x' y y'} 
                      (U : Matrix x x') (U' : Matrix y y'),
        Unitary_Prop U -> Unitary_Prop U' -> Unitary_Prop (M_tensor U U').
  Axiom M_tensor_compose : forall {x1 x2 x3 y1 y2 y3} 
                           (U1 : Matrix x1 x2) (U2 : Matrix x2 x3)
                           (V1 : Matrix y1 y2) (V2 : Matrix y2 y3),
        M_tensor (transitivity U1 U2) (transitivity V1 V2)
      = transitivity (M_tensor U1 V1) (M_tensor U2 V2).

  Global Instance U_HSet : forall q r, IsHSet (UMatrix q r).
  Proof.
    intros q r. 
    apply trunc_sigma.
  Qed.

  Global Instance U_refl : Reflexive UMatrix.
  Proof.
    intros q.
    exists (M_refl _).
    apply refl_Unitary.
  Defined.
  Global Instance U_trans : Transitive UMatrix.
  Proof.
    intros q r s [U pfU] [V pfV].
    exists (transitivity U V).
    apply trans_Unitary; auto.
  Defined.
  Global Instance U_symm : Symmetric UMatrix.
  Proof.
    intros q r [U pfU].
    exists (symmetry _ _ U).
    apply symm_Unitary; auto.
  Defined.

  Local Open Scope groupoid_scope.
  Axiom U_groupoid : groupoid _ UMatrix.

  Definition U_tensor : forall {q q' r r'} (U : UMatrix q q') (V : UMatrix r r'),
             UMatrix (Tensor' q r) (Tensor' q' r').
  Proof.
    intros q q' r r' [U pfU] [V pfV].
    exists (M_tensor U V).
    apply M_tensor_Unitary; auto.
  Defined.
  Lemma U_tensor_compose : forall {q1 q2 q3 r1 r2 r3}
                                  (U1 : UMatrix q1 q2) (U2 : UMatrix q2 q3)
                                  (V1 : UMatrix r1 r2) (V2 : UMatrix r2 r3),
        U_tensor (U2 o U1) (V2 o V1)
      = (U_tensor U2 V2) o (U_tensor U1 V1).
  Admitted.

  Definition QType := quotient1 U_groupoid.
    
  Definition Tensor : QType -> QType -> QType.
  Proof.
    apply quotient1_map2 with (f := Tensor') (map_cell := @U_tensor).
    apply @U_tensor_compose.
  Defined.
  Lemma Tensor_point : forall q r, 
        Tensor (point U_groupoid q) (point U_groupoid r) 
      = point U_groupoid (Tensor' q r).
  Proof.
    intros q r.
    reflexivity.
  Qed. 

  Definition Lolli : QType -> QType -> QType.
  Proof.
    apply quotient1_map2 with (f := Lolli') (map_cell := @U_tensor).
    apply @U_tensor_compose.
  Defined.
  Lemma Lolli_point : forall q r,
     Lolli (point U_groupoid q) (point U_groupoid r) = point U_groupoid (Lolli' q r).
  Proof.
    intros q r.
    reflexivity.
  Qed.
  Definition Qubit : QType := point U_groupoid Qubit'.
  Definition Lower τ : QType := point U_groupoid (Lower' τ).


  Lemma QUnitary_eq : forall {Q1 Q2} (U1 U2 : UMatrix Q1 Q2),
                      U1 = U2 -> cell U_groupoid U1 = cell U_groupoid U2.
  Proof.
    intros Q1 Q2 U1 U2 eq.
    rewrite eq. reflexivity.
  Qed. (* Do we need to go the other way? Does that even make sense? *)
       (* No, we would need [U : QTy Q1 = QTy Q2] = ||UMatrix Q1 Q2|| *)

  Definition size_QType : QType -> nat.
  Proof.
    apply quotient1_rec_set with (C_point := size_QType').
    * intros q r [U pfU].
      apply (Unitary_Prop_size U pfU).
    * exact _.
  Defined.

  Local Open Scope nat_scope.

  Lemma size_Tensor : forall q r, 
        size_QType (Tensor q r) = size_QType q * size_QType r.
  Proof.
    apply quotient1_ind2_set with (P_point := fun _ _ => 1%path).
    * intros. exact _.
    * intros. apply hset_nat.
    * intros. apply hset_nat.
  Qed.
 
  Lemma size_Lolli : forall q r,
        size_QType (Lolli q r) = size_QType q * size_QType r.
  Proof.
    apply quotient1_ind2_set with (P_point := fun _ _ => 1%path).
    * intros. exact _.
    * intros. apply hset_nat.
    * intros. apply hset_nat.
  Qed.

  


(*
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
      UMatrix q r -> UMatrix (to_classical' q) (to_classical' r).
Axiom to_classical_map_compose : 
      forall (x y z : QType') (f : UMatrix x y) (g : UMatrix y z),
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
  Let P0_cell_l : forall q q' r (U : UMatrix q q'),
                   transport P0 (cell U_groupoid U) (P0_point q r) = P0_point q' r.
  Let (P0_cell_r : forall q r r' (A : UMatrix r r'),
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
  
*)


(*
  Fixpoint to_classical' (q : QType') : Type :=
  match q with
  | Qubit'        => Bool
  | Tensor' q1 q2 => (to_classical' q1) * (to_classical' q2)
  | Lolli' q1 q2  => Unit
  | Lower' τ _    => τ
  end.


  Instance to_classical_is_trunc : forall q, IsHSet (to_classical' q).
  Proof.
    induction q; intros; auto.
    * simpl. apply hset_bool.
    * simpl. exact _. 
    * simpl. exact _.
  Defined.

  Definition to_classical_1type (q : QType') : TruncType 0 :=
  {| trunctype_type := to_classical' q |}.
    
(* Can't prove this from the axioms we have, but is reasonable *)
(*  Axiom to_classical_cell : forall {q r} (U : UMatrix q r), 
      to_classical_1type q = to_classical_1type r.*)
(*  Axiom to_classical_linear : 
        forall {q r s} (U : UMatrix q r) (V : UMatrix r s),
        to_classical_cell (V o U) = to_classical_cell U @ to_classical_cell V.*)

(* need univalence to show that HSet is a 0-type (aka an hSet) *)
Definition to_classical_hSet `{Univalence} : QType -> hSet.
Proof.
  apply quotient1_rec with (C_cell := @to_classical_cell).
  -- apply @to_classical_linear.
  -- exact _.
Defined.
Definition to_classical `{Univalence} (q : QType) : Type :=
  to_classical_hSet q.



Definition toUnitary : QType -> QType'.
Proof.
  apply quotient1_rec_set with (C_point := fun Q => Q); [ | apply QType'_HSet].
  (* this is only true up to asssociativity/commutativity *)
  (* or maybe UMatrix can be more restrictive *)
Abort.
*)
End QType.

Infix "⊗" := Tensor (at level 40).
Infix "⊸" := Lolli (at level 40).

(* I think this property should be true *)
Lemma lolli_inv : forall q q' r r',
      q ⊸ r = q' ⊸ r' ->
      q = q' /\ r = r'.
Admitted.

(*
Lemma to_classical_lolli `{Univalence} q r : to_classical (q ⊸ r) = Unit.
Admitted.
Lemma to_classical_tensor `{Univalence} q r : to_classical (q ⊗ r) = (to_classical q) * (to_classical r).
Admitted.
*)


  
