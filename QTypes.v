Require Import HoTT.
Require Import quotient1.
Require Import Groupoid.


Section QType.

  Inductive QType' :=
  | Qubit'
  | Tensor' (Q1 Q2 : QType')
(*  | Lolli' (Q1 Q2 : QType') *)
  | Lower' : forall (τ : Type) `{IsHSet τ}, QType'
  .

Section QType_dec.


  Definition QType'_code (q1 q2 : QType') : Type :=
    match q1, q2 with
    | Qubit', Qubit' => True
    | Tensor' q11 q12, Tensor' q21 q22 => (q11 = q21) * (q12 = q22)
(*  | Lolli' q11 q12, Lolli' q21 q22 => (q11 = q21) * (q12 = q22)*)
    | Lower' τ1 _, Lower' τ2 _ => τ1 = τ2
    | _, _ => Empty
    end.

  Lemma Qubit_Tensor_inv : forall q1 q2, Qubit' <> Tensor' q1 q2.
  Proof.
    intros q1 q2 H.
    set (P := QType'_code Qubit').
    apply (transport P H tt).
  Qed.
(*Lemma Qubit_Lolli_inv : forall q1 q2, Qubit' <> Lolli' q1 q2.
  Proof.
    intros q1 q2 H.
    set (P := QType'_code Qubit').
    apply (transport P H tt).
  Qed.*)
  Lemma Qubit_Lower_inv : forall τ `{IsHSet τ}, Qubit' <> Lower' τ.
  Proof.
    intros τ pf H.
    set (P := QType'_code Qubit').
    apply (transport P H tt).
  Qed.
  Lemma Tensor_Tensor_inv : forall q1 q2 q1' q2', Tensor' q1 q2 = Tensor' q1' q2' ->
    (q1 = q1') * (q2 = q2').
  Proof.
    intros q1 q2 q1' q2' H.
    apply (transport (QType'_code (Tensor' q1 q2)) H (1,1)%path).
  Qed.
(*Lemma Tensor_Lolli_inv : forall q1 q2 q1' q2', Tensor' q1 q2 <> Lolli' q1' q2'.
  Proof.
    intros q1 q2 q1' q2' H.
    apply (transport (QType'_code (Tensor' q1 q2)) H (1,1)%path).
  Qed.*)
  Lemma Tensor_Lower_inv : forall q1 q2 τ `{IsHSet τ}, Tensor' q1 q2 <> Lower' τ.
  Proof.
    intros q1 q2 τ pf H.
    apply (transport (QType'_code (Tensor' q1 q2)) H (1,1)%path).
  Qed.
(*Lemma Lolli_Lolli_inv : forall q1 q2 q1' q2', Lolli' q1 q2 = Lolli' q1' q2' ->
    (q1 = q1') * (q2 = q2').
  Proof.
    intros q1 q2 q1' q2' H.
    apply (transport (QType'_code (Lolli' q1 q2)) H (1,1)%path).
  Qed.*)
(*Lemma Lolli_Lower_inv : forall q1 q2 τ, Lolli' q1 q2 <> Lower' τ.
  Proof.
    intros q1 q2 τ H.
    apply (transport (QType'_code (Lolli' q1 q2)) H (1,1)%path).
  Qed.*)
  Lemma Lower_Lower_inv : forall (τ1 τ2 : Type) `{IsHSet τ1} `{IsHSet τ2},
    Lower' τ1 = Lower' τ2 -> τ1 = τ2.
  Proof.
    intros τ1 τ2 pf1 pf2 H.
    apply (transport (QType'_code (Lower' τ1)) H 1%path).
  Qed.
    
End QType_dec.

Fixpoint size_QType' (q : QType') : nat :=
  match q with
  | Qubit' => 2
  | Tensor' Q1 Q2 => size_QType' Q1 * size_QType' Q2
(*| Lolli' Q1 Q2  => size_QType' Q1 * size_QType' Q2*)
  | Lower' τ _ => 0
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

(*Definition Lolli : QType -> QType -> QType.
  Proof.
    apply quotient1_map2 with (f := Lolli') (map_cell := @U_tensor).
    apply @U_tensor_compose.
  Defined.
  Lemma Lolli_point : forall q r,
     Lolli (point U_groupoid q) (point U_groupoid r) = point U_groupoid (Lolli' q r).
  Proof.
    intros q r.
    reflexivity.
  Qed.*)
  Definition Qubit : QType := point U_groupoid Qubit'.
  Definition Lower τ `{IsHSet τ} : QType := point U_groupoid (Lower' τ).


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
 
(*Lemma size_Lolli : forall q r,
        size_QType (Lolli q r) = size_QType q * size_QType r.
  Proof.
    apply quotient1_ind2_set with (P_point := fun _ _ => 1%path).
    * intros. exact _.
    * intros. apply hset_nat.
    * intros. apply hset_nat.
  Qed.*)


Close Scope nat_scope.

Section Basis.
  Context `{Univalence}.
  Fixpoint Basis' (q : QType') : Type.
  Proof.
    destruct q.
    * (* Qubit *) exact Bool. 
    * (* Tensor *) exact ((Basis' q1) * (Basis' q2)). 
    * (* Lower *) exact τ.
  Defined.
  Lemma Basis'_ishset : forall q, IsHSet (Basis' q).
  Proof.
    induction q; exact _.
  Qed.

  (* This might be better with a different defn of UMatrix based on Bases *)
  Lemma Basis_cell : forall q r (U : UMatrix q r), Basis' q = Basis' r.
  Proof.
    induction q; destruct r; intros U; simpl.
    * reflexivity.
    * (* Since |r1 ⊗ r2| = 2, either r1 or r2 has size 1, so either 
         U : UMatrix Qubit r1 or U : UMatrix Qubit r2. In the first case,   
         we get Bool = r1 ~ r1 * r2 by univalence, & vice versa *) admit.
    * destruct U as [U pf_U].
      assert (2 <> 0)%nat by admit. 
      apply Empty_rec. apply X. 
      apply (Unitary_Prop_size U pf_U).
    * (* same as case 2 *) 
      admit.
    * (*???*) admit.
    * (* since |q1 ⊗ q2| = 0, it must be the case that |q1|=0 or |q2|=0, 
         *)
  Admitted.

  Definition Basis : QType -> hSet.
  Proof.
    eapply quotient1_rec with (C_point := Basis').
    
    admit. exact _.


    
End Basis.
 
  Definition QData `{Univalence} : QType -> hProp.
  Proof.
    apply quotient1_rec_set with (C_point := QData'').
    * intros q r U. unfold QData''.

      
    * exact _.

  Close Scope nat_scope.


  Definition Basis {q : QType} : QData q -> hSet.
  Proof.
    


  Fixpoint Basis {q} (pf : QData q) : Type.
  Proof.
    destruct pf.
    * exact Bool.
    * exact ((Basis _ pf1) * (Basis _ pf2)).
    * exact τ.
  Defined.

  Lemma Basis_eq : forall q r (pf : QData q) (U : q = r),
    Basis (transport _ U pf) = Basis pf.
  Proof.
    destruct U.
    reflexivity.
  Defined.

  Lemma Basis_eq' : forall q r (pf : QData q) (U : q = r),
    transport _ U (Basis pf) = Basis pf.
  Proof.
    destruct U.
    reflexivity.
  Qed.
  

(*
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


  
