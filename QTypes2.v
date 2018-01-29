Require Import HoTT.
Require Import quotient1.
Require Import Groupoid.
Require Import Matrix2.


Section QTypes.
Context `{Univalence}.


Inductive QType' :=
| One' : QType'
| OPlus' : QType' -> QType' -> QType'
| Tensor' : QType' -> QType' -> QType'
| Lower' (τ : Type) `{IsHSet τ} : QType'
.

Fixpoint Basis' (q : QType') : Type :=
  match q with
  | One'          => Unit
  | OPlus' q1 q2  => Basis' q1 + Basis' q2
  | Tensor' q1 q2 => Basis' q1 * Basis' q2
  | Lower' τ _    => τ
  end.
Instance Basis'_HSet q : IsHSet (Basis' q).
Proof.
  induction q; try (exact _).
Defined.



Section Q_groupoid.

  Inductive Unitary : QType' -> QType' -> Type :=
  | MkU {q} (U : Matrix (Basis' q) (Basis' q)) : UnitaryProp U -> Unitary q q.

  Definition Unitary' (q r : QType') := UMatrix (Basis' q) (Basis' r).
  Instance Unitary'_refl : Reflexive Unitary'.
  Proof.
    intros q. unfold Unitary'. apply UMatrix_refl.
  Defined.
  Instance Unitary'_sym : Symmetric Unitary'.
  Proof.
    intros q r. unfold Unitary'. apply UMatrix_sym.
  Defined.
  Instance Unitary'_trans : Transitive Unitary'.
  Proof.
    intros q r s. unfold Unitary'. apply UMatrix_trans.
  Defined.

  Instance list_Trunc n A `{IsTrunc n A} : IsTrunc n (list A).
  Admitted.

  Instance Vector_HSet {I} `{IsHSet I} : IsHSet (Vector I).
  Proof.
    exact _.
  Qed.
  Instance Matrix_HSet {I J} `{IsHSet I} `{IsHSet J} : IsHSet (Matrix I J).
  Admitted. (* how to prove things about record constructors? *)
  Instance UnitaryProp_HProp : forall I J `{IsHSet I} `{IsHSet J} (A : Matrix I J), 
          IsHProp (UnitaryProp A).
  Proof.
    intros.
  Admitted.
  Instance UMatrix_HSet : forall I J `{IsHSet I} `{IsHSet J}, IsHSet (UMatrix I J).
  Proof.
    exact _.
  Qed.
  Instance Unitary'_HSet : forall q r, IsHSet (Unitary' q r).
  Proof.
    exact _.
  Defined.

  Definition Q_groupoid : groupoid _ Unitary'.
  Proof.
    constructor; intros; unfold Unitary' in *.
    * apply (g_1_l U_groupoid).
    * apply (g_1_r U_groupoid).
    * apply (g_assoc U_groupoid).
    * apply (g_V_r U_groupoid).
    * apply (g_V_l U_groupoid).
  Defined.

  Definition U_tensor {q r q' r'} (U : Unitary' q r) (V : Unitary' q' r')
             : Unitary' (Tensor' q q') (Tensor' r r') :=
    UMatrix_kron _ _ _ _ U V.
  Definition U_plus {q r q' r'} (U : Unitary' q r) (V : Unitary' q' r')
             : Unitary' (OPlus' q q') (OPlus' r r') :=
    UMatrix_plus _ _ _ _ U V.
  Open Scope groupoid_scope.
  Lemma U_tensor_compose : forall q r s q' r' s' 
                                  (U1 : Unitary' q r) (U2 : Unitary' r s)
                                  (V1 : Unitary' q' r') (V2 : Unitary' r' s'),
    U_tensor (U2 o U1) (V2 o V1) = (U_tensor U2 V2) o (U_tensor U1 V1).
  Admitted.
  Lemma U_plus_compose : forall q r s q' r' s' 
                                  (U1 : Unitary' q r) (U2 : Unitary' r s)
                                  (V1 : Unitary' q' r') (V2 : Unitary' r' s'),
    U_plus (U2 o U1) (V2 o V1) = (U_plus U2 V2) o (U_plus U1 V1).
  Admitted.



End Q_groupoid.


Section QType.

  Open Scope groupoid_scope.
  Existing Instance Unitary'_HSet.
  
  Definition QType := quotient1 Q_groupoid.

  Definition Tensor : QType -> QType -> QType.
  Proof.
    apply quotient1_map2 with (f := Tensor') (map_cell := @U_tensor).
    apply @U_tensor_compose.
  Defined.
  Lemma Tensor_point : forall q r, 
        Tensor (point Q_groupoid q) (point Q_groupoid r) 
      = point Q_groupoid (Tensor' q r).
  Proof.
    intros q r.
    reflexivity.
  Qed. 

  Definition Tensor_cell {q1 q2 r1 r2} 
             (U1 : Unitary' q1 r1) (U2 : Unitary' q2 r2) :
             ap2 Tensor (cell _ U1) (cell _ U2) = cell _ (U_tensor U1 U2).
  Proof.
    apply quotient1_map2_cell.
  Qed.


  Lemma OPlus : QType -> QType -> QType.
  Proof.
    apply quotient1_map2 with (f := OPlus') (map_cell := @U_plus).
    apply @U_plus_compose.
  Defined.

  Lemma OPlus_point : forall q r,
      OPlus (point Q_groupoid q) (point Q_groupoid r)
    = point Q_groupoid (OPlus' q r).
  Proof. reflexivity.
  Qed.
  Lemma OPlus_cell : forall {q1 q2 r1 r2} 
                    (U1 : Unitary' q1 r1) (U2 : Unitary' q2 r2),
    ap2 OPlus (cell _ U1) (cell _ U2) = cell _ (U_plus U1 U2).
  Proof.
    intros.
    apply quotient1_map2_cell.
  Qed.

  Definition One : QType := point Q_groupoid One'.
  Definition Lower τ `{IsHSet τ} : QType := point Q_groupoid (Lower' τ).
  
  Definition Qubit : QType := Lower Bool.
End QType.


Infix "⊗" := Tensor (at level 40).
Infix "⊕" := OPlus (at level 40).

Section QBasis.
  Existing Instance Unitary'_HSet.

  Definition QBasis' (q' : QType') := Lower (Basis' q').
  Definition QBasis_cell {q' r'} : Unitary' q' r' -> QBasis' q' = QBasis' r'. 
  Proof.
    intros U'.
    unfold QBasis'.
    apply cell.
    unfold Unitary' in *.
    simpl.
    exact U'.
  Defined.

  Open Scope groupoid_scope.
  Existing Instance Unitary'_trans.

  Arguments cell {A R R_HSet reflR transR symmR} G x y.
  Arguments cell_compose {A R R_HSet reflR transR symmR} G x y z.

  Definition QBasis_compose : forall q r s (U : Unitary' q r) (V : Unitary' r s),
    QBasis_cell (V o U) = QBasis_cell U @ QBasis_cell V.
  Proof.
    intros q r s U V.
    unfold QBasis_cell.
    apply (cell_compose Q_groupoid (Lower' (Basis' q)) 
                                   (Lower' (Basis' r)) 
                                   (Lower' (Basis' s))).
  Defined.

  Definition QBasis : QType -> QType.
  Proof.
    apply quotient1_rec with (C_point := QBasis')
                             (C_cell := @QBasis_cell).
    * apply QBasis_compose.
    * exact _.
  Defined.

  Lemma transport_QBasis : forall {q r} (U : q = r) (V : QBasis q = q),
    transport (fun s => QBasis s = s) U V = ap QBasis (U^) @ V @ U.
  Proof.
    destruct U; intros V.
    simpl.
    Search (1 @ _)%path.
    refine ((concat_1p _)^ @ (concat_p1 _)^).
  Defined.
    

  Section QINIT.
    Existing Instance UMatrix_refl.
    Existing Instance Unitary'_sym.
    Existing Instance UMatrix_sym.

    Let QINIT_type q := QBasis q = q.

    Instance QINIT_type_1Type : forall q, IsTrunc 0 (QINIT_type q).
    Proof.
      intros.
      unfold QINIT_type.
      exact _.
    Defined.

    Let QINIT_point (q' : QType') : QINIT_type (point _ q').
    Proof.
      exact (cell Q_groupoid (Lower' (Basis' q')) q' 1).
    Defined.
    Let QINIT_cell q' r' (U : Unitary' q' r') :
      transport _ (cell _ q' r' U) (QINIT_point q') = QINIT_point r'.
    Proof.
      unfold QINIT_type, QINIT_point.
      rewrite transport_QBasis.
      rewrite quotient1_inv.
      rewrite quotient1_rec_cell.
      unfold QBasis_cell.
      repeat rewrite <- cell_compose.
      apply ap.
      unfold Unitary' in U.
      refine (_ @ (UMatrix_V_r _ _ U)).
      unfold Unitary'_trans, Unitary'_sym.
      apply (ap (fun (V : UMatrix (Basis' r') (Basis' q')) => 
                     UMatrix_trans _ _ _ V U)).
      set (H' := g_1_l Q_groupoid U^).
      simpl in *. unfold Unitary'_trans, Unitary'_refl in H'.
      exact H'.
    Defined. 


    Definition QINIT : forall q, QBasis q = q.
    Proof.
      apply quotient1_ind_set with (P_point := QINIT_point).
      * exact _.
      * apply QINIT_cell.
    Defined.

    Lemma QINIT_compose : forall q r (U : q = r),
        QINIT q @ U = ap QBasis U @ QINIT r.
    Proof.
      destruct U.
      simpl. 
      refine (concat_p1 _ @ (concat_1p _)^).
    Qed.

  End QINIT.


  Arguments cell {A R R_HSet reflR transR symmR} G {x y}.
  Arguments cell_compose {A R R_HSet reflR transR symmR} G {x y z}.


End QBasis.

(*
Section Basis.
  Existing Instance Unitary'_trans. 
  Existing Instance Unitary'_refl.
  Existing Instance Unitary'_sym.
  Existing Instance Unitary'_HSet.
  Existing Instance Basis'_HSet.


  Definition Basis'_hset (q : QType') : hSet.
    exists (Basis' q).
    apply Basis'_HSet.
  Defined.


  Existing Instance UMatrix_HSet.
  Definition HMatrix : hSet -> hSet -> Type := UMatrix. 
  Instance hmatrix_refl : Reflexive HMatrix.
  Proof.
    intros I.
    apply UMatrix_refl.
  Defined.
  Instance hmatrix_sym : Symmetric HMatrix.
  Proof.
    intros I J U.
    apply UMatrix_sym. exact U.
  Defined.
  Instance hmatrix_trans : Transitive HMatrix.
  Proof.
    intros I J K U V.
    apply (UMatrix_trans _ _ _ U V).
  Defined.
  Lemma U_groupoid_hset : groupoid hSet HMatrix.
  Admitted.

  Lemma Basis_cell : forall q r, Unitary' q r  ->
                                 HMatrix (Basis'_hset q) (Basis'_hset r).
  Proof.
    intros q r U.
    exact U.
  Defined.
 About quotient1.

    
  Definition Basis'' (q : QType') := quotient1 (Basis' q) U_groupoid. ???




  Inductive Basis (q : QType) : Type :=
  | basis {q' : QType'} (U : q = point _ q') (b : Basis' q') : Basis q.

  Definition Basis_Lower_fun {α} `{IsHSet α} : Basis (Lower α) -> α.
  Proof.
    destruct 1.  
(*
  Inductive Basis : QType -> Type :=
  | basis {q : QType'} : Basis' q -> Basis (point _ q).
*)
(*  | Basis_Tensor {q r} : Basis q -> Basis r -> Basis (q ⊗ r)
  | Basis_OPlus_l {q r} : Basis q -> Basis (q ⊕ r)
  | Basis_OPlus_r {q r} : Basis r -> Basis (q ⊕ r)
  | Basis_Lower α `{IsHSet α} : α -> Basis (Lower α).*)

(*
I want U # (b : Basis q) : Basis r
So I don't want Basis q = Basis r.

e.g. H # (put b) <> b
     so I don't want (H # Basis Qubit) = Basis Qubit
*)

(* maybe not...
  Lemma Basis_inv : forall q' q (b : Basis q) (U : point _ q' = q), 
    {x : Basis' q' & b = U # basis x}.
  Proof.
    intros q' q b. destruct U. simpl.
    destruct b. intros U. 
   
    assert (b' : Basis' q').
    { 
    }

    set (P := fun q => forall (b : Basis q) (U : point _ q' = q), 
              {x : Basis' q' & b = U # basis x}).
    change (forall q, P q).
    transparent assert (P_point' : (forall q0, P (point _ q0))).
    { intros q0. unfold P. intros B U.
    }
    apply quotient1_ind with (P_point :=

*)

  Lemma Basis_Lower α `{IsHSet α} : Basis (Lower α) = α.
  Proof.
    apply path_universe_uncurried.
    transparent assert (f : (Basis (Lower α) -> α)).
    { unfold Lower.
     }
    exists f.

(*
  
  Definition Basis'_cell' : forall q r (U : Unitary' q r), 
             Basis' q = Basis' r.
  Proof.
    intros.
    unfold Unitary' in U.
    destruct U as [U pfU].
    apply (square _ pfU).
  Qed.
  Definition Basis'_cell : forall q r (U : Unitary' q r), 
             Basis'_hset q = Basis'_hset r.
  Proof.
    intros.
    unfold Basis'_hset.
  Admitted.

  Lemma Basis'_compose : forall (x y z : QType') (f : Unitary' x y) (g : Unitary' y z),
  Basis'_cell x z (g o f)%groupoid = Basis'_cell x y f @ Basis'_cell y z g.
  Admitted.

  Definition Basis_hset : QType -> hSet.
  Proof. 
    apply quotient1_rec with (C_point := Basis'_hset)
                             (C_cell := Basis'_cell).
    * apply Basis'_compose.
    * exact _.
  Defined.
  Definition Basis (q : QType) : Type := Basis_hset q.
*)

  Notation "[[ A ]]" := (point U_groupoid_hset (BuildhSet A)).
  Definition hset_prod (A B : hSet) : hSet := BuildhSet (A * B).

  Existing Instance UMatrix_trans.
  Lemma UMatrix_kron_bilinear : forall a1 a2 a3 b1 b2 b3 a23 b23 b12 a12,
    UMatrix_kron a1 a3 b1 b3 (a23 o a12)%groupoid (b23 o b12)%groupoid =
  (UMatrix_kron a2 a3 b2 b3 a23 b23 o UMatrix_kron a1 a2 b1 b2 a12 b12)%groupoid.
  Admitted.

  Definition qhset_prod (A B : quotient1 U_groupoid_hset)
                     : quotient1 U_groupoid_hset.
    transparent assert (map_cell0 : (forall a a' b b', 
            HMatrix a a' -> 
            HMatrix b b' ->
            HMatrix (hset_prod a b) (hset_prod a' b'))).
    {
      intros a a' b b' U V.
      apply (UMatrix_kron _ _ _ _ U V).
    }
    generalize dependent A. generalize dependent B.
    apply quotient1_map2 with (f := hset_prod)
                              (map_cell := map_cell0).
    { intros. unfold map_cell0. apply UMatrix_kron_bilinear.
    }
  Defined.
  Definition qset_sum (A B  : quotient1 U_groupoid_hset)
                     : quotient1 U_groupoid_hset.
  Admitted.

  Notation "A × B" := (qhset_prod A B) (at level 30).
  Notation "A ⧺ B" := (qset_sum A B) (at level 30).

  Lemma Basis_Unit : Basis One = [[ Unit ]].
  Proof.
    reflexivity.
  Qed.

  Lemma Basis_Tensor : forall q r, Basis (q ⊗ r) = Basis q × Basis r.
  Proof. 
    assert (b_point : forall (q' r' : QType'),
        Basis (point _ (Tensor' q' r')) = Basis (point _ q') × Basis (point _ r')).
    admit (*
    { intros. unfold Basis. unfold quotient1_map. simpl.
      unfold Basis'_hset. simpl.
      unfold qhset_prod. unfold quotient1_map2. 
      unfold quotient1_rec2. simpl.
      apply ap.
      unfold hset_prod. simpl.
      admit (* huh, how did that happen? *).
    }
*).
    apply quotient1_ind2_set with (P_point := b_point).
    * intros. exact _.
    * intros. admit.
    * admit.
  Admitted.

  Lemma Basis_OPlus : forall q r, Basis (q ⊕ r) = Basis q ⧺ Basis r.
  Admitted.

  Lemma Basis_Lower : forall τ `{IsHSet τ}, Basis (Lower τ) = [[τ]].
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma Plus_Bool_equiv : Unit + Unit <~> Bool.
  Admitted.

  Lemma Basis_Qubit : Basis Qubit = [[Bool]].
  Admitted.

End Basis.
*)


Section QType_ind.

(*  Context `{Funext}.*)
  Variable P : QType -> Type.
  Variable P_1Type : forall q, IsTrunc 1 (P q).

  Variable P_One : P One.
  Variable P_Tensor : forall q1 q2, P q1 -> P q2 -> P (q1 ⊗ q2).
  Variable P_OPlus : forall q1 q2, P q1 -> P q2 -> P (q1 ⊕ q2).
  Variable P_Lower : forall τ `{IsHSet τ}, P (Lower τ).

  Lemma QType_point : forall q, P (point _ q).
  Proof.
    induction q.
    * apply P_One.
    * set (IH := P_OPlus _ _ IHq1 IHq2).
      exact IH.
    * set (IH := P_Tensor _ _ IHq1 IHq2).
      exact IH.
    * apply P_Lower.
  Defined.


  Variable QType_cell : forall {q r} (U : Unitary' q r),
           cell _ U # QType_point q = QType_point r.

  Variable QType_compose : forall q r s (U : Unitary' q r) (V : Unitary' r s),
    QType_cell _ _ (V o U)%groupoid 
      = transport2 P (cell_compose _ U V) (QType_point q)
      @ ((transport_pp P (cell _ U) (cell _ V) (QType_point q)
      @ ap (transport P (cell _ V)) (QType_cell _ _ U))
      @ QType_cell _ _ V).
  
  Lemma QType_ind : forall q, P q.
  Proof.
    apply quotient1_ind with (P_point := QType_point)
                             (P_cell := @QType_cell).
    * exact P_1Type.
    * intros q r s U V.
      apply QType_compose.
  Defined.

End QType_ind.

Section QType_rec.

(*  Context `{Funext}.*)
  Variable C : Type.
  Variable C_1Type : IsTrunc 1 C.

  Variable C_One : C.
  Variable C_Tensor : C -> C -> C.
  Variable C_OPlus : C -> C -> C.
  Variable C_Lower : forall τ `{IsHSet τ}, C.

  Fixpoint QType_point_rec (q : QType') : C :=
    match q with
    | One' => C_One
    | Tensor' q1 q2 => C_Tensor (QType_point_rec q1) (QType_point_rec q2)
    | OPlus' q1 q2 => C_OPlus (QType_point_rec q1) (QType_point_rec q2)
    | Lower' τ _ => C_Lower τ _
    end.

  Variable QType_cell : forall {q r} (U : Unitary' q r),
    QType_point_rec q = QType_point_rec r.
  
  Existing Instance Unitary'_trans.
  Variable QType_compose : forall (x y z : QType') 
                                  (f : Unitary' x y) (g : Unitary' y z),
  QType_cell x z (g o f)%groupoid = QType_cell x y f @ QType_cell y z g.

  Lemma QType_rec : QType -> C.
  Proof.
    apply quotient1_rec with (C_point := QType_point_rec)
                             (C_cell := QType_cell).
    * apply QType_compose.
    * apply C_1Type.
  Defined.

End QType_rec.

(*
Section PQType.

  (******************)
  (* Partial QTypes *)
  (******************)
(*  Context `{Funext}.*)


  Inductive PQType :=
  | Hole : QType -> PQType
  | POne : PQType
  | PTensor : PQType -> PQType -> PQType
  | POPlus : PQType -> PQType -> PQType
  | PLower τ `{IsHSet τ} : PQType
  .

  Instance pqtype_hset : IsTrunc 1 PQType.
  Admitted.

  Fixpoint from_PQType (q : PQType) : QType.
    destruct q as [q | | q1 q2 | q1 q2 | τ pf_τ].
    * exact q.
    * exact One.
    * exact (from_PQType q1 ⊗ from_PQType q2).
    * exact (from_PQType q1 ⊕ from_PQType q2).
    * exact (Lower τ).
  Defined.

  Fixpoint to_PQType' (q : QType') : PQType :=
    match q with
    | One' => POne
    | Tensor' q1 q2 => PTensor (to_PQType' q1) (to_PQType' q2)
    | OPlus' q1 q2 => POPlus (to_PQType' q1) (to_PQType' q2)
    | Lower' τ _ => PLower τ
    end.
  Lemma to_PQType_cell : forall q r (U : Unitary' q r),
    to_PQType' q = to_PQType' r.
  Abort. (* Not true because PQType do not have higher structure *)
  
  (*
  Definition to_PQType : QType -> PQType.
  Proof.
    apply quotient1_rec with (C_point := to_PQType')
  *)

  Section PBasis.

    Variable Var : QType -> Type.
    Fixpoint PBasis (q : PQType) : Type.
      destruct q as [q | | q1 q2 | q1 q2 | τ pf_τ].
      * exact (Var q).
      * exact Unit.
      * exact (PBasis q1 * PBasis q2).
      * exact (PBasis q1 + PBasis q2).
      * exact τ.
    Defined.
  End PBasis.


  Definition basis_pbasis {q} : Basis (from_PQType q) -> PBasis Basis q.
  Proof.
    induction q.
    * exact (fun x => x).
    * simpl. exact (fun x => x).
    * simpl. intros z.
      set (z' := transport (fun x => x) (Basis_Tensor _ _) z).
      destruct z' as [x y].
      exact (IHq1 x, IHq2 y).
    * simpl. intros z.
      set (z' := transport (fun x => x) (Basis_OPlus _ _) z).
      destruct z' as [x | y].
      + exact (inl (IHq1 x)).
      + exact (inr (IHq2 y)).
    * simpl. 
      exact (fun x => x).
  Defined.

  Definition pbasis_basis {q} : PBasis Basis q -> Basis (from_PQType q).
  Proof.
    induction q.
    * exact (fun x => x).
    * simpl. exact (fun x => x).
    * simpl. intros [x y].
      apply (transport (fun x => x) (Basis_Tensor _ _)^).
      exact (IHq1 x, IHq2 y).
    * simpl. intros z.
      apply (transport (fun x => x) (Basis_OPlus _ _)^).
      destruct z as [x | y].
      + exact (inl (IHq1 x)).
      + exact (inr (IHq2 y)).
    * simpl. 
      exact (fun x => x).
  Defined.

  Definition pbasis_basis_equiv {q} : PBasis Basis q <~> Basis (from_PQType q).
  Admitted.

  Definition pbasis_basis_fun {p q : PQType} 
                  (f : forall Var, PBasis Var p <~> PBasis Var q) 
                  : Basis (from_PQType p) <~> Basis (from_PQType q).
  Proof.
    set (g := fun x => pbasis_basis (f _ (basis_pbasis x))).
    set (g' := fun x => pbasis_basis ((f _)^-1 (basis_pbasis x))).
    Print IsEquiv.
    assert (pf1 : Sect g' g).
    { intros x. unfold g, g'. admit.
    }
    assert (pf2 : Sect g g') by admit.
    exists g.
    apply (BuildIsEquiv _ _ _ g' pf1 pf2).
    intros x. admit.
  Admitted.

  Definition PBasis_to_Matrix {p q : PQType} 
               (f : forall Var, PBasis Var p <~> PBasis Var q) 
             : Matrix (Basis (from_PQType p)) (Basis (from_PQType q)).
  Proof.
    apply isoToMatrix.
    exact (pbasis_basis_fun f).
  Defined.

(*
  Section basis_inj.
    Lemma Basis'_inj : forall q r, Basis' q = Basis' r -> q = r.
    Admitted (* not sure how to prove effectively *).
    Lemma Basis_inj : forall q r, Basis q = Basis r -> q = r.
    Proof.
      set (P := fun q r => Basis q = Basis r -> q = r).
      change (forall q r, P q r).
      apply quotient1_ind2 with (P_1Type := _).
  End basis_inj.
*)

  Definition PBasis_to_Unitary {p q : PQType}
               (f : forall Var, PBasis Var p <~> PBasis Var q) 
               (pf : UnitaryProp (PBasis_to_Matrix f))
             : from_PQType p = from_PQType q.
  Proof.
(*    destruct pf.

    repeat rewrite <- (path_universe_uncurried pbasis_basis_equiv) in U.
    Existing Instance UMatrix_HSet.
    set (pf' := cell U_groupoid U).
    auto.
  Defined.
*)
  Admitted.

  Definition PQubit := POPlus POne POne.
  Definition X_fun : forall Var, PBasis Var PQubit <~> PBasis Var PQubit.
  Proof.
    intros Var. Locate "_ <~> _". Print Equiv.
    exists (fun z => match z with
                       | inl tt => inr tt
                       | inr tt => inl tt
                       end).
  Admitted.
  (*
  Lemma Fin_PQubit : FinQType (from_PQType PQubit).
  Proof.
    simpl.
    exact _.
  Defined.
  *)
  (* This is slow because it is checking the above theorem *)
  Definition X_mat : Matrix (Unit + Unit) (Unit + Unit) := PBasis_to_Matrix X_fun.

  Lemma X_mat_Unitary : UnitaryProp X_mat.
  Proof.
  Admitted.
  
  Definition X : Qubit = Qubit :=  PBasis_to_Unitary X_fun X_mat_Unitary.


  Definition distr_fun : forall q Var, 
             PBasis Var (PTensor PQubit (Hole q)) <~> PBasis Var (POPlus (Hole q) (Hole q)).
  Proof.
    intros q Var. simpl.
    exists (fun z => match z with
                     | (inl tt, v) => inl v
                     | (inr tt, v) => inr v
                     end).
    admit.
  Admitted.

(*
  Definition distr_mat (q : QType) 
             : Matrix ((Unit+Unit)*Basis q) (Basis q + Basis q).
  Proof.
    set (p1 := PTensor PQubit (Hole q)).
    set (p2 := POPlus (Hole q) (Hole q)).
    set (pf1 := (Basis_Tensor _ _ : Basis (from_PQType p1) = ((Unit+Unit)*Basis q))).
    set (pf2 := (Basis_OPlus _ _ : Basis (from_PQType p2) = (Basis q + Basis q))).
    
    set (M := PBasis_to_Matrix (distr_fun q)).
    rewrite <- pf1, <- pf2.
    exact M.
  Defined.
  Lemma distr_mat_Unitary : forall q `{FinQType q},
        Unitary_Prop (PBasis_to_Matrix (distr_fun q)).
  Admitted.
  Definition distr {q} `{FinQType q} : Qubit ⊗ q = q ⊕ q.
  Proof.
    set (pf := PBasis_to_Unitary (distr_fun q) (distr_mat_Unitary q)).
    simpl in pf.
    exact pf.
  Defined.
*)
  

End PQType.*)
End QTypes.

Infix "⊗" := Tensor (at level 40).
Infix "⊕" := OPlus (at level 40).
