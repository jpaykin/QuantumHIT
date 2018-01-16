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
Qed.



Section Q_groupoid.

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
  Qed.

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
  Lemma OPlus : QType -> QType -> QType.
  Proof.
    apply quotient1_map2 with (f := OPlus') (map_cell := @U_plus).
    apply @U_plus_compose.
  Defined.

  Definition One : QType := point Q_groupoid One'.
  Definition Lower τ `{IsHSet τ} : QType := point Q_groupoid (Lower' τ).
  
  Definition Qubit : QType := OPlus One One.
End QType.


Infix "⊗" := Tensor (at level 40).
Infix "⊕" := OPlus (at level 40).


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

  Lemma Basis_Unit : Basis One = Unit.
  Proof.
    reflexivity.
  Qed.

  Lemma Basis_Tensor : forall q r, Basis (q ⊗ r) = Basis q * Basis r.
  Proof.
    apply quotient1_ind2_set with (P_point := fun _ _ => 1%path).
    * intros. exact _.
    * intros. admit.
    * admit.
  Admitted.

  Lemma Basis_OPlus : forall q r, Basis (q ⊕ r) = Basis q + Basis r.
  Admitted.

  Lemma Basis_Lower : forall τ `{IsHSet τ}, Basis (Lower τ) = τ.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma Plus_Bool_equiv : Unit + Unit <~> Bool.
  Admitted.

  Lemma Basis_Qubit : Basis Qubit <~> Bool.
  Proof.
    unfold Qubit. 
    rewrite Basis_OPlus.
    unfold Basis. simpl.
    apply Plus_Bool_equiv.
  Qed.

End Basis.



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


  Definition PBasis_to_Unitary {p q : PQType}
               `{FinQType (from_PQType p)} `{FinQType (from_PQType q)}
               (f : forall Var, PBasis Var p -> PBasis Var q) 
               (pf : Unitary_Prop (PBasis_to_Matrix f))
             : from_PQType p = from_PQType q.
  Proof.
    apply (toU (pbasis_basis_fun f)).
    auto.
  Defined.

  Definition PQubit := POPlus POne POne.
  Definition X_fun : forall Var, PBasis Var PQubit -> PBasis Var PQubit.
  Proof.
    simpl.
    refine (fun _ z => match z with
                       | inl tt => inr tt
                       | inr tt => inl tt
                       end).
  Defined.
  (*
  Lemma Fin_PQubit : FinQType (from_PQType PQubit).
  Proof.
    simpl.
    exact _.
  Defined.
  *)
  (* This is slow because it is checking the above theorem *)
  Definition X_mat : Matrix (Unit + Unit) (Unit + Unit) := PBasis_to_Matrix X_fun.

  Lemma X_mat_Unitary : Unitary_Prop X_mat.
  Proof.
    unfold Unitary_Prop.
    unfold X_mat.
    unfold PBasis_to_Matrix. simpl.
    unfold to_matrix. 
    unfold Unitary_Prop. simpl.
    constructor.
    * admit.
    * admit.
    * reflexivity.
  Admitted.
  
  Definition X : Qubit = Qubit :=  PBasis_to_Unitary X_fun X_mat_Unitary.


  Definition distr_fun : forall q Var, 
             PBasis Var (PTensor PQubit (Hole q)) -> PBasis Var (POPlus (Hole q) (Hole q)).
  Proof.
    intros q Var. simpl.
    refine (fun z => match z with
                     | (inl tt, v) => inl v
                     | (inr tt, v) => inr v
                     end).
  Defined.

  Definition distr_mat (q : QType) `{FinQType q} 
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
  

End PQType.
End QTypes.

Infix "⊗" := Tensor (at level 40).
Infix "⊕" := OPlus (at level 40).
