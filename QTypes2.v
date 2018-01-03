Require Import HoTT.
Require Import quotient1.
Require Import Groupoid.


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
  | One' => Unit
  | OPlus' q1 q2 => Basis' q1 + Basis' q2
  | Tensor' q1 q2 => Basis' q1 * Basis' q2
  | Lower' τ _ => τ
  end.

Definition bdec_paths {A} `{DecidablePaths A} (x y : A) : Bool :=
  if dec_paths x y then true else false.
Notation "x =? y" := (dec_paths x y) (at level 25).


Section Matrix.

(*  Context `{Funext}.*)
(*Axiom C : Type.
Axiom nat_to_C : nat -> C.
Coercion nat_to_C : nat >-> C.*)

  Inductive Matrix (I J : Type) := 
  | MkMatrix `{Finite I} `{Finite J} :
              (I -> J -> nat) -> Matrix I J.
  (* Here, nat is a stand-in for C *)
  Arguments MkMatrix {I J} {FinI} {FinJ} f : rename.

  Definition lookupMatrix {I J} (A : Matrix I J) (i : I) (j : J) :=
    match A with
    | MkMatrix _ _ A' => A' i j
    end.
  Notation "A [ i , j ]" := (lookupMatrix A i j) (at level 10).



  Section Id.

    Variable I : Type.
(*    Axiom finI : Finite I. (* how to resolve this?? *)*)
    Definition Id : Matrix I I. (*MkMatrix (fun i i' => if i =? i' then 1 else 0).*)
    Admitted.
  End Id.

  Instance M_refl : Reflexive Matrix := Id.

  Definition Compose {I J K} (A : Matrix I J) (B : Matrix J K) : Matrix I K :=
    match A, B with
    | MkMatrix _ _ A', MkMatrix _ _ B' => 
      MkMatrix (fun i k => finplus (fun (j : J) => (A' i j * B' j k)%nat))
    end.
  Instance M_trans : Transitive Matrix := @Compose.
    

  Definition Transpose {I J} (A : Matrix I J) : Matrix J I :=
    match A with
    | MkMatrix _ _ A' => MkMatrix (fun j i => A' i j) 
    (* for Complex numbers, this should be (A' i j)^† *)
    end.
  Instance M_sym : Symmetric Matrix := @Transpose.

  Open Scope groupoid_scope.
  Record Unitary_Prop' {I J} `{Finite I} `{Finite J} (A : Matrix I J) :=
    { A_A_dag : A^ o A = 1
    ; A_dag_A : A o A^ = 1
    ; U_size  : fcard I = fcard J
    }.
  Definition Unitary_Prop {I J} (A : Matrix I J) := 
    match A with
    | MkMatrix _ _ _ => Unitary_Prop' A
    end.

  Definition Kron {I J I' J'} (A : Matrix I J) (B : Matrix I' J') : Matrix (I * I') (J * J') :=
    match A, B with
    | MkMatrix _ _ _, MkMatrix _ _ _ => MkMatrix (fun (x : I*I') (y : J*J') =>
        let (i,i') := x in
        let (j,j') := y in
        (A [i , j] * B [i' ,j'])%nat
      )
    end.

  Definition DSum {I J I' J'} (A : Matrix I J) (B : Matrix I' J') : Matrix (I + I') (J + J') :=
    match A, B with
    | MkMatrix _ _ _, MkMatrix _ _ _ => MkMatrix (fun (x : I + I') (y : J + J') =>
        match x, y with
        | inl i, inl j => A[i,j]
        | inr i', inr j' => B[i',j']
        | _, _ => 0
        end
    )
    end.

  (* I think this is true... *)
  Global Instance M_decPaths : forall {I J}, DecidablePaths (Matrix I J).
  Proof.
    intros I J [pfI pfJ A] [pfI' pfJ' B].
    assert (Decidable (pfI = pfI')) by exact _.
    assert (Decidable (pfJ = pfJ)) by exact _.
    assert (Decidable (A = B)).
    { admit. (*??*) }
  Admitted.
  (* which means that Matrix I J is an HSet *)

  Global Instance Unitary_Prop_hprop : forall {I J} (A : Matrix I J),
    IsHProp (Unitary_Prop A).
  Proof.
    intros.
    intros pf1 pf2.
    destruct A.
    destruct pf1, pf2.
    assert (Contr (A_A_dag0 = A_A_dag1)) by exact _.
    assert (Contr (A_dag_A0 = A_dag_A1)) by exact _.
    assert (Contr (U_size0 = U_size1)) by exact _.
    assert ({| A_A_dag := A_A_dag0; A_dag_A := A_dag_A0; U_size := U_size0 |}
          = {| A_A_dag := A_A_dag1; A_dag_A := A_dag_A1; U_size := U_size1 |}).
    { admit. }
  (* I think this is true *)
  Admitted.

  (* todo: *)

  Lemma refl_Unitary : forall I, Unitary_Prop (Id I).
  Admitted.

  Lemma trans_Unitary : forall {I J K} (A : Matrix I J) (B : Matrix J K),
    Unitary_Prop A -> Unitary_Prop B -> Unitary_Prop (B o A).
  Admitted.

  Lemma symm_Unitary : forall {I J} (A : Matrix I J),
    Unitary_Prop A -> Unitary_Prop A^.
  Admitted.

  Lemma kron_Unitary : forall {I J I' J'} (A : Matrix I J) (B : Matrix I' J'),
    Unitary_Prop A -> Unitary_Prop B -> Unitary_Prop (Kron A B).
  Admitted.

  Lemma dsum_Unitary : forall {I J I' J'} (A : Matrix I J) (B : Matrix I' J'),
    Unitary_Prop A -> Unitary_Prop B -> Unitary_Prop (DSum A B).
  Admitted.

  Lemma kron_compose : forall {I1 I2 I3 J1 J2 J3}
                              (A1 : Matrix I1 I2) (A2 : Matrix I2 I3)
                              (B1 : Matrix J1 J2) (B2 : Matrix J2 J3),
    Kron (A2 o A1) (B2 o B1) = Kron A2 B2 o Kron A1 B1.
  Admitted.

End Matrix.

Section UMatrix.

  Definition UMatrix (q r : QType') := {A : Matrix (Basis' q) (Basis' r) & Unitary_Prop A}.

  Global Instance U_refl : Reflexive UMatrix.
  Admitted.

  Global Instance U_trans : Transitive UMatrix.
  Admitted.

  Global Instance U_sym : Symmetric UMatrix.
  Admitted.

  Lemma U_groupoid : groupoid _ UMatrix.
  Proof.
    constructor.
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
  Admitted.
  
  Definition U_tensor {q q' r r'} (U : UMatrix q q') (V : UMatrix r r') :
             UMatrix (Tensor' q r) (Tensor' q' r').
  Admitted.

  Open Scope groupoid_scope.

  Lemma U_tensor_compose : forall {q1 q2 q3 r1 r2 r3}
                                  (U1 : UMatrix q1 q2) (U2 : UMatrix q2 q3)
                                  (V1 : UMatrix r1 r2) (V2 : UMatrix r2 r3),
        U_tensor (U2 o U1) (V2 o V1)
      = (U_tensor U2 V2) o (U_tensor U1 V1).
  Admitted.

  Definition U_oplus {q q' r r'} (U : UMatrix q q')(V : UMatrix r r') :
             UMatrix (OPlus' q r) (OPlus' q' r').
  Admitted.

  Lemma U_oplus_compose : forall {q1 q2 q3 r1 r2 r3}
                                 (U1 : UMatrix q1 q2) (U2 : UMatrix q2 q3)
                                 (V1 : UMatrix r1 r2) (V2 : UMatrix r2 r3),
        U_oplus (U2 o U1) (V2 o V1)
      = (U_oplus U2 V2) o (U_oplus U1 V1).
  Admitted.

  Global Instance U_hset : forall {q r}, IsHSet (UMatrix q r).
  Proof.
    intros q r.
    exact _.
  Qed.

End UMatrix.

Section QType.

  Open Scope groupoid_scope.
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
  Lemma OPlus : QType -> QType -> QType.
  Proof.
    apply quotient1_map2 with (f := OPlus') (map_cell := @U_oplus).
    apply @U_oplus_compose.
  Defined.

  Definition One : QType := point U_groupoid One'.
  Definition Lower τ `{IsHSet τ} : QType := point U_groupoid (Lower' τ).
  
  Definition Qubit : QType := OPlus One One.
End QType.


Infix "⊗" := Tensor (at level 40).
Infix "⊕" := OPlus (at level 40).




Section Basis.
(*

  Context `{Univalence}.

  Fixpoint Lowered' (P : Type -> Type) (q : QType') : Type :=
    match q with
    | One' => Unit
    | Tensor' q1 q2 => Lowered' P q1 * Lowered' P q2
    | OPlus' q1 q2 =>  Lowered' P q1 * Lowered' P q2
    | Lower' τ _ => P τ
    end.
  Instance Lowered'_ishprop : forall q, IsHProp (Lowered' IsHSet q).
  Proof.
    induction q; simpl.
    * exact _.
    * exact _.
    * exact _.
    * exact _.
  Qed.
  Definition Lowered'_hprop (q : QType') : hProp.
    exists (Lowered' IsHSet q).
    apply Lowered'_ishprop.
  Defined.

  Lemma finite_lowered : forall q, Finite (Basis' q) -> Lowered' IsHSet q.
  Proof.
    induction q; intros; simpl.
    * exact tt.
    * refine (IHq1 _, IHq2 _).
      admit. admit. (* reasonable *)
    * simpl in X.
      refine (IHq1 _, IHq2 _).
      admit. admit. (* reasonable *)
    * simpl in X.
      exact _.
  Admitted.    

  (* depends on univalence *)
  Lemma finite_lowered_equiv : forall q, Finite (Basis' q) -> 
                                         Lowered' IsHSet q <~> Unit.
  Proof.
    intros.
    apply if_hprop_then_equiv_Unit.
    * apply Lowered'_ishprop.
    * apply finite_lowered; auto.
  Qed.

  (* true since UMatrix q r implies q is finite *)
  Lemma UMatrix_Lowered_eq : forall q r,
    UMatrix q r ->
    Lowered' IsHSet q = Unit.
  Proof.
    intros q r [[pf_q pf_r U] pf_U].
    apply path_universe_uncurried.
    apply finite_lowered_equiv.
    auto.
  Qed.
  Lemma UMatrix_Lowered_eq' : forall q r ,
    UMatrix q r ->
    BuildhProp (Lowered' IsHSet q) = BuildhProp Unit.
  Proof.
  Admitted.

  Definition Lowered : QType -> hProp.
  Proof.    
    apply quotient1_rec_set with (C_point := Lowered'_hprop).
    * intros q r U.
      unfold Lowered'_hprop.
      transitivity (BuildhProp Unit).
      + apply (UMatrix_Lowered_eq' q r U).
      + refine (UMatrix_Lowered_eq' _ _ (U^)%groupoid)^. apply U_sym.
    * exact _.
  Defined.
*)

  Lemma Basis'_ishset : forall (q : QType'), IsHSet (Basis' q).
  Proof.
    induction q.
    * exact _.
    * exact _.
    * exact _.
    * exact _.
  Qed.

  Definition Basis'_hset (q : QType') : hSet.
    exists (Basis' q).
    apply Basis'_ishset.
  Defined.
  
  Definition Basis'_cell : forall q r (U : UMatrix q r), 
             Basis'_hset q = Basis'_hset r.
  Admitted.
  Lemma Basis'_compose : forall (x y z : QType') (f : UMatrix x y) (g : UMatrix y z),
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

Section ToMatrix.
(*  Context `{Univalence}.*)

  Class FinQType (q : QType) := { finBasis : Finite (Basis q) }.
  Global Instance finOne : FinQType One.
  Proof.
    constructor.
    rewrite Basis_Unit. 
    apply finite_unit.
  Defined.
  Global Instance finTensor {q r} `{FinQType q} `{FinQType r} : FinQType (q ⊗ r).
  Proof.
    constructor.
    rewrite Basis_Tensor.
    destruct H0, H1.
    apply finite_prod; auto.
  Defined.
  Global Instance finOPlus {q r} `{FinQType q} `{FinQType r} : FinQType (q ⊕ r).
  Proof.
    constructor.
    rewrite Basis_OPlus.
    destruct H0, H1.
    apply finite_sum; auto.
  Defined.
  Global Instance finLower {τ} `{Finite τ} : FinQType (Lower τ).
  Proof.
    constructor.
    auto.
  Qed.
  Global Instance FinQType_Finite q `{FinQType q} : Finite (Basis q).
  Proof.
    destruct H0.
    auto.
  Qed.

  (* Defining unitary transformations on classical states *)
  Definition to_matrix {I J} `{Finite I} `{Finite J} (f : I -> J) : Matrix I J :=
    MkMatrix _ _ (fun i j => if dec_paths j (f i) then 1 else 0)%nat.
  Definition toU {q r} `{FinQType q} `{FinQType r} (f : Basis q -> Basis r)
             (pf : Unitary_Prop (to_matrix f)) : q = r.
  Proof.
    admit (* will we need to prove this by induction on q, r? *).
  Admitted.

End ToMatrix.


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


  Variable QType_cell : forall {q r} (U : UMatrix q r),
           cell _ U # QType_point q = QType_point r.

  Variable QType_compose : forall q r s (U : UMatrix q r) (V : UMatrix r s),
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

  Variable QType_cell : forall {q r} (U : UMatrix q r),
    QType_point_rec q = QType_point_rec r.
  
  Variable QType_compose : forall (x y z : QType') 
                                  (f : UMatrix x y) (g : UMatrix y z),
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
  Lemma to_PQType_cell : forall q r (U : UMatrix q r),
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
               `{FinQType (from_PQType p)} `{FinQType (from_PQType q)}
               (f : forall Var, PBasis Var p -> PBasis Var q) 
                  : Basis (from_PQType p) -> Basis (from_PQType q).
  Proof.
    intros x.
    apply pbasis_basis.
    apply f.
    apply basis_pbasis.
    exact x.
  Defined.

  Definition PBasis_to_Matrix {p q : PQType} 
               `{FinQType (from_PQType p)} `{FinQType (from_PQType q)}
               (f : forall Var, PBasis Var p -> PBasis Var q) 
             : Matrix (Basis (from_PQType p)) (Basis (from_PQType q)).
  Proof.
    apply to_matrix.
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
