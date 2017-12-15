Require Import HoTT.
Require Import quotient1.
Require Import Groupoid.

Inductive QType' :=
| One' : QType'
| OPlus' : QType' -> QType' -> QType'
| Tensor' : QType' -> QType' -> QType'
| Lower' : Type -> QType'
.

Fixpoint Basis' (q : QType') : Type :=
  match q with
  | One' => Unit
  | OPlus' q1 q2 => Basis' q1 + Basis' q2
  | Tensor' q1 q2 => Basis' q1 * Basis' q2
  | Lower' τ => τ
  end.

Section Matrix.

  Context `{Funext}.
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
    Definition bdec_paths {A} `{DecidablePaths A} (x y : A) : Bool :=
      if dec_paths x y then true else false.
    Notation "x =? y" := (dec_paths x y) (at level 25).

    Variable I : Type.
    Axiom finI : Finite I. (* how to resolve this?? *)
    Definition Id : Matrix I I := MkMatrix (fun i i' => if i =? i' then 1 else 0).
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
  Instance M_decPaths : forall {I J}, DecidablePaths (Matrix I J).
  Proof.
    intros I J [pfI pfJ A] [pfI' pfJ' B].
    assert (Decidable (pfI = pfI')) by exact _.
    assert (Decidable (pfJ = pfJ)) by exact _.
    assert (Decidable (A = B)).
    { admit. (*??*) }
  Admitted.
  (* which means that Matrix I J is an HSet *)

  Lemma Unitary_Prop_Set : forall {I J} (A : Matrix I J),
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

  Context `{Funext}.
  Definition UMatrix (q r : QType') := {A : Matrix (Basis' q) (Basis' r) & Unitary_Prop A}.

  Instance U_refl : Reflexive UMatrix.
  Admitted.

  Instance U_trans : Transitive UMatrix.
  Admitted.

  Instance U_sym : Symmetric UMatrix.
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


End UMatrix.

Section QType.

  Context `{Funext}.
  Open Scope groupoid_scope.
  Definition QType := quotient1 U_groupoid.

  Definition Tensor : QType -> QType -> QType.
  Proof.
    apply quotient1_map2 with (f := Tensor') (map_cell := @U_tensor _).
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
    apply quotient1_map2 with (f := OPlus') (map_cell := @U_oplus _).
    apply @U_oplus_compose.
  Defined.

  Definition One : QType := point U_groupoid One'.
  Definition Lower τ : QType := point U_groupoid (Lower' τ).
  
  Definition Qubit : QType := OPlus One One.

End QType.

Infix "⊗" := Tensor (at level 40).
Infix "⊕" := OPlus (at level 40).

