Require Import HoTT.
Require Import quotient1.
Require Import Groupoid.


Section DecidablePaths.
  Notation "x =? y" := (dec_paths x y) (at level 25).
  Context {I} `{DecidablePaths I}.
  Definition del (i j : I) : nat := (if i =? j then 1 else 0)%nat.

  Lemma del_sym : forall i j, del i j = del j i.
  Proof.
    intros i j. unfold del.
    destruct (j =? i) as [b | b];
    destruct (i =? j) as [b' | b']; auto.
    * apply Empty_ind.
      apply b'. 
      apply b^.
    * apply Empty_ind.
      apply b.
      apply b'^.
  Qed.

End DecidablePaths.
Notation "x =? y" := (dec_paths x y) (at level 25).
Notation "δ_{ i }[ j ]" := (del i j) (at level 40).




Section Matrix.
  Context `{funext : Funext}.

  Lemma finplus_del : forall {I J} `{Finite I} `{Finite J} (f : I -> J -> nat) i j,
        f i j = finplus (fun k => (δ_{i}[k] * f k j))%nat.
  Admitted.


  Inductive Matrix (I J : Type) := 
  | MkMatrix `{Finite I} `{Finite J} :
              (I -> J -> nat) -> Matrix I J.
  (* Here, nat is a stand-in for C *)
  Arguments MkMatrix {I J} {FinI} {FinJ} f : rename.

  Ltac collapse_finite :=
    repeat match goal with
    | [H : Finite ?I, H' : Finite ?I |- _ ] => assert (eq : H = H') by (apply ishprop_finite); 
                                               try rewrite eq in *; clear eq H
    end.

  Ltac prep_matrix_equality := collapse_finite;
                               apply ap; apply path_arrow; intro i; apply path_arrow; intros j. 


  Definition lookupMatrix {I J} (A : Matrix I J) (i : I) (j : J) :=
    match A with
    | MkMatrix _ _ A' => A' i j
    end.
  Notation "A [ i , j ]" := (lookupMatrix A i j) (at level 10).

  Definition Id {I} `{Finite I}: Matrix I I := MkMatrix del.
(*
  Instance M_refl : Reflexive Matrix := Id.
*)

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
  Section groupoid_properties.

    Lemma Matrix_v_v : forall {I J} (A : Matrix I J), A^^ = A.
    Proof.
      intros.
      destruct A.
      reflexivity.
    Qed.

    (* I CAN'T FIND THIS IN THE LIBRARY, GRR *)
    Lemma mult_comm : forall (m n : nat), (m * n = n * m)%nat.
    Proof.
      induction m; intros; simpl.
      * rewrite <- mult_n_O. reflexivity.
      * rewrite <- mult_n_Sm. rewrite IHm.
        apply nat_plus_comm.
    Qed.

    Lemma Matrix_inv_compose : forall {I J K} (A : Matrix I J) (B : Matrix J K),
        (B o A)^ = A^ o B^.
    Proof.
      intros.
      destruct A, B.
      simpl. 
      prep_matrix_equality.
      apply ap.
      apply path_arrow; intro k. 
      apply mult_comm.
    Qed.

    Lemma Matrix_Id_v : forall {I} `{Finite I}, Id^ = @Id I _.
    Proof.
      intros.
      unfold Id.
      simpl.
      prep_matrix_equality.
      apply del_sym.
    Qed.

    Lemma Matrix_Id_r : forall {I J} `{Finite I} (A : Matrix I J), A o Id = A.
    Proof.
      destruct A. simpl. 
      prep_matrix_equality.
      rewrite (finplus_del n).
      reflexivity.
    Qed.


    Lemma finplus_sym : forall I J `{Finite I} `{Finite J} (f : I -> J -> nat),
      finplus (fun i : I => finplus (fun j : J => f i j))
    = finplus (fun j : J => finplus (fun i : I => f i j)).
    Admitted.


    Lemma Matrix_assoc : forall {I J K L} (A : Matrix I J) (B : Matrix J K) (C : Matrix K L),
          (C o (B o A)) = (C o B) o A.
    Proof.
      destruct A, B, C. simpl.
      prep_matrix_equality. rename j into l.
      set (f := fun k j => (n i j * n0 j k)%nat).
      admit (* this is true, just arithmetic *).
    Admitted.
  End groupoid_properties.


  Record UnitaryProp {I J} `{Finite I} `{Finite J} (A : Matrix I J) :=
    { A_A_dag : A^ o A = Id
    ; A_dag_A : A o A^ = Id
    ; U_size  : fcard I = fcard J
    }.

  Lemma UnitaryProp_Id : forall {I} `{Finite I}, UnitaryProp (@Id I _).
  Proof.
    intros. 
    split.
    * rewrite Matrix_Id_r. apply Matrix_Id_v.
    * rewrite Matrix_Id_v. rewrite Matrix_Id_r. reflexivity.
    * reflexivity.
  Qed.
  Lemma UnitaryProp_sym : forall {I J} `{Finite I} `{Finite J} (A : Matrix I J), 
        UnitaryProp A -> UnitaryProp (A^).
  Proof.
    intros I J FinI FinJ A pf.
    destruct pf.
    split.
    + rewrite Matrix_v_v. auto.
    + rewrite Matrix_v_v. auto.
    + symmetry. auto.
  Qed.
  Lemma UnitaryProp_trans : forall {I J K} `{Finite I} `{Finite J} `{Finite K} 
        (A : Matrix I J) (B : Matrix J K),
    UnitaryProp A -> UnitaryProp B -> UnitaryProp (B o A).
  Proof.
    intros I J K FinI FinJ FinK A B pfA pfB.
    destruct pfA, pfB.
    split.
    + rewrite Matrix_inv_compose.
      transitivity (A^ o (B^ o B) o A).
      * repeat rewrite Matrix_assoc. reflexivity.
      * rewrite A_A_dag1.
        rewrite Matrix_Id_r.
        apply A_A_dag0.
    + rewrite Matrix_inv_compose.
      transitivity (B o (A o A^) o B^).
      * repeat rewrite Matrix_assoc. reflexivity.
      * rewrite A_dag_A0.
        rewrite Matrix_Id_r.
        apply A_dag_A1.
    + refine (U_size0 @ U_size1).
  Qed.

  Inductive UnitaryMatrix' : Type -> Type -> Type :=
  | UMatrix' {I} `{Finite I} (U : Matrix I I) : UnitaryProp U -> UnitaryMatrix' I I
  | UIso' {I J} : I <~> J -> UnitaryMatrix' I J.

  Definition toMatrix {I} `{Finite I} (f : I <~> I) : Matrix I I :=
    MkMatrix (fun i j => if j =? f i then 1 else 0)%nat.
  Lemma toMatrix_v : forall {I} `{Finite I} (f : I <~> I),
    (toMatrix f)^ = toMatrix f^.
  Proof.
    intros. simpl.
    unfold toMatrix.
    simpl.
    prep_matrix_equality. Search (equiv_inverse (equiv_inverse _)).
    specialize (einv_V f); intros eq.
    destruct (i =? f j) as [b | b], (j =? f^-1 i) as [b' | b']; auto.
    * apply Empty_ind. apply b'.
      apply moveL_equiv_V.
      rewrite b. reflexivity.
    * apply Empty_ind. apply b.
      apply moveL_equiv_M.
      rewrite b'. reflexivity.
  Qed.



  Inductive UnitaryMatrixEq' : forall I J, UnitaryMatrix' I J -> UnitaryMatrix' I J -> Type :=
  | UIsoMatrix {I} `{Finite I} (f : I <~> I) (U : Matrix I I) (pf : UnitaryProp U) :
    U = toMatrix f ->
    UnitaryMatrixEq' I I (UMatrix' U pf) (UIso' f).
  Definition UnitaryMatrixEq I J (U1 U2 : UnitaryMatrix' I J) : Type := 
    Trunc -1 (UnitaryMatrixEq' I J U1 U2).

  Definition UnitaryMatrix I J := @quotient (UnitaryMatrix' I J) (UnitaryMatrixEq I J) _.

  Definition UMatrix {I} `{Finite I} (U : Matrix I I) (pf : UnitaryProp U) : UnitaryMatrix I I :=
    class_of _ (UMatrix' U pf).
  Definition UIso {I J} (f : I <~> J) : UnitaryMatrix I J :=
    class_of _ (UIso' f).
  
  Section UnitaryMatrix_ind.

    Variable P : forall I J, UnitaryMatrix I J -> Type.
    Variable P_HSet : forall I J (U : UnitaryMatrix I J), IsHSet (P _ _ U).

    Variable P_UMatrix : forall {I} `{Finite I} (U : Matrix I I) (pf : UnitaryProp U),
        P _ _ (UMatrix U pf).
    Variable P_UIso : forall {I J} (f : I <~> J), P _ _ (UIso f).

    Variable P_Eq : forall {I} `{Finite I} (f : I <~> I) (U : Matrix I I) 
                                           (pf : UnitaryProp U) (eq : U = toMatrix f),
                           
      transport (P I I) (related_classes_eq _ (tr (UIsoMatrix f _ pf eq))) (P_UMatrix _ _ _ pf)
    = P_UIso _ _ f.

    Let P_class : forall {I J} (U : UnitaryMatrix' I J), P _ _ (class_of _ U).
    Proof.
      destruct U; [ apply P_UMatrix | apply P_UIso ].
    Defined.
    
    Lemma UnitaryMatrix_ind : forall I J (U : UnitaryMatrix I J), P _ _ U.
    Proof.
      intros I J.
      apply quotient_ind with (dclass := P_class).
      + exact _.
      + intros x y. apply Trunc_ind; [exact _ | ].
        intros eq.
        destruct eq.
        apply P_Eq.
    Defined.

    (* TODO: add computation rule? *)

  End UnitaryMatrix_ind.
  About quotient_rec.

  Section UnitaryMatrix_rec.
    Variable C : Type -> Type -> Type.
    Variable C_HSet : forall I J, IsHSet (C I J).
    Variable C_UMatrix : forall {I} `{Finite I} (U : Matrix I I), UnitaryProp U -> C I I.
    Variable C_UIso : forall {I J}, I <~> J -> C I J.
    Variable C_Eq : forall {I} `{Finite I} (f : I <~> I) (U : Matrix I I) 
                                           (pf : UnitaryProp U), U = toMatrix f ->
                                           C_UMatrix _ _ U pf = C_UIso _ _ f.

    Definition UnitaryMatrix_rec : forall I J, UnitaryMatrix I J -> C I J.
    Proof.
      apply UnitaryMatrix_ind with (P_UMatrix := C_UMatrix) (P_UIso := C_UIso).
      + exact _.
      + intros. 
        refine (transport_const _ _ @ C_Eq _ _ _ _ _ eq).
    Defined.
  End UnitaryMatrix_rec.

  Section UGroupoid.

    Definition UId I : UnitaryMatrix I I := UIso 1.
    Instance UnitaryMatrix_refl : Reflexive UnitaryMatrix := UId.

    Instance UnitaryMatrix_sym : Symmetric UnitaryMatrix.
    Proof.
      transparent assert (sym_UMatrix : (forall {I} `{Finite I} (U : Matrix I I), 
                                         UnitaryProp U -> UnitaryMatrix I I)).
      {
        intros .
        refine (UMatrix (U^)%groupoid _).
        apply UnitaryProp_sym.
        auto.
      }
      
      transparent assert (sym_UIso : (forall {I J} (f : I <~> J), 
                                      UnitaryMatrix J I)).
      { intros.
        refine (UIso (symmetry _ _ f)). 
      }
 
      intros I J.
      apply UnitaryMatrix_rec with (C := fun I J => UnitaryMatrix J I) 
                                   (C_UMatrix := sym_UMatrix)
                                   (C_UIso := sym_UIso).
      * exact _.
      * clear I J. intros.
        unfold sym_UMatrix, sym_UIso.
        apply related_classes_eq.
        apply tr.
        apply UIsoMatrix.
        rewrite X.
        apply toMatrix_v.
    Qed.

  Instance UnitaryMatrix_trans : Transitive UnitaryMatrix.
  Admitted.

  Axiom U_groupoid : groupoid _ UnitaryMatrix.

  End UGroupoid.

End Matrix.