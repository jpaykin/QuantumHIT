Require Import HoTT.
Require Import quotient1.
Require Import Groupoid.
Require Import Math.
Require Import Monad.

Section Vector.

  Definition ℂ := nat. (* stand-in for complex numbers *)
  Definition Vector I := list (I * ℂ).
  
  
  Open Scope list_scope.
  Notation "[]" := nil.
  Notation "[ x ]" := (x :: []).


  Definition Vector_fmap {I J}  (f : I -> J) : Vector I -> Vector J := 
    fmap (fun (x : I * ℂ) => let (i,c) := x in (f i,c)).
  Definition Vector_pure {I} (i : I) : Vector I := return_ (i,1).
  Definition Vector_liftA {I J} (f : list ((I -> J)*ℂ)) (v : list (I*ℂ)) 
                                 : list (J*ℂ) :=
    do x  ← v; let (i,c) := (x : I*ℂ) in
    do z ← f; let (f',c') := (z : (I -> J)*ℂ)  in 
    return_ (f' i, c*c')%nat.
  Definition Vector_bind {I} (v : list (I*ℂ)) {J} (f : I -> list (J*ℂ)) 
                         : Vector J :=
    do x ← v;   let (i,c) := (x : I*ℂ) in 
    do y ← f i; let (j,c') := (y : J*ℂ) in
    return_ (j,c*c')%nat.
  Instance VectorF : Functor Vector := {fmap := @Vector_fmap}.
  Instance VectorA : Applicative Vector := { pure := @Vector_pure 
                                           ; liftA := @Vector_liftA }.
  Instance VectorM : Monad Vector := { bind := @Vector_bind }.


  Fixpoint lookup {I} `{DecidablePaths I} i (v : Vector I) :=
    match v with
    | nil => 0%nat
    | (j,c)::v' => if i =? j then c else lookup i v'
    end.
  Fixpoint In {A} (a : A) (ls : list A) : Type :=   
    match ls with
    | nil => Empty
    | b :: ls' => a = b \/ In a ls'
    end.
  Notation "i ↦ c ∈ v" := (In (i,c) v) (at level 37).
  
  Fixpoint dot `{Funext} {I} `{Finite I} (v v' : Vector I) : ℂ :=
    finplus (fun i => lookup i v * lookup i v')%nat.

  Definition del {I} i : Vector I := return_ i.
  Notation "δ^{ i }" := (del i).

(*  Definition support {I J} (f : I -> Vector J) (j : J) := 
    { x : I*ℂ & j ↦ snd x ∈ f (fst x) }.*)
  Definition equiv {I J} (rows : I -> Vector J) (cols : J -> Vector I) :=
    forall i j c, j ↦ c ∈ rows i <-> i ↦ c ∈ cols j.
  Global Instance equiv_HProp : forall I J 
                                (rows : I -> Vector J) (cols : J -> Vector I), 
        IsHProp (equiv rows cols).
  Proof.
  Admitted (* should be true *).
  
  Record Matrix I J := { rows : I -> Vector J
                       ; cols : J -> Vector I
                       ; rows_cols_equiv : equiv rows cols }.
  Arguments rows {I J}.
  Arguments cols {I J}.
  Arguments rows_cols_equiv {I J}.

  (* need some tactics for proving lemmas of the form `equiv rows cols` *)

  Definition Id I : Matrix I I.
  Proof.
    exists del del.
    { intros i j c. simpl; split. 
      * intros [eq | [ ] ]. 
        left. 
        destruct (pair_inv eq) as [eqj eqc].
        rewrite eqj, eqc. reflexivity.
      * intros [eq | [ ] ].
        left.
        destruct (pair_inv eq) as [eqj eqc].
        rewrite eqj, eqc. reflexivity.
    }
  Defined.

  Instance Matrix_refl : Reflexive Matrix.
  Proof.
    intros I. exact (Id I).
  Defined.

  Instance Matrix_sym : Symmetric Matrix.
  Proof.
    intros I J A.
    exists (cols A) (rows A).
    intros i j c.
    set (pf := rows_cols_equiv A j i c).
    destruct pf; split; auto.
  Defined.

  Section Transitive.  
    Context {I J K} (A : Matrix I J) (B : Matrix J K).
    Definition rows_trans : I -> Vector K :=
      fun i => do j ← rows A i; rows B j.
    Definition cols_trans : K -> Vector I :=
      fun k => do j ← cols B k; cols A j.
    Lemma rows_cols_trans_equiv : equiv (rows_trans) (cols_trans).
    Admitted.
  End Transitive.
  Instance Matrix_trans : Transitive Matrix.
  Proof.
    intros I J K A B.
    exists (rows_trans A B) (cols_trans A B).
    apply rows_cols_trans_equiv.
  Defined.

  Section Kron.
    Context {I I' J J'} (A : Matrix I J) (B : Matrix I' J').
    Definition rows_kron := fun (x : I*I') => 
                       let (i,i') := x in 
                       do j  ← rows A i;
                       do j' ← rows B i';
                       return_ (j,j').
    Definition cols_kron := fun (y : J*J') =>
                       let (j,j') := y in
                       do i  ← cols A j;
                       do i' ← cols B j';
                       return_ (i,i').
    Lemma rows_cols_equiv_kron : equiv rows_kron cols_kron.
    Admitted.
  End Kron.
  Definition kron {I J I' J'} (A : Matrix I J) (B : Matrix I' J') 
                :  Matrix (I*I') (J*J').
  Proof.
    exists (rows_kron A B) (cols_kron A B).
    apply rows_cols_equiv_kron.
  Defined.

  Section Plus.
    Context {I I' J J'} (A : Matrix I J) (B : Matrix I' J').
    Definition rows_plus := fun (x : I+I') => match x with
                                    | inl i  => do j ← rows A i; return_ (inl j)
                                    | inr i' => do j ← rows B i'; return_ (inr j)
                                    end.
    Definition cols_plus := fun (y : J+J') => match y with
                                    | inl j  => do i ← cols A j; return_ (inl i)
                                    | inr j' => do i ← cols B j'; return_ (inr i)
                                    end.
    Lemma rows_cols_equiv_plus : equiv rows_plus cols_plus.
    Admitted.
  End Plus.
  Definition plus {I J I' J'} (A : Matrix I J) (B : Matrix I' J') 
                : Matrix (I+I') (J+J').
  Proof.
    exists (rows_plus A B) (cols_plus A B).
    apply rows_cols_equiv_plus.
  Defined.

  
  Definition isoToMatrix {I J} (f : I <~> J) : Matrix I J.
  Proof.
    exists (fun i => δ^{f i}) (fun j => δ^{f^-1 j}).
    { intros i j c.
      split; simpl; intros [H | [ ] ]; destruct (pair_inv H) as [H1 H2]; 
        rewrite H1, H2; left.
      * admit (* true *).
      * admit.
    }
  Admitted.

End Vector.
Existing Instance VectorF.
Existing Instance VectorA.
Existing Instance VectorM.
Instance VectorM_correct : Monad_Correct Vector.
Admitted.

Existing Instance Matrix_refl.
Existing Instance Matrix_sym.
Existing Instance Matrix_trans.

Section MatrixProofs.

  Open Scope groupoid_scope.
  Context `{Funext}.

  Lemma Matrix_eq : forall {I J} 
        (f f' : I -> Vector J) (g g' : J -> Vector I) pf pf',
        (forall i, f i = f' i) ->
        (forall j, g j = g' j) ->
        Build_Matrix _ _ f g pf = Build_Matrix _ _ f' g' pf'.
  Admitted.

  Ltac destruct_matrices :=
    repeat match goal with
    | [ H : Matrix _ _ |- _ ] => destruct H
    end.

  Ltac solve_matrix_eq := intros; try (destruct_matrices; simpl;
    repeat unfold Matrix_refl, Id, Matrix_sym, 
           Matrix_trans, cols_trans, rows_trans,
           kron, cols_kron, rows_kron,
           plus, cols_plus, rows_plus;
   apply Matrix_eq; simpl; intros; try reflexivity).


    Lemma Matrix_v_v : forall {I J} (A : Matrix I J), A^^ = A.
    Proof. 
      solve_matrix_eq. 
    Qed.

    Lemma Matrix_inv_compose : forall {I J K} (A : Matrix I J) (B : Matrix J K),
        (B o A)^ = A^ o B^.
    Proof. 
      solve_matrix_eq.
    Qed.

    Lemma Matrix_Id_v : forall {I}, (Id I)^ = Id I.
    Proof. 
      solve_matrix_eq.
    Qed.

    Opaque bind return_.
    Lemma Matrix_Id_r : forall {I J} (A : Matrix I J), A o 1 = A.
    Proof. 
      solve_matrix_eq.
      * rewrite <- bind_left_unit. reflexivity.
      * rewrite <- bind_right_unit. reflexivity.
    Qed.


    Lemma Matrix_assoc : forall {I J K L} 
                         (A : Matrix I J) (B : Matrix J K) (C : Matrix K L),
          (C o (B o A)) = (C o B) o A.
    Proof.
      solve_matrix_eq.
      * rewrite bind_associativity. reflexivity.
      * rewrite bind_associativity. reflexivity.
    Qed.


    Lemma Kron_inv : forall {I J I' J'} (A : Matrix I J) (B : Matrix I' J'),
        (kron A B)^ = kron A^ B^.
    Proof.
      solve_matrix_eq.
    Qed.
    Lemma Kron_bilinear : forall {I I' J J' K K'} 
                                 (A : Matrix I J) (B : Matrix J K)
                                 (A' : Matrix I' J') (B' : Matrix J' K'),
        kron B B' o kron A A' = kron (B o A) (B' o A').
    Proof.
      solve_matrix_eq.
      * destruct i as [i i'].
        repeat rewrite <- bind_associativity.
        apply ap. apply path_arrow; intro j.
        repeat rewrite <- bind_associativity.
        admit (* need a monad_solver here *).
      * destruct j as [k k'].
        repeat rewrite <- bind_associativity.
        apply ap. apply path_arrow; intro j.
        repeat rewrite <- bind_associativity.
        admit.
    Admitted.

    Lemma kron_Id : forall I J,
          kron (Id I) (Id J) = Id (I*J).
    Proof.
      solve_matrix_eq.
    Qed.

    Lemma plus_inv : forall {I J I' J'} (A : Matrix I J) (B : Matrix I' J'),
        (plus A B)^ = plus A^ B^.
    Proof.
      solve_matrix_eq.
    Qed.

    Lemma plus_bilinear : forall {I I' J J' K K'} 
                                 (A : Matrix I J) (B : Matrix J K)
                                 (A' : Matrix I' J') (B' : Matrix J' K'),
        plus B B' o plus A A' = plus (B o A) (B' o A').
    Proof.
      solve_matrix_eq.
      - destruct i as [i | i'].
        * (* interaction between fmap and bind *) admit.
        * admit.
      - admit.
    Admitted.

    Lemma plus_Id : forall I J,
          plus (Id I) (Id J) = Id (I+J).
    Proof.
      solve_matrix_eq.
      - destruct i as [i | j]; rewrite <- bind_left_unit; reflexivity.
      - destruct j as [i | j]; rewrite <- bind_left_unit; reflexivity.
    Qed.

    Transparent bind return_.

End MatrixProofs.

Section UnitaryProp.

  Context `{Funext}.
  Open Scope groupoid_scope.
  Record UnitaryProp {I J} (A : Matrix I J) := { A_dag_A : A^ o A = 1
                                               ; A_A_dag : A o A^ = 1 
                                               ; square  : I = J }.
                        
  Lemma UnitaryProp_Id : forall {I}, UnitaryProp (Id I).
  Proof.
    intros I.
    split.
    * rewrite Matrix_Id_r. apply Matrix_Id_v.
    * rewrite Matrix_Id_v. apply Matrix_Id_r.
    * exact 1.
  Qed.

  Lemma UnitaryProp_sym : forall {I J} (A : Matrix I J), 
        UnitaryProp A -> UnitaryProp (A^).
  Proof.
    intros I J A [A_dag_A A_A_dag square].
    constructor.
    + rewrite Matrix_v_v.
      apply A_A_dag.
    + rewrite Matrix_v_v.
      apply A_dag_A.
    + exact square^.
  Qed.

  Lemma UnitaryProp_trans : forall {I J K}
        (A : Matrix I J) (B : Matrix J K),
    UnitaryProp A -> UnitaryProp B -> UnitaryProp (B o A).
  Proof.
    intros I J K A B pfA pfB.
    destruct pfA as [A_dag_A A_A_dag squareA]
           , pfB as [B_dag_B B_B_dag squareB].
    constructor.
    + rewrite Matrix_inv_compose.
      transitivity (A^ o (B^ o B) o A).
      * repeat rewrite Matrix_assoc. reflexivity.
      * rewrite B_dag_B.
        rewrite Matrix_Id_r.
        apply A_dag_A.
    + rewrite Matrix_inv_compose.
      transitivity (B o (A o A^) o B^).
      * repeat rewrite Matrix_assoc. reflexivity.
      * rewrite A_A_dag.
        rewrite Matrix_Id_r.
        apply B_B_dag.
    + exact (squareA @ squareB).
  Qed.


  Lemma UnitaryProp_kron : forall {I J I' J'} (A : Matrix I J) (B : Matrix I' J'),
        UnitaryProp A -> UnitaryProp B -> UnitaryProp (kron A B).
  Proof.
    intros I J I' J' A B [A_dag_A A_A_dag squareA]
                         [B_dag_B B_B_dag squareB].
    constructor.
    + rewrite Kron_inv.
      rewrite Kron_bilinear.
      rewrite A_dag_A, B_dag_B.
      apply kron_Id.

    + rewrite Kron_inv.
      rewrite Kron_bilinear.
      rewrite A_A_dag, B_B_dag.
      apply kron_Id.
    + rewrite squareA, squareB. reflexivity.
  Qed.    

  Lemma UnitaryProp_plus : forall {I J I' J'} (A : Matrix I J) (B : Matrix I' J'),
        UnitaryProp A -> UnitaryProp B -> UnitaryProp (plus A B).
  Proof.
    intros I J I' J' A B [A_dag_A A_A_dag squareA]
                         [B_dag_B B_B_dag squareB].
    constructor.
    + rewrite plus_inv. 
      rewrite plus_bilinear.
      rewrite A_dag_A, B_dag_B.
      apply plus_Id.
    + rewrite plus_inv. 
      rewrite plus_bilinear.
      rewrite A_A_dag, B_B_dag.
      apply plus_Id.
    + rewrite squareA, squareB. reflexivity.
  Qed.

  Section UMatrix.
    Definition UMatrix I J := { A : Matrix I J & UnitaryProp A }.

    Definition UId I : UMatrix I I := exist _ 1 (UnitaryProp_Id).
    Instance UMatrix_refl : Reflexive UMatrix := UId.
    
    Instance UMatrix_sym : Symmetric UMatrix.
    Proof.
      intros I J [A pfA].
      exists A^.
      apply UnitaryProp_sym; auto.
    Defined.

    Instance UMatrix_trans : Transitive UMatrix.
    Proof.
      intros I J K [A pfA] [B pfB].
      exists (B o A).
      apply UnitaryProp_trans; auto.
    Qed.

    Definition UMatrix_kron :  forall I J I' J',
               UMatrix I J -> UMatrix I' J' -> 
               UMatrix (I * I') (J * J').
    Proof.
      intros I J I' J' [A pfA] [B pfB].
      exists (kron A B).
      apply UnitaryProp_kron; auto.
    Qed.
    
    
    Definition UMatrix_plus :  forall I J I' J',
               UMatrix I J -> UMatrix I' J' -> 
               UMatrix (I + I') (J + J').
    Proof.
      intros I J I' J' [A pfA] [B pfB].
      exists (plus A B).
      apply UnitaryProp_plus; auto.
    Qed.
  
  End UMatrix.
End UnitaryProp.

Section Ugroupoid.
Context `{Funext}.
Existing Instance UMatrix_refl.
Existing Instance UMatrix_sym.
Existing Instance UMatrix_trans.

Open Scope groupoid_scope.


  Lemma UMatrix_1_l : forall I J (U : UMatrix I J),
        1 o U = U.
  Admitted.

  Lemma UMatrix_1_r : forall I J (U : UMatrix I J),
    U o 1 = U.
  Admitted.

  Lemma UMatrix_assoc : forall I J K L 
        (U : UMatrix I J) (V : UMatrix J K) (W : UMatrix K L),
        W o (V o U) = W o V o U.
  Admitted.

  Lemma UMatrix_V_r : forall I J (U : UMatrix I J),
        U o U^ = 1.
  Admitted.

  Lemma UMatrix_V_l : forall I J (U : UMatrix I J),
        U^ o U = 1.
  Admitted.

  Lemma U_groupoid : groupoid _ UMatrix.
    exact(
    Build_groupoid _ _ 
                   UMatrix_1_l UMatrix_1_r
                   UMatrix_assoc
                   UMatrix_V_r UMatrix_V_l).
  Defined.



End Ugroupoid.