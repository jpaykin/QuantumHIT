Require Import HoTT.
Require Import quotient1.
Require Import QTypes2.


Context `{Funext}.
Section Exp.
  
  Variable Var : QType -> Type.

  Inductive exp : QType -> Type :=
  | var {q} : Var q -> exp q

  | pair {q r} : exp q -> exp r -> exp (q ⊗ r)
  | let_pair {q r s} : exp (q ⊗ r) -> (Var q -> Var r -> exp s) -> exp s 

  | unit : exp One
  | let_unit {q} : exp One -> exp q -> exp q

  | ι0 {q0 q1} : exp q0 -> exp (q0 ⊕ q1)
  | ι1 {q0 q1} : exp q1 -> exp (q0 ⊕ q1)
  | case_of {q0 q1 r} : exp (q0 ⊕ q1) -> (Var q0 -> exp r) -> (Var q1 -> exp r) ->
                        exp r

  | put {τ : hSet} : τ -> exp (Lower τ)
  | let_bang {τ : hSet} {q} : exp (Lower τ) -> (τ -> exp q) -> exp q
  .


End Exp.

Arguments var {Var} {q}.
Arguments pair {Var} {q r}.
Arguments let_pair {Var} {q r s}.
Arguments unit {Var}.
Arguments let_unit {Var} {q}.
Arguments ι0 {Var} {q0 q1}.
Arguments ι1 {Var} {q0 q1}.
Arguments case_of {Var} {q0 q1 r}.
Arguments put {Var} {τ} : rename.
Arguments let_bang {Var} {τ} {q} : rename.


(**************)
(* flattening *)
(**************)

Section Squash.
  Variable Var : QType -> Type.

  Fixpoint squash {q} (e : exp (exp Var) q) : exp Var q.
  Proof.
    destruct e as [ q x 
                  | q r e1 e2 | q r s e e' (* pairs *)
                  | | q e e' (* unit *)
                  | q0 q1 e | q0 q1 e | q0 q1 r e f1 f2 (* sum *)
                  | τ x | τ q e e' (* let! *)].
    * exact x.
    * exact (pair (squash _ e1) (squash _ e2)).
    * exact (let_pair (squash _ e) (fun x1 x2 => squash _ (e' (var x1) (var x2)))).
    * exact unit.
    * exact (let_unit (squash _ e) (squash _ e')).
    * exact (ι0 (squash _ e)).
    * exact (ι1 (squash _ e)).
    * exact (case_of (squash _ e) (fun x => squash _ (f1 (var x))) 
                                  (fun x => squash _ (f2 (var x)))).
    * exact (put x).
    * exact (let_bang (squash _ e) (fun x => squash _ (e' x))).
  Defined.
End Squash.
Arguments squash {Var} {q}.

(* Polymorphic expressions *)

Definition Exp q := forall Var, exp Var q.
Definition Exp1 q r := forall Var, Var q -> exp Var r.
Definition Exp2 q r s := forall Var, Var q -> Var r -> exp Var s.
Notation "q --o r" := (Exp1 q r) (at level 30).


Section Exp_1Type.
  Context `{Funext}.
  Lemma exp_trunc : forall Var, (forall q, IsTrunc 1 (Var q)) ->
                    forall q, IsTrunc 1 (exp Var q).
  Proof.
    intros.
  Admitted (* is this true? *).

  Global Instance Exp_trunc : forall q, IsTrunc 1 (Exp q).
  Proof.
    intros q.
    unfold Exp.
    apply @trunc_forall; [auto | ].
    intros Var.
    apply exp_trunc.
    admit.
  Admitted.
End Exp_1Type.


Definition Subst {q r} (f : q --o r) (e : Exp q) : Exp r := fun Var =>
  squash (f (exp Var) (e Var)).

Definition Subst2 {q r s} (f : Exp2 q r s) (e1 : Exp q) (e2 : Exp r) : Exp s := 
  fun Var => squash (f (exp Var) (e1 Var) (e2 Var)).

Inductive Lift : QType -> QType -> Type :=
| Suspend {q r} : (q --o r) -> Lift q r.
Definition Force {q r} (f : Lift q r) : Exp q -> Exp r.
  destruct f as [q r f].
  exact (Subst f).
Defined.

Definition Let_In {q r} (e : Exp q) (f : q --o r) : Exp r :=
  Subst f e.

Definition Unit : Exp One := fun _ => unit.
Definition Let_Unit {q} (e : Exp One) (e' : Exp q) : Exp q := fun _ =>
  let_unit (e _) (e' _).

Definition Inj0 {q0 q1} (e : Exp q0) : Exp (q0 ⊕ q1) := fun _ =>
  ι0 (e _).
Definition Inj1 {q0 q1} (e : Exp q1) : Exp (q0 ⊕ q1) := fun _ =>
  ι1 (e _).
Definition Case_Of {q0 q1 r} (e : Exp (q0 ⊕ q1)) (f0 : q0 --o r) (f1 : q1 --o r) 
           : Exp r := fun _ =>
  case_of (e _) (f0 _) (f1 _).

Definition Pair {q r} (e1 : Exp q) (e2 : Exp r) : Exp (q ⊗ r) := fun Var =>
    pair (e1 Var) (e2 Var).
Definition Let_Pair {q r s} (e : Exp (q ⊗ r)) (f : Exp2 q r s) : Exp s := fun Var =>
    let_pair (e Var) (f Var).

Definition Put {τ : hSet} (x : τ) : Exp (Lower τ) := fun _ => put x.
Definition Let_Bang {τ : hSet} {q} 
           (e : Exp (Lower τ)) (f : τ -> Exp q) : Exp q := fun Var =>
    let_bang (e Var) (fun x => f x Var).

Definition New (b : Bool) : Exp Qubit := if b then Inj1 Unit else Inj0 Unit.

Definition meas {Var} (e : exp Var Qubit) : exp Var (Lower Bool).
  unfold Qubit in e.
  refine (
  case_of e (fun x => let_unit (var x) (put false))
            (fun x => let_unit (var x) (put true)) ).
Defined.
Definition Meas (e : Exp Qubit) : Exp (Lower Bool).
Proof.
  unfold Qubit in e.
  refine (Case_Of e (fun _ x => let_unit (var x) (put false))
                    (fun _ x => let_unit (var x) (put true))).
Defined.


(*************************)
(* Operational semantics *)
(*************************)

Inductive β : forall {q}, Exp q -> Exp q -> Type :=
| β_tensor {q r s} (e1 : Exp q) (e2 : Exp r) (f : Exp2 q r s) : 
    β (Let_Pair (Pair e1 e2) f) (Subst2 f e1 e2)

| β_unit {q} (e : Exp q) : 
    β (Let_Unit Unit e) e

| β_ι0 {q0 q1 r} (e : Exp q0) (f0 : q0 --o r) (f1 : q1 --o r) :
    β (Case_Of (Inj0 e) f0 f1) (Subst f0 e)
| β_ι1 {q0 q1 r} (e : Exp q1) (f0 : q0 --o r) (f1 : q1 --o r) :
    β (Case_Of (Inj1 e) f0 f1) (Subst f1 e)

| β_lower {τ : hSet} {q} (x : τ) (f : τ -> Exp q) :
    β (Let_Bang (Put x) f) (f x)
.


Instance β_relation : forall q, is_mere_relation (Exp q) β.
Admitted. (* should be true because β is type directed *)

Definition βExp q := quotient (@β q).

About class_of.
Notation "[ e ]" := (class_of β e).
Definition β_equiv q (e1 e2 : Exp q) : Type := [e1] = [e2].
Notation "e1 ≡ e2" := (β_equiv _ e1 e2) (at level 50).

Instance β_equiv_refl : forall q, Reflexive (β_equiv q).
Admitted.
Instance β_equiv_trans : forall q, Transitive (β_equiv q).
Admitted.
Instance β_equiv_symm : forall q, Symmetric (β_equiv q).
Admitted.

Ltac is_β_step := apply related_classes_eq; constructor.
Ltac β_step := etransitivity; [is_β_step | ].
Ltac solve_β := repeat (try reflexivity; β_step).
  
Lemma β_qubit : forall b, Meas (New b) ≡ Put b.
Proof.
  destruct b; solve_β.
Qed.

(*************)
(* unitaries *)
(*************)

Definition unitary {q r : QType} (U : q = r) (e : Exp q) : Exp r := transport _ U e.
Definition Unitary (q : QType) := q = q.


Context `{Univalence}.


Section Init.

  Definition pinit {q : PQType} : PBasis Exp q -> Exp (from_PQType q).
  Proof.
    induction q.
    * exact (fun x => x).
    * exact (fun _ => Unit).
    * simpl.
      intros [x y].
      exact (Pair (IHq1 x) (IHq2 y)).
    * simpl.
      intros [x | y].
      + exact (Inj0 (IHq1 x)).
      + exact (Inj1 (IHq2 y)).
    * simpl. exact Put.
  Defined.

  Variable q_in q_out : PQType.
  Context `{FinQType (from_PQType q_in)} `{FinQType (from_PQType q_out)}.
  Variable f : forall Var, PBasis Var q_in -> PBasis Var q_out.
  Let f' : Matrix (Basis (from_PQType q_in)) (Basis (from_PQType q_out)).
  Proof.
    apply (@PBasis_to_Matrix _ _ H1 ). 
    admit (*exact H2.*)(*????*).
    exact f.
  Admitted.

  Variable f_UProp : Unitary_Prop f'.
  Let f_U : from_PQType q_in = from_PQType q_out.
  Proof.
    specialize (@PBasis_to_Unitary q_in q_out H1); intros H.
    assert (H' : forall (f : forall Var, PBasis Var q_in -> PBasis Var q_out),
      Unitary_Prop f' -> from_PQType q_in = from_PQType q_out).
    { admit (*???*).
    }
    apply (H' f f_UProp).
  Admitted.


  Axiom pinit_U : forall (x : PBasis Exp q_in),
        unitary f_U (pinit x) = pinit (f _ x).

End Init.

Section Meas.
  Variable Var : QType -> Type.
  Fixpoint pmeas (q : PQType)
           : forall r, exp Var (from_PQType q) -> (PBasis (exp Var) q -> exp Var r) -> exp Var r.
  Proof.
    destruct q; simpl; intros r e f.
    * (* Hole *) exact (f e).
    * (* Unit *) exact (let_unit e (f tt)).
    * (* Tensor *) 
      refine (let_pair e (fun x y => _)).
      refine (pmeas _ _ (var x) (fun x' => _)).
      refine (pmeas _ _ (var y) (fun y' => _)).
      exact (f (x',y')).
    * (* OPlus *)
      refine (case_of e (fun x => _) (fun y => _)).
      + exact (pmeas _ _ (var x) (fun x' => f (inl x'))).
      + exact (pmeas _ _ (var y) (fun y' => f (inr y'))).
    * (* Lower *)
      refine (let_bang e f).
  Defined.
End Meas.

  Definition PMeas {q r} (e : Exp (from_PQType q))
                         (f : forall Var, PBasis (exp Var) q -> exp Var r)
                       : Exp r.
  Proof.
    intros Var.
    exact (pmeas _ q _ (e _) (f _)).
  Defined.
Section Meas_Ax.

  Variable q_in q_out : PQType.
  Context `{FinQType (from_PQType q_in)} `{FinQType (from_PQType q_out)}.
  Variable f : forall Var, PBasis Var q_in -> PBasis Var q_out.
  Let f' : Matrix (Basis (from_PQType q_in)) (Basis (from_PQType q_out)).
  Proof.
    apply (@PBasis_to_Matrix _ _ H1 ). 
    admit (*exact H2.*)(*????*).
    exact f.
  Admitted.

  Variable f_UProp : Unitary_Prop f'.
  Let f_U : from_PQType q_in = from_PQType q_out.
  Proof.
    specialize (@PBasis_to_Unitary q_in q_out H1); intros H.
    assert (H' : forall (f : forall Var, PBasis Var q_in -> PBasis Var q_out),
      Unitary_Prop f' -> from_PQType q_in = from_PQType q_out).
    { admit (*???*).
    }
    apply (H' f f_UProp).
  Admitted.


  Axiom pmeas_U : forall {r} (e : Exp (from_PQType q_in)) 
                             (g : forall Var, PBasis (exp Var) q_out -> exp Var r),
    PMeas (unitary f_U e) g = PMeas e (fun _ b => g _ (f _ b)).
  
End Meas_Ax.
  

End Meas.

  Let P0 q := Basis q -> Exp q.
  Let P0_One : P0 One := fun _ => Unit.
  Let P0_Tensor q r (initq : P0 q) (initr : P0 r) : P0 (q ⊗ r).
    intros z.
    transparent assert (z' : (Basis q * Basis r)).
    { rewrite <- Basis_Tensor.
      exact z.
    }
    destruct z' as [x y].
    exact (Pair (initq x) (initr y)).
  Defined.
  Let P0_OPlus q r (initq : P0 q) (initr : P0 r) : P0 (q ⊕ r).
    intros z.
    rewrite Basis_OPlus in z.
    unfold P0 in initq, initr.
    destruct z as [x | y].
    * admit (*exact (@Inj0 _ _ (initq x)).*).
    * admit (*exact (Inj1 (initr y)).*).
  Admitted.
  Let P0_Lower {τ} `{IsHSet τ} : P0 (Lower τ).
  Proof.
    intros x.
    exact (Put x).
  Defined.
  About QType_ind.


  Let P0_point := QType_point P0 P0_One P0_Tensor P0_OPlus (@P0_Lower).

  Let P0_cell : forall q r (U : UMatrix q r),
      transport P0 (cell _ U) (P0_point q) = P0_point r.
  Proof.
    intros.
    unfold P0_point.
    admit (*???*).
  Admitted.
    
  Definition Init : forall q, Basis q -> Exp q.
  Proof.
    change (forall q, P0 q).

    apply QType_ind with (P_One := @P0_One)
                         (P_Tensor := @P0_Tensor)
                         (P_OPlus := @P0_OPlus)
                         (P_Lower := @P0_Lower)
                         (QType_cell := P0_cell).
    * intros. unfold P0. exact _.
    * intros q r s U V.
      admit (*??*).
  Admitted.
End Init.

(*
  match q with
  | One           => fun _ => Unit
  | Tensor' q1 q2 => fun x => let (x1,x2) := x in 
                              Pair (Init' q1 x1) (Init' q2 x2)
  | OPlus' q0 q1  => fun x => match x with
                              | inl x0 =#> Inj0 (Init' q0 x0)
                              | inr x1 => Inj1 (Init' q1 x1)
                              end
  | Lower' τ _    => fun x => Put x
  end.
*)
  





Axiom new_matrix : Bool -> Matrix 1 2.
Axiom X' : Matrix 2 2.
Axiom XU : Unitary_Prop X'.
Definition X : Qubit = Qubit.
Proof.
  apply cell.
  exists X'.
  exact XU.
Defined.

Require Import Groupoid.
Open Scope groupoid_scope.


(*
(* Converting a quantum expression to a vector depends on the linear structure
of the expression. *)


Axiom X_new : forall b, X o new_matrix b = new_matrix (negb b).

Inductive equiv : forall {q}, Exp q -> Exp q -> Type :=
| U_new : forall (U : Matrix Qubit' Qubit') b b', 
          U o new_matrix b = new_matrix b' ->
          equiv (unitary (cell _ U) (New b)) (New b')
.
*)


Lemma U_compose : forall q1 q2 q3 (U1 : q1 = q2) (U2 : q2 = q3) (e : Exp q1),
      unitary U2 (unitary U1 e) = unitary (U1 @ U2) e.
Proof.
  destruct U1. intros.
  simpl.
  rewrite concat_1p.
  reflexivity.
Qed.

Lemma U_U_transpose : forall {q : QType} (U : Unitary q) (e : Exp q),
      unitary (U^) (unitary U e) = e.
Proof. 
  intros. rewrite U_compose. rewrite concat_pV. reflexivity.
Defined.

Require Import Groupoid.
Local Open Scope groupoid_scope.


Axiom H' : UMatrix Qubit' Qubit'.
Axiom H'_dag : (H'^ = H')%groupoid.
Definition H : Unitary Qubit := cell _ H'.
Lemma H_dag : H^%path = H.
Proof.
  unfold H.
  rewrite (quotient1_inv _ _ U_groupoid _ _ H').
  rewrite H'_dag.
  reflexivity.
Qed.

Lemma H_H_inverse : forall (e : Exp Qubit), unitary H (unitary H e) = e.
Proof.
  intros.
  refine (_ @ U_U_transpose H e).
  rewrite H_dag.
  reflexivity.
Qed.

Definition U_tensor {q1 q1' q2 q2'} (U1 : q1 = q1') (U2 : q2 = q2') :
           q1 ⊗ q2 = q1' ⊗ q2'.
Proof.
  destruct U1, U2.
  reflexivity.
Defined.

Lemma U_tensor_pair : forall {q1 q1' q2 q2'} (U1 : q1 = q1') (U2 : q2 = q2')
                                             (e1 : Exp q1) (e2 : Exp q2),
      unitary (U_tensor U1 U2) (Pair e1 e2) = Pair (unitary U1 e1) (unitary U2 e2).
Proof.
  destruct U1, U2; intros; auto.
Qed.


Definition U_lolli {Q1 Q1' Q2 Q2'} (U1 : Q1 = Q1') (U2 : Q2 = Q2') : (Q1 ⊸ Q2) = (Q1' ⊸ Q2').
Proof.
  destruct U1.
  destruct U2.
  reflexivity.
Defined.


Definition apply_U_lolli {q1 q1' q2 q2'} (U1 : q1 = q1') (U2 : q2 = q2') 
                    (f : q1 --o q2) : q1' --o q2' := fun _ x => 
  transport _ U2 (f _ (transport _ U1^ x)).

Lemma U_lolli_unitary : forall q1 q1' q2 q2' (U1 : q1 = q1') (U2 : q2 = q2')
                               (f : q1 --o q2),
      unitary (U_lolli U1 U2) (Abs f)
    = Abs (apply_U_lolli U1 U2 f).
Proof.
  destruct U1, U2; intros.
  unfold apply_U_lolli.
  reflexivity.
Qed.

Notation "U1 -u⊸ U2" := (U_lolli U1 U2) (at level 30).
  

Lemma unitary_id : forall Q (e : Exp Q), e = unitary 1 e.
Proof. reflexivity. Defined.

(* CANNOT prove this (which is good) *)
Lemma U_not_id : forall Q (U : Q = Q) (e : Exp Q),
                 unitary U e = e ->
                 U = 1%path.
Abort.



Inductive IsTrue : Bool -> Type :=
| Istrue : IsTrue true.

(* TODO: prove cell H <> 1 *)


Lemma bool_set : forall (b : Bool) (p : b = b), p = 1.
Proof.
  intros. 
  apply hset_bool.
Qed.

Lemma IsTrue_eq : forall b1 b2 (p : b1 = b2) (pf1 : IsTrue b1) (pf2 : IsTrue b2), 
    transport _ p pf1 = pf2.
Proof.
  destruct pf1.
  destruct pf2.
  rewrite (bool_set _ p).
  simpl.
  reflexivity.
Defined.
  

Lemma IsTrue_eq' : forall (pf : IsTrue true), pf = Istrue.
Proof.
  intros. 
  refine (IsTrue_eq _ _ 1 pf Istrue).
Defined.
  

Inductive IsQubit : QType -> Type :=
| IsQ : IsQubit Qubit.
Definition fromQubit {q} (pfQubit : IsQubit q) : Exp Qubit -> Exp q.
Proof.
  destruct pfQubit.
  exact (fun e => e).
Defined.
Definition toQubit {q} (pfQubit : IsQubit q) : Exp q -> Exp Qubit.
Proof.
  destruct pfQubit.
  exact (fun e => e).
Defined.

(* I don't think this lemma is actually true. To prove the corresponding
property for booleans, we rely on the fact that Bool is an HSet, but this is not
true of QType. *)
Lemma IsQubit_eq : forall (pf : IsQubit Qubit), pf = IsQ.
Abort. 
(* If it were true, we could prove the lemmas below *)
(*
Lemma bad : forall q r (U : q = r) (pf_q : IsQubit q) (pf_r : IsQubit r) (e : Exp q),
    unitary U e = fromQubit pf_r (toQubit pf_q e).
Proof.
  destruct U.
  destruct pf_q.
  intros. 
  simpl.
  transitivity (fromQubit IsQ e); [reflexivity | ].
  apply (ap (fun pf => fromQubit pf e)).
  refine (IsQubit_eq _)^.
Defined.

Lemma bad_pos : unitary H (New False) = New False.
Proof.
  exact (bad _ _ H IsQ IsQ _).
Defined.
Lemma bad_flip : Meas (unitary H (New False)) = Meas (New False).
Proof.
  apply ap. apply bad_pos.
Defined
*)


Section measure_discard.

  Variable Var : QType -> Type.

  (* This should be defined mutually recursively with measure_discard *)
(*  Variable prepare0 : forall (q : QType), Exp q. *)

  Fixpoint meas_discard' {q} (e : exp (fun _ => Unit) q) : exp Var (Lower Unit).
  Proof.
    destruct e as [ q x | q r f | q r e1 e2 (* abstraction *)
                  | q r e1 e2 | q r s e e' (* pairs *)
                  | τ H x | τ H q e e' (* let! *)
                  | | e (* new *) ].
    * exact (put x).
    * apply (meas_discard' _ (f tt)).
    * exact (let_bang (meas_discard' _ e1) (fun _ => 
             let_bang (meas_discard' _ e2) (fun _ =>
             put tt))).
    * exact (let_bang (meas_discard' _ e1) (fun _ => 
             let_bang (meas_discard' _ e2) (fun _ =>
             put tt))).
    * exact (let_bang (meas_discard' _ e) (fun _ =>
             meas_discard' _ (e' tt tt))).
    * exact (put tt).
    * admit (*exact (let_bang e (fun x => meas_discard' _ (e' x))).*).
    * exact (put tt).
    * exact (meas_discard' _ e).
  Admitted.

End measure_discard.

Definition Meas_Discard {q} (e : Exp q) : Exp (Lower Unit) :=
  fun _ => meas_discard' _ (e _).


Section meas_all.

  Variable Var : QType -> Type.

  Fixpoint meas_all {q} (pf : QData q) (e : exp Var q) : exp Var (Lower (Basis pf)).
  Proof.
    destruct pf.
    * (* Qubit *) exact (meas e).
    * (* Tensor *)
      refine (let_pair e (fun x₁ x₂ => _)).
      refine (let_bang (meas_all q1 pf1 (var x₁)) (fun y₁ => _)).
      refine (let_bang (meas_all q2 pf2 (var x₂)) (fun y₂ => _)).
      refine (put (y₁,y₂)).
    * (* Lower *)
      exact e.
  Defined.

End meas_all.
Arguments meas_all {Var} {q} {pf} e.

Definition Meas_All {q} (pf : QData q) : Exp q -> Exp (Lower (Basis pf)) :=
  fun e _ => meas_all (e _).

Definition transport_meas_all {q r} (pf_q : QData q)(U : q = r) (e : Exp q)
    : Exp (Lower (Basis (transport _ U pf_q))).
Proof.
  set (P := fun τ => Exp (Lower τ)).
  exact (transport P (Basis_eq _ _ pf_q U)^ (Meas_All pf_q e)).
Defined.

Lemma meas_all_U : forall {q r} (pf_q : QData q) (U : q = r)
                          (e : Exp q),
      Meas_All (transport (fun σ => QData σ) U pf_q) (unitary U e)
    = transport_meas_all pf_q U e.
Proof.
  intros.
  unfold transport_meas_all.
  destruct U. simpl. reflexivity.
Qed.

Lemma Basis_Qubit_eq : forall {q} (U : Qubit = q),
      Basis (U # QubitData) = Bool.
Proof.
  intros.
  refine (Basis_eq _ _ _ _).
Defined.

Lemma meas_U' : forall {q} (U : Qubit = q) (e : Exp q),
      Meas (unitary U^ e) 
    = transport (fun τ => Exp (Lower τ)) (Basis_Qubit_eq U) 
                (Meas_All (U # QubitData) e).
Proof.
  destruct U; intros.
  simpl.
  reflexivity.
Qed.

Lemma meas_U : forall (U : Unitary Qubit) (e : Exp Qubit),
      Meas (unitary U e) 
    = transport (fun τ => Exp (Lower τ)) (Basis_Qubit_eq U^) 
                (Meas_All (U^ # QubitData) e).
Proof.
  intros.
  refine (_ @ meas_U' U^ e).
  apply (ap (fun p => Meas (unitary p e))).
  apply (inv_V _)^.
Qed.


Lemma meas_discard_U : forall {q r s} (pf_q : QData q)
                              (U : q = r)
                              (e : Exp q) (e' : Exp s),
      Let_Bang (Meas_All (U # pf_q) (unitary U e)) (fun _ => e')
    = Let_Bang (Meas_All pf_q e) (fun _ => e').
Proof.
  intros.
  destruct U.
  reflexivity.
Qed.
(* Can I instead define Meas_All by induction on QType, instead of QData? *)

Lemma Meas_All_QubitData : 
      Meas_All QubitData = Meas.
Proof. reflexivity. Qed.

Definition U_meas  {q} (U : Qubit = q) (e : Exp Qubit) : Exp (Lower Bool).
Proof.
  destruct U.
  exact (Meas e).
Defined.

Lemma meas_discard_U_Qubit' : forall {q r} (U : Qubit = q) (e : Exp q) (e' : Exp r),
      Let_Bang (Meas (unitary U^ e))  (fun _ => e')
    = Let_Bang (Meas_All (U # QubitData) e) (fun _ => e').
Proof.
  destruct U.
  intros.
  reflexivity.
Qed.

(* This is not quite true due to the obnoxious QData terms *)
Lemma meas_discard_U_Qubit : forall {q} (U : Unitary Qubit) 
                                    (e : Exp Qubit) (e' : Exp q),
      Let_Bang (Meas (unitary U e)) (fun _ => e')
    = Let_Bang (Meas e) (fun _ => e').
Proof.
  intros.
  transitivity (Let_Bang (Meas_All QubitData e) (fun _ : Bool => e')); 
    [ | reflexivity].
  rewrite <- (inv_V U).
  rewrite meas_discard_U_Qubit'.
  rewrite meas_discard_U.

Abort. 


(*
Section meas_all.

  Variable Var : QType -> Type.
  Context `{Univalence}.

  Lemma Lower_to_classical_lolli : forall q r, Lower (to_classical (q ⊸ r)) = Lower Unit.
  Admitted.



  Fixpoint meas_all {q} (e : exp to_classical q) : exp Var (Lower (to_classical q)).
  Proof.
    destruct e as [ q x | q r f | q r e1 e2 (* abstraction *)
                  | q r e1 e2 | q r s e e' (* pairs *)
                  | τ H x | τ H q e e' (* let! *)
                  | | e (* new *) ].
    * exact (put x).
    * rewrite Lower_to_classical_lolli.
      exact (put tt).
    * set (e1' := meas_all _ e1). rewrite Lower_to_classical_lolli in e1'.
      set (e2' := meas_all _ e2).
      rewrite to_classical_lolli in e1'.
      exact (app e1' e2').
    * rewrite to_classical_tensor.
      exact (pair (meas_all _ _ e1) (meas_all _ _ e2)).
    * set (e0 := meas_all _ _ e). 
      rewrite to_classical_tensor in e0. 
      exact (let_pair e0 (fun x y => meas_all _ _ (e' x y))).
    * exact (put x).
    * exact (let_bang (meas_all _ _ e) (fun x => meas_all _ _ (e' x))).
    * exact (put b).
    * exact (meas_all _ _ e).
  Defined.

(*
  Fixpoint meas_all {q} {Var} (e : exp (fun r => Var (to_classical r)) q) : exp Var (to_classical q).
  Proof.
    destruct e as [ q x | q r f | q r e1 e2 (* abstraction *)
                  | q r e1 e2 | q r s e e' (* pairs *)
                  | τ H x | τ H q e e' (* let! *)
                  | | e (* new *) ].
    * exact (var x).
    * rewrite to_classical_lolli.
      refine (abs (fun x => meas_all _ _ (f x))).
    * set (e1' := meas_all _ _ e1).
      set (e2' := meas_all _ _ e2).
      rewrite to_classical_lolli in e1'.
      exact (app e1' e2').
    * rewrite to_classical_tensor.
      exact (pair (meas_all _ _ e1) (meas_all _ _ e2)).
    * set (e0 := meas_all _ _ e). 
      rewrite to_classical_tensor in e0. 
      exact (let_pair e0 (fun x y => meas_all _ _ (e' x y))).
    * exact (put x).
    * exact (let_bang (meas_all _ _ e) (fun x => meas_all _ _ (e' x))).
    * exact (put b).
    * exact (meas_all _ _ e).
  Defined.
*)

End meas_all.

Definition Meas_All {q} (e : Exp q) : Exp (to_classical q) :=
  fun Var => meas_all (e _).
  

Lemma unitary_discard' `{Univalence} : 
      forall {q1 q2} (U : q1 = q2) {q} (e1 : Exp q1) (e : Exp q),
      Let_Bang (Meas_All (unitary U e1)) (fun _ => e) 
    = Let_Bang (Meas_All e1) (fun _ => e).
Proof.
  destruct U; intros.
  reflexivity.
Qed.

Lemma Meas_All_Qubit `{Univalence} : forall (e : Exp Qubit),
    Meas_All e = Meas e.
Proof.
  intros e. apply path_forall; intros var.
  unfold Meas_All.

Lemma unitary_discard `{Univalence} : 
      forall (U : Unitary Qubit) {q} (e : Exp Qubit) (e' : Exp q),
      Let_Bang (Meas (unitary U e)) (fun _ => e')
    = Let_Bang (Meas e) (fun _ => e').
Proof.
  intros.
  set (p := unitary_discard' U e e').
  simpl in p.

*)