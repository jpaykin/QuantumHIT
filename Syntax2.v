Require Import HoTT.
Require Import quotient1.
Require Import QTypes2.

(* P x = P0 x -> P1 x *)
Lemma transport_fun : forall A (P0 P1 : A -> Type) (x y : A) (p : x = y) (a : P0 x -> P1 x),
      transport (fun z => P0 z -> P1 z) p a 
    = fun z : P0 y => transport P1 p (a (transport P0 p^ z)).
Proof.
  destruct p.
  intros.
  simpl.
  reflexivity.
Qed.


Section Syntax.
Context `{uni : Univalence}.
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

About transport.


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

  Instance exp1_trunc : forall q r, IsTrunc 1 (q --o r).
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
  Variable f : forall Var, PBasis Var q_in <~> PBasis Var q_out.
Require Import Matrix2.
  Let f' : Matrix (Basis (from_PQType q_in)) (Basis (from_PQType q_out)).
  Proof.
    apply (@PBasis_to_Matrix _ _ _).
    exact f.
  Defined.

  Variable f_UProp : UnitaryProp f'.
  Let f_U : from_PQType q_in = from_PQType q_out.
  Proof.
    apply (@PBasis_to_Unitary _ q_in q_out f).
    exact f_UProp.
  Defined.

(*
  Axiom pinit_U : forall (x : PBasis Exp q_in),
        unitary f_U (pinit x) = pinit (f _ x).
*)

End Init.


Section meas_all.

  Existing Instance Basis'_HSet.
  Fixpoint meas_all' (q : QType') : point _ q --o Lower (Basis' q).
  Proof.
    destruct q.
    - intros Var x. refine (let_unit (var x) (put tt)).
    - intros Var x. 
      set (y := (x : Var (OPlus (point _ q1) (point _ q2)))).
      refine (case_of (var y) (fun x => _) (fun x => _)).
      * refine (let_bang (meas_all' q1 _ x) (fun z => put (inl z))).
      * refine (let_bang (meas_all' q2 _ x) (fun z => put (inr z))).
    - intros Var x.
      set (y := (x : Var (Tensor (point _ q1) (point _ q2)))).
      refine (let_pair (var y) (fun z1 z2 => _)).
      refine (let_bang (meas_all' q1 _ z1) (fun z1' => _)).
      refine (let_bang (meas_all' q2 _ z2) (fun z2' => _)).
      refine (put (z1', z2')).
    - intros Var x. simpl.
      set (y := (x : Var (Lower τ))). 
      set (e' := let_bang (var y) (fun z => put z)).
      simpl in *.
      exact e'.
  Defined.

  Let P := fun q => q --o Lower (Basis q).

  Lemma meas_all_cell : forall (q r : QType') (U : Unitary' q r),
        transport P (cell Q_groupoid U) (meas_all' q) = meas_all' r.
  Admitted.

  Open Scope groupoid_scope.
  Existing Instance exp1_trunc.
  Definition meas_all : forall (q : QType), q --o Lower (Basis q).
  Proof.
    eapply quotient1_ind with (P_point := meas_all')
                              (P_cell := meas_all_cell).
    - exact _.
    - intros. (* since (q --o Lower (Basis q)) isn't a set, still need to prove
      this part *)
  Admitted.

End meas_all.

Section PMeas.
  Variable HVar : QType -> Type.
  Variable Var : QType -> Type.
  Variable from_HVar : forall q, exp Var q -> HVar q.

  Fixpoint pmeas (q : PQType)
           : forall r, exp Var (from_PQType q) -> (PBasis HVar q -> exp Var r) -> exp Var r.
  Proof.
    destruct q; simpl in *; intros r e f.
    * (* Hole *) exact (f (from_HVar _ e)).
    * (* Unit *) exact (let_unit e (f tt)).
    * (* Tensor *) simpl in *.
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


End PMeas.


  Fixpoint meas_all {Var} {q : QType} (e : exp Var q) : exp Var (Lower (Basis q)).
  Proof.
    refine (pmeas (fun s => exp Var (Lower (Basis s))) _ _ (Hole q) _ e idmap).
    * intros r e'. exact (meas_all _ r e').
  Abort (* this doesn't have decreasing fixpoint value *).



  Definition PMeas {q r} (e : Exp (from_PQType q))
                         (f : forall Var, PBasis (exp Var) q -> exp Var r)
                       : Exp r.
  Proof.
    intros Var.
    exact (pmeas _ _ (fun _ x => x) q _ (e _) (f _)).
  Defined.
Section Meas_Ax.

  Variable q_in q_out : PQType.
  Context `{@FinQType uni (from_PQType q_in)} `{@FinQType uni (from_PQType q_out)}.
  Variable f : forall Var, PBasis Var q_in -> PBasis Var q_out.

  Variable f_UProp : Unitary_Prop (f' _ _ f).



  Axiom pmeas_U : forall {r} (e : Exp (from_PQType q_in)) 
                             (g : forall Var, PBasis (exp Var) q_out -> exp Var r),
    PMeas (unitary (f_U _ _ f f_UProp) e) g = PMeas e (fun _ b => g _ (f _ b)).
  
End Meas_Ax.
  





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


Axiom H' : Matrix (Basis Qubit) (Basis Qubit).
Axiom H'_Unitary : Unitary_Prop H'.

Existing Instance M_sym.
Axiom H'_dag : (H'^ = H')%groupoid.
Definition H'_U : UMatrix (OPlus' One' One') (OPlus' One' One').
  econstructor.
  exact H'_Unitary.
Defined.
Lemma H'_U_dag : H'_U^ = H'_U.
Proof.
  unfold H'_U. simpl.
  generalize H'_dag; intros H. simpl in H.
Admitted.
Definition H : Unitary Qubit := cell _ H'_U.
Lemma H_dag : H^%path = H.
Proof.
  unfold H.
  rewrite (quotient1_inv _ _ U_groupoid _ _ H'_U).
  rewrite H'_U_dag.
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
  refine (ap (fun q => q ⊗ q2) U1 @ ap _ U2).
Defined.

Lemma U_tensor_pair : forall {q1 q1' q2 q2'} (U1 : q1 = q1') (U2 : q2 = q2')
                                             (e1 : Exp q1) (e2 : Exp q2),
      unitary (U_tensor U1 U2) (Pair e1 e2) = Pair (unitary U1 e1) (unitary U2 e2).
Proof.
  destruct U1, U2; intros; auto.
Qed.

  

Lemma unitary_id : forall Q (e : Exp Q), e = unitary 1 e.
Proof. reflexivity. Defined.

(* CANNOT prove this (which is good) *)
Lemma U_not_id : forall Q (U : Q = Q) (e : Exp Q),
                 unitary U e = e ->
                 U = 1%path.
Abort.

(* This only works if q does not have any holes in it *)
Inductive NoHoles : PQType -> Type :=
| NHOne : NoHoles POne
| NHTensor {q1 q2} : NoHoles q1 -> NoHoles q2 -> NoHoles (PTensor q1 q2)
| NHOPlus {q1 q2} : NoHoles q1 -> NoHoles q2 -> NoHoles (POPlus q1 q2)
| NHLower {τ} `{IsHSet τ} : NoHoles (PLower τ).
Class no_holes (q : PQType) := {has_no_holes : NoHoles q}.
Instance no_holes_One : no_holes POne := { has_no_holes := NHOne }.
Instance no_holes_Tensor {q1 q2} `{nh1 : no_holes q1} `{nh2 : no_holes q2} :no_holes (PTensor q1 q2).
Proof.
    destruct nh1, nh2.
    constructor.
    exact (NHTensor has_no_holes0 has_no_holes1).
Qed.

Definition no_holes_OPlus {q1 q2} `{nh1 : no_holes q1} `{nh2 : no_holes q2} :no_holes (POPlus q1 q2).
Proof.
    destruct nh1, nh2.
    constructor.
    exact (NHOPlus has_no_holes0 has_no_holes1).
Qed.
Definition no_holes_Lower {τ} `{IsHSet τ} : no_holes (PLower τ).
Proof.
    constructor.
    exact (NHLower).
Qed.

Lemma NoHoles_Hole_inv : forall q, ~ NoHoles (Hole q).
Admitted.
Lemma no_holes_Hole_inv : forall q, ~ no_holes (Hole q).
Proof.
  intros q [H].
  apply NoHoles_Hole_inv in H. auto.
Qed.

Lemma no_holes_Tensor_inv : forall q1 q2, no_holes (PTensor q1 q2) -> no_holes q1 * no_holes q2.
Admitted.
Lemma no_holes_OPlus_inv : forall q1 q2, no_holes (POPlus q1 q2) -> no_holes q1 * no_holes q2.
Admitted.


Lemma no_holes_PBasis : forall q `{no_holes q} (Var1 Var2 : QType -> Type), 
      PBasis Var1 q = PBasis Var2 q.
Proof.
  induction q; intros nh_q Var1 Var2; simpl.
  * apply no_holes_Hole_inv in nh_q. contradiction.
  * reflexivity.
  * apply no_holes_Tensor_inv in nh_q.
    destruct nh_q.
    erewrite IHq1, IHq2; auto.
  * apply no_holes_OPlus_inv in nh_q.
    destruct nh_q.
    erewrite IHq1, IHq2; auto.
  * reflexivity.
Qed.


Instance basis_HSet q : IsHSet (Basis q).
Proof.
  unfold Basis. exact _.
Qed.
(*
Definition Meas_All q `{no_holes q} (e : Exp (from_PQType q)) : Exp (Lower (Basis (from_PQType q))).
  refine (PMeas e (fun x b => put _)).
  simpl.
  set (b' := transport idmap (no_holes_PBasis _ (exp x) Basis) b). simpl in b'.
  apply pbasis_basis. 
(*    Set Printing Universes.
  exact b'.*)
Admitted.

Definition Meas_Discard q `{no_holes q}
           (e : Exp (from_PQType q)) : Exp (Lower Overture.Unit) :=
  Let_Bang (Meas_All q e) (fun _ => Put tt).

Lemma Meas_Discard_U : forall q r (U : from_PQType q = from_PQType r)
*)

(*
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
*)



Section measure_discard.

  Variable Var : QType -> Type.

  (* This should be defined mutually recursively with measure_discard *)
(*  Variable prepare0 : forall (q : QType), Exp q. *)

  Fixpoint meas_discard' {q} (e : exp (fun _ => Overture.Unit) q) 
                                : exp Var (Lower Overture.Unit).
  Proof.
    destruct e as [ q x 
                  | q r e1 e2 | q r s e e' (* pairs *)
                  | | q e e' (* unit *)
                  | q0 q1 e | q0 q1 e | q0 q1 r e f0 f1
                  | τ H x | τ H q e e' (* let! *)].
    * exact (put x).
    * exact (let_bang (meas_discard' _ e1) (fun _ => 
             let_bang (meas_discard' _ e2) (fun _ =>
             put tt))).
    * exact (let_bang (meas_discard' _ e) (fun _ =>
             meas_discard' _ (e' tt tt))).
    * exact (put tt).
    * refine (let_bang (meas_discard' _ e) (fun _ =>
              let_bang (meas_discard' _ e') (fun _ =>
              put tt))).
    * refine (meas_discard' _ e).
    * refine (meas_discard' _ e).
    * admit (*refine (let_unit e (meas_discard' _ e'))*).
    * exact (put tt).
    * admit (*exact (let_bang e (fun x => meas_discard' _ (e' x))).*).
  Admitted.

End measure_discard.

Definition Meas_Discard {q} (e : Exp q) : Exp (Lower Overture.Unit) :=
  fun _ => meas_discard' _ (e _).

Lemma Meas_Discard_U : forall {q r} (U : q = r) (e : Exp q),
    Meas_Discard (U # e) = Meas_Discard e.
Proof.
  destruct U; intros.
  reflexivity.
Qed.

(*
Lemma Meas_Discard_Qubit : forall (e : Exp Qubit),
    Meas_Discard e = Case_Of e (fun _ z => let_unit (var z) (put tt))
                               (fun _ z => let_unit (var z) (put tt)).
*)


End Syntax.