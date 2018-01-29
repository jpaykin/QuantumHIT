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

(*
Definition New (b : Bool) : Exp Qubit := if b then Put true else Put false.

Definition Meas (e : Exp Qubit) : Exp (Lower Bool).
  unfold Qubit in e.
  refine (Let_Bang e Put).
Defined.
*)


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

Lemma β_cong_Let_Bang : forall α `{IsHSet α} q
    (e e' : Exp (Lower α)) (f f' : α -> Exp q) 
    (pf1 : e ≡ e') (pf2 : forall a, f a ≡ f' a),
    Let_Bang e f ≡ Let_Bang e' f'.
Admitted.
(* need to lift Let_Bang to βExp, I think *) 

(*  
Lemma β_qubit : forall b, Meas (New b) ≡ Put b.
Proof.
  destruct b; solve_β.
Qed.
*)

(*************)
(* unitaries *)
(*************)

Definition unitary {q r : QType} (U : q = r) (e : Exp q) : Exp r := transport _ U e.
Definition Unitary (q : QType) := q = q.

(******************)
(* Groupoid rules *)
(******************)

Lemma U_Eq : forall q r (U V : q = r) (pf : U = V) (e : Exp q),
    U # e = V # e.
Proof.
  intros q r U V pf e. destruct pf; reflexivity.
Qed.

Lemma U_Compose : forall {q r s} (U : q = r) (V : r = s) (e : Exp q),
    V # U # e = (U @ V) # e.
Proof.
  destruct U; intros. simpl.
  rewrite concat_1p.
  reflexivity.
Qed.

Lemma U_I : forall q (e : Exp q), 1 # e = e.
Proof.
  reflexivity.
Qed.


(********************)
(* Structural rules *)
(********************)

Lemma U_Tensor_I : forall q1 q2 r1 r2 (U1 : q1 = r1) (U2 : q2 = r2)
                   (e1 : Exp q1) (e2 : Exp q2),
    ap2 Tensor U1 U2 # Pair e1 e2 = Pair (U1 # e1) (U2 # e2).
Proof.
  destruct U1, U2. intros.
  reflexivity.
Qed.

Lemma U_Tensor_E : forall q1 q2 r1 r2 s (U1 : q1 = r1) (U2 : q2 = r2)
                   (e : Exp (q1 ⊗ q2)) (f : Exp2 r1 r2 s),
    Let_Pair (ap2 Tensor U1 U2 # e) f 
  = Let_Pair e (fun _ x1 x2 => f _ (U1 # x1) (U2 # x2)).
Proof.
  destruct U1, U2; intros.
  reflexivity.
Qed.

Lemma U_Tensor_comm : forall q1 q2 r s (U : r = s) 
                      (e : Exp (q1 ⊗ q2)) (f : Exp2 q1 q2 r),
    U # Let_Pair e f = Let_Pair e (fun _ x1 x2 => U # (f _ x1 x2)).
Proof.
  destruct U; intros.
  reflexivity.
Qed.

Lemma U_OPlus_I0 : forall q0 q1 r0 r1 (U0 : q0 = r0) (U1 : q1 = r1)
                          (e : Exp q0),
    ap2 OPlus U0 U1 # Inj0 e = Inj0 (U0 # e).
Proof.
  destruct U0, U1; intros; reflexivity.
Qed.
Lemma U_OPlus_I1 : forall q0 q1 r0 r1 (U0 : q0 = r0) (U1 : q1 = r1)
                          (e : Exp q1),
    ap2 OPlus U0 U1 # Inj1 e = Inj1 (U1 # e).
Proof.
  destruct U0, U1; intros; reflexivity.
Qed.
About Case_Of.
Lemma U_OPlus_E : forall q0 q1 r0 r1 s (U0 : q0 = r0) (U1 : q1 = r1)
                  (e : Exp (q0 ⊕ q1)) (f0 : r0 --o s) (f1 : r1 --o s),
    Case_Of (ap2 OPlus U0 U1 # e) f0 f1
  = Case_Of e (fun _ x0 => f0 _ (U0 # x0)) (fun _ x1 => f1 _ (U1 # x1)).
Proof.
  destruct U0, U1; intros; reflexivity.
Qed.
Lemma U_OPlus_comm : forall q0 q1 r s (U : r = s)
                     (e : Exp (q0 ⊕ q1)) (f0 : q0 --o r) (f1 : q1 --o r),
    U # Case_Of e f0 f1 
  = Case_Of e (fun _ x0 => U # f0 _ x0) (fun _ x1 => U # f1 _ x1).
Proof.
  destruct U; intros; reflexivity.
Qed.

Definition Lower0 (α : 0-Type) := Lower α.

Lemma U_Lower_E : forall (α β : 0-Type) (pf : α = β) q
                         (e : Exp (Lower α)) (f : β -> Exp q),
    Let_Bang (transport (fun X => Exp (Lower0 X)) pf e) f 
  = Let_Bang e (fun a => f (transport _ pf a)).
Proof.
    destruct pf. intros. reflexivity.
Qed.


Lemma U_Lower_comm : forall α `{IsHSet α} q r (U : q = r)
                            (e : Exp (Lower α)) (f : α -> Exp q),
    U # (Let_Bang e f) = Let_Bang e (fun a => U # (f a)).
Proof.
  destruct U; intros; reflexivity.
Qed.

Lemma U_Lower_distr : forall α β `{IsHSet α} `{IsHSet β} q (U : Lower α = Lower β)
                         (e : Exp (Lower α)) (e' : Exp q),
    Let_Bang (U # e) (fun _ => e') = Let_Bang e (fun _ => e').
Abort.



(* Initialization and measurement *)    

Section Init.


  Definition Init (q : QType) (e : Exp (QBasis q)) : Exp q := (QINIT q # e).

  Require Import Groupoid.  
  Open Scope groupoid_scope.

  Lemma QINIT_Lower : forall α `{IsHSet α},
    QINIT (Lower α) = 1.
  Proof.
    intros.
    apply quotient1_1.
  Defined.

  Lemma Init_Lower α `{IsHSet α} (e : Exp (QBasis (Lower α))) : 
    Init (Lower α) e = e.
  Proof.
    unfold Init.
    rewrite QINIT_Lower.
    reflexivity.
  Qed.

  Lemma U_Init : forall q r (U : q = r) (e : Exp (QBasis q)),
    U # Init q e = Init r (transport (fun s => Exp (QBasis s)) U e).
  Proof.
    intros.
    unfold Init.
    refine ((transport_pp _ _ _ _)^ @ _).
    rewrite QINIT_compose. (* MAIN LEMMA *)
    refine (transport_pp _ _ _ _ @ _).
    apply ap.
    apply (transport_compose _ _ _ _)^.
  Defined.
  

End Init.

Section Meas.

  Inductive Basis : QType -> Type :=
  | basis {q'} : Basis' q' -> Basis (point _ q').
(*  | bPair {q1 q2} : Basis q1 -> Basis q2 -> Basis (q1 ⊗ q2)
  | bPut {α} `{IsHSet α} : α -> Basis (Lower α).
*)
  Inductive IsPoint : QType -> Type :=
  | isPoint' q' : IsPoint (point _ q').

  Existing Instance Basis'_HSet.

  (* Can't even express Lower (Basis q) because Basis q is not an HSet *)
  Definition Init_Basis {q} (b : Basis q) : Exp q.
    destruct b as [q' b].
    refine ((QINIT (point _ q')) # Put b).
  Defined.

  Definition Init_Basis_Lower {q'} (b : Basis (point _ q')) 
             : Exp (Lower (Basis' q')).
  Proof.
    set (e := Init_Basis b).
    refine ((QINIT (point _ q'))^ # e).
  Defined.

  Lemma Init_Basis_Put : forall {q'} (b : Basis' q'),
    Init_Basis_Lower (basis b) = Put b.
  Proof.
    intros. 
    unfold Init_Basis_Lower.
    unfold Init_Basis. 
    rewrite <- transport_pp.
    rewrite concat_pV.
    reflexivity.
  Qed.
(*
  Lemma Init' q r' : Basis q -> q = point _ r' -> Exp (Lower (Basis' r')).
  Proof.
    intros [q' b] U.
    set (e := Init (Lower (Basis' q')) (Put b) : Exp (QBasis (point _ q'))).
    set (e' := transport (fun s => Exp (QBasis s)) U e).
    exact e'.
  Defined.
  Definition Init'' {q'} (b : Basis (point _ q')) : Exp (Lower (Basis' q')) :=
    Init' _ _ b 1.
  Definition Init''' q (b : Basis q) : Exp (QBasis q).
    destruct b as [q' b].
    exact (Init' _ _ (basis _ b) 1).
  Defined.
  Definition Init'''' {q} (b : Basis q) : Exp q.
  Proof.
    destruct b as [q' b].
*)
    


  (* I feel like IsPoint is wrong, but...??? *)
  Definition Meas {q r} : IsPoint q -> Exp q -> (Basis q -> Exp r) -> Exp r.
  Proof.
    intros [q'] e f.
    set (e' := (((QINIT (point _ q'))^ # e) : Exp (Lower (Basis' q')))).
    refine (Let_Bang e' (fun b => f (basis b))). 
  Defined.


  Lemma Meas_Lower {α} `{IsHSet α} {r} : forall (e : Exp (Lower α)) (f : α -> Exp r),
      Meas (isPoint' _) e (fun (x : Basis (Lower α)) =>
      Let_Bang (Init_Basis_Lower x) (fun (y : α) => f y))
    ≡ Let_Bang e f.
  Proof.
    intros e f.
    unfold Meas.
    simpl. 
    
    Open Scope groupoid_scope.
    Require Import Matrix2.
    simpl. Existing Instance UMatrix_refl. 
    assert (eq : Matrix2.UMatrix_refl α = 1) by reflexivity.
    rewrite eq; clear eq.
    rewrite (quotient1_1 _ _ Q_groupoid (Lower' α)).
    simpl.


    transitivity (Let_Bang e (fun a => Let_Bang (Put a) f)).
    * apply ap. apply ap.
      apply path_arrow; intros a; simpl in a. 
      rewrite Init_Basis_Put.
      reflexivity.
    * apply β_cong_Let_Bang; [reflexivity | ].
      intros a.
      apply related_classes_eq.
      constructor.
  Defined.
    


  Lemma Meas_commute : forall q r s (U : q = r) (pf_q : IsPoint q)
                                    (e : Exp q) (f : Basis r -> Exp s),
      Meas (U # pf_q) (U # e) f
    = Meas pf_q e (fun x : Basis q => f (U # x)).
  Proof.
    destruct U; intros.
    simpl.
    reflexivity.
  Qed.


  Definition η {q} (pf : IsPoint q) (e : Exp q) : Exp q :=
    Meas pf e (fun b => Init_Basis b).
  

  Lemma Let_Bang_η : forall α `{IsHSet α} q (U : Lower α = q) (e : Exp q),
      Let_Bang (U^ # e) (fun a => U # Put a) 
    = η (transport _ U (isPoint' _)) e.
  Proof.
    destruct U. intros e. simpl.

    simpl. Existing Instance UMatrix_refl. 
    assert (eq : Matrix2.UMatrix_refl α = 1) by reflexivity.
    rewrite eq; clear eq.
    rewrite (quotient1_1 _ _ Q_groupoid (Lower' α)).
    simpl.
    
    reflexivity.
  Qed.

  

  Lemma Meas_discard : forall q r s (U : q = r) (pf : IsPoint q) 
                              (e : Exp q) (e' : Exp s),
      Meas (U # pf) (U # e) (fun _ => e')
    = Meas pf e (fun _ => e').
  Proof.
    intros.
    rewrite Meas_commute.
    reflexivity.
  Qed.

  Lemma LetBang_discard : forall α β `{IsHSet α} `{IsHSet β} q 
                          (U : Lower α = Lower β)
                          (e : Exp (Lower α)) (e' : Exp q),
      Let_Bang (U # e) (fun _ => e') ≡ Let_Bang e (fun _ => e').
  Proof.
    intros α β IsHSetα IsHSetβ q U e e'.
    simpl.

    set (H := Meas_discard (Lower α) (Lower β) q U (isPoint' _) e e').
    simpl in H.


    assert (eq : Matrix2.UMatrix_refl α = 1) by reflexivity.
    rewrite eq in H; clear eq.
    rewrite (quotient1_1 _ _ Q_groupoid (Lower' α)) in H.
    simpl in H.
    rewrite <- H.

    

    


    set (H' := @Meas_Lower _ _ _ ().
    

    transitivity (Meas (isPoint' _) e (fun (x : Basis (Lower α)) =>
                  Let_Bang (Init_Basis_Lower x) (fun _ => e')));
      [ | apply Meas_Lower].
    simpl.

    transitivity (Meas (transport IsPoint U (isPoint' (Lower' α)))
                       (U # e) (fun _ => e') ).
    * admit.
    * apply Meas_Lower.

    assert (Meas (transport IsPoint U (isPoint' (Lower' α))) (U # e) (fun _ => e')
          ≡ Let_Bang e (fun _ => e')).
    simpl in H.
    


    refine (ap _ (Meas_Lower _ _) @ _).
    rewrite <- Meas_Lower.

    simpl in H.
    


  Let Meas_Type q := forall r (U : q = r), Exp q -> Exp (QBasis r).
  Definition Meas_point : forall q', Meas_Type (point Q_groupoid q').
  Proof.
    intros q' r V e.
    refine (Let_Bang ((QINIT (point _ q'))^ # e) (fun a => 
            ap QBasis V # Put a)).
  Defined.

  Lemma Meas_point_compose' : forall q' r' (U : Unitary' q' r') s 
                                           (V : point _ q' = s) 
                                           (e : Exp (point _ q')),
      Meas_point q' s V e 
    = Meas_point r' s ((cell Q_groupoid U)^ @ V) (cell Q_groupoid U # e).
  Proof.
    intros q' r' U s V e.
    unfold Meas_point.



  Let Meas_Type (q : QType) := Exp q -> Exp (QBasis q).
  
  Definition Meas_point : forall (q' : QType'), Meas_Type (point Q_groupoid q').
  Proof.
    intros q'.
    intros e.
    simpl.
    unfold QBasis'.
    exact (Let_Bang ((QINIT (point _ q'))^ # e) Put).
  Defined.

  Existing Instance Unitary'_HSet.
  Existing Instance Unitary'_sym.

  Lemma Meas_point_compose' : forall q' r' (U : Unitary' q' r') (e : Exp (point _ q')),
      transport (fun s => Exp (QBasis s)) (cell Q_groupoid U) (Meas_point q' e)
    = Meas_point r' (cell Q_groupoid U # e).
  Proof.
    intros.
    rewrite transport_compose.
    rewrite U_Lower_comm.

    unfold Meas_point.

    rewrite <- transport_pp.
    rewrite <- inv_pV.
    rewrite QINIT_compose.
    rewrite inv_pp.
    rewrite inverse_ap.
    rewrite inv_V.
    rewrite transport_pp.

    set (H := U_Lower_E).
    
    rewrite quotient1_rec_cell; unfold QBasis_cell.


    change ( Let_Bang ((QINIT (point _ q'))^ # e) (fun a => cell _ U # Put a)
           = Let_Bang (cell _ U # (QINIT (point _ q'))^ # e) Put ).

    rewrite inv_Vp.

    assert (cell Q_groupoid U @ (QINIT (point Q_groupoid r'))^
            = (QINIT (point Q_groupoid r') @ cell Q_groupoid (U^)%groupoid)^).
    { Search (_ @ _)^.
      rewrite inv_
    }

    Search (_ @ _^).
    rewrite <- QINIT_compose.

    

    (* doesn't help... *)
  Admitted.

  Lemma Meas_point_compose : forall q' r' (U : Unitary' q' r'),
    transport _ (cell Q_groupoid U) (Meas_point q') = Meas_point r'.
  Proof.
    intros q' r' U.
    apply path_arrow. intros e.
    rewrite transport_fun.
    rewrite Meas_point_compose'. 
    apply ap.
    rewrite <- transport_pp.
    rewrite concat_Vp.
    reflexivity.

    unfold Meas_point. 
    rewrite <- transport_pp.
    rewrite <- inv_pp.
    rewrite QINIT_compose.
    rewrite transport_compose.
    rewrite U_Lower_comm.
    repeat rewrite quotient1_rec_cell. unfold QBasis_cell.
    





  Definition Meas : forall q, Exp q -> Exp (QBasis q).
  Proof.
    apply quotient1_ind.
End Meas.

(*
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

  Definition PEquiv (p₁ p₂ : PQType) : Type :=
     (forall Var, PBasis Var p₁ <~> PBasis Var p₂).

  Instance PEquiv_refl : Reflexive PEquiv. 
    intros p Var. apply reflexive_equiv.
  Defined.
  Instance PEquiv_sym : Symmetric PEquiv.
    intros p₁ p₂ eq Var. apply symmetric_equiv.
    apply eq.
  Defined.
  Instance PEquiv_trans : Transitive PEquiv.
    intros p1 p2 p3 eq1 eq2 Var. eapply transitive_equiv.
    + apply eq1.
    + apply eq2.
  Defined.
  Instance PEquiv_HSet : forall p₁ p₂, IsHSet (PEquiv p₁ p₂).
  Proof.
    intros p1 p2. 
    unfold PEquiv.
    apply @trunc_forall; [exact _ | ].
    intros Var.
    apply @istrunc_equiv; [exact _ | ].
    (* Is PBasis Var p2 an HSet? *)
    (* might rely on the fact that Var is an HSet, which we don't currently have
    but could add. *)
  Admitted.

  Require Import Groupoid.
  Axiom G_PEquiv : groupoid PQType PEquiv.
  
  Definition Partial := quotient1 G_PEquiv.

  Lemma fromPartial_cell : forall p1 p2, PEquiv p1 p2 ->
    from_PQType p1 = from_PQType p2.
  Admitted. (* true *)
    
  Lemma fromPartial_compose : forall (x y z : PQType) (f : PEquiv x y) (g : PEquiv y z),
  fromPartial_cell x z (g o f)%groupoid =
  fromPartial_cell x y f @ fromPartial_cell y z g.
  Admitted.

  Definition fromPartial : Partial -> QType.
  Proof.
    apply quotient1_rec with (C_point := from_PQType)
                             (C_cell := fromPartial_cell).
    * apply fromPartial_compose.
    * exact _.
  Defined.

  Lemma PBasis_cell : forall Var (x y : PQType),
      PEquiv x y -> PBasis Var x = PBasis Var y.
  Admitted.

  Definition PBasis' (Var : QType -> Type) : Partial -> Type.
    apply quotient1_rec with (C_point := PBasis Var)
                             (C_cell := PBasis_cell Var).
  Admitted (* should be fine if we're careful about result types *).
  Lemma PBasis'_point : forall Var (p : PQType),
    PBasis' Var (point _ p) = PBasis Var p.
  Admitted.
  
  Definition pinit' : forall (p : Partial), PBasis' Exp p -> Exp (fromPartial p).
  Proof.
    set (P := fun p => PBasis' Exp p -> Exp (fromPartial p)).
    change (forall p, P p).

    assert (pinit0 : forall (p : PQType), P (point _ p)).
    { intros p0.
      unfold P.
      unfold fromPartial. simpl.
      rewrite PBasis'_point.
      apply pinit.
    }

    assert (pinit0_cell : forall (p1 p2 : PQType) (eq : PEquiv p1 p2),
        transport P (cell _ eq) (pinit0 p1) = pinit0 p2).
    { unfold PEquiv. intros p1 p2 eq. admit.
      (* maybe by case analysis on p1 and p2?? *)
    }

    apply quotient1_ind with (P_point := pinit0)
                             (P_cell := pinit0_cell).
  Abort.


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

*)
End Syntax.