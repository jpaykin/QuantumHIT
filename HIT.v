Require Import HoTT.
Require Import MyNotations.
Require Import Monad.

Check transport.
(* forall (P : A -> Type) (x y : A), x = y -> P x -> P y *)
Check ap.
(* forall f : A -> B) (x y : A), x = y -> f x = f y *)
Check apD.
(* ∀ (f : ∀ (a:A), B a) (x y : A) (p : x = y), transport p (f x) = f y *)
About inverse.
(* Use notation p^ *)


Section QType.

(* Define a HIT on quantum types *)
Private Inductive QType := 
| Qubit 
(*| Tensor (Q1 : QType) (Q2 : QType)*)
| Lolli (Q1 Q2 : QType)
(*| H : Qubit = Qubit
| H_dag : H^ = H.*)
.
(*Notation "Q1 ⊗ Q2" := (Tensor Q1 Q2) (at level 20).*)
Notation "Q1 ⊸ Q2" := (Lolli Q1 Q2) (at level 20).
Axiom H : Qubit = Qubit.
Axiom H_dag : H^ = H. 

Variable P : QType -> Type.
Variable P_Qubit : P Qubit. 
Variable P_Lolli : forall Q1, P Q1 -> forall Q2, P Q2 -> P (Q1 ⊸ Q2).
Variable P_H : transport P H P_Qubit = P_Qubit. 

Definition P_H' : transport P H^ P_Qubit = P_Qubit :=
  moveR_transport_V _ _ _ _ P_H^.
Variable P_H_dag : P_H' = transport2 _ H_dag P_Qubit @ P_H.



Fixpoint QType_rect (Q : QType) : P Q := 
  (match Q with
  | Qubit => fun _ _ => P_Qubit
  | Lolli Q1 Q2 => fun _ _ => P_Lolli _ (QType_rect Q1) _ (QType_rect Q2)
  end) P_H P_H_dag.
Axiom QType_rect_H : apD QType_rect H = P_H.

(* bleh, this is super dense *)
Definition R :=  fun p => moveR_transport_V P H P_Qubit P_Qubit p^
                          = transport2 P H_dag P_Qubit @ p.
Definition P_H_dag' : apD QType_rect H^ 
                    = transport2 P H_dag (QType_rect Qubit) @ apD QType_rect H :=
  apD_V _ _ @ transport R QType_rect_H^ P_H_dag.
Axiom QType_rect_H_dag : apD02 QType_rect H_dag = P_H_dag'.



End QType.
Check QType_rect.

(* Recursion *)
Section QType_rec.

Lemma moveR_transport_V_const : ∀ (A : Type) (C : Type) (x y : A) (p : y = x)
                                  (u v : C) (r : u = transport (λ _· C) p v),
                                           (*( r : u = v ),*)
                                  moveR_transport_V (λ _· C) p u v r 
                                = transport_const _ _ @ r @ transport_const _ _.
Proof.
  destruct p. intros.
  exact ((concat_1p _)^ @ (concat_p1 _)^).
Defined.

Variable C : Type.
Variable C_Qubit : C.
Variable C_Lolli : C -> C -> C.
Variable C_H : C_Qubit = C_Qubit.
Variable C_H_dag : C_H^ = C_H.

Definition QType_rec (Q : QType) : C.
(*  QType_rect _ C_Qubit (λ _ C1 _ C2 · C_Lolli C1 C2) C_H _ Q.*)
Proof. 
  set (P_Lolli := λ (_ : QType) C1 (_ : QType) C2 · C_Lolli C1 C2).
  set (P_H := (transport_const _ _ @ C_H) : transport (λ _· C) H C_Qubit = C_Qubit).  assert (P_H_dag : P_H' (λ _· C) C_Qubit P_H 
                  = transport2 (λ _· C) H_dag C_Qubit @ P_H).
  { unfold P_H'. 
    About transport2_const.
    transitivity ( transport2 (λ _· C) H_dag C_Qubit 
                 @ (transport_const H C_Qubit @ (transport_const H C_Qubit)^)
                 @ P_H); [ | rewrite concat_pV, concat_p1; reflexivity].
    repeat rewrite concat_p_pp.
    rewrite <- transport2_const.
    rewrite moveR_transport_V_const.
    repeat rewrite <- concat_p_pp.
    f_ap.
    unfold P_H.
    rewrite inv_pp.
    repeat rewrite <- concat_p_pp.
    rewrite concat_Vp, concat_p1.
    repeat rewrite concat_p_pp.
    rewrite concat_Vp, concat_1p.
    exact C_H_dag.
  }
  exact (QType_rect _ C_Qubit P_Lolli P_H P_H_dag Q).
Defined.

(* TODO: computation rules for QType_rec *)
Lemma QType_rec_Qubit : QType_rec Qubit = C_Qubit.
Proof.
  reflexivity.
Defined.
Lemma QType_rec_H : ap QType_rec H = C_H.
Admitted.

(* Used in the type of QType_rec_H_dag *)
Lemma QType_rec_H' : ap QType_rec H^ = C_H^.
Proof.
  exact ((inverse_ap _ _)^ @ ap _ QType_rec_H).
Defined.

Lemma QType_rec_H_dag : ap02 QType_rec H_dag 
                      = QType_rec_H' @ C_H_dag @ QType_rec_H^.
Admitted.
End QType_rec.
Arguments QType_rec C C_Qubit C_Lolli C_H C_H_dag Q : assert.

(* We can define a recursion principle that collapses all unitaries,
   sending them all to 1. *)
Definition QType_rec_triv (C : Type) (C_Q : C) (C_Lolli : C -> C -> C) 
                          : QType -> C :=
  QType_rec C C_Q C_Lolli 1 1.


Definition toClassical (Q : QType) : Type :=
  QType_rec_triv _ Bool (λ τ1 τ2 · τ1 -> τ2) Q.

Definition QType_size : QType -> nat := QType_rec_triv nat 1 (λ n1 n2· n1+n2)%nat.

Require Import Peano.
Open Scope nat.

Lemma lt_trans : forall (m n p : nat), m < n -> n < p -> (m < p)%nat.
Admitted.
(*
Proof.
  unfold lt.
  intros m n p H1 H2.
  apply (leq_transd H1).
  assert (le_1 : forall (x:nat), x <= x.+1).
  { induction x. constructor.
    Print Peano.le.
    apply le_S.
  }
  eapply (leq_transd _ H2).
  -
Admitted.
*)
Lemma lt_plus : forall m n p q, m < p -> n < q -> m + n < p + q.
Admitted.
Lemma lt_plus_r : forall m n, 0 < m -> n < m + n.
Admitted.


Print le. Print leq. Print DHProp. About hProp. Locate "_ -Type".
Print TruncType. Print IsTrunc. Print IsTrunc_internal.

(* This is just unfolding the definition of "m < n" *)
Lemma lt_neg1 : forall m n, IsTrunc -1 (m < n).
Proof. 
  intros.
  destruct (m < n). simpl in *. destruct dhprop_hprop.
  auto.
Defined.
(* It says that forall (pf1 pf2 : m < n), ∃! (pf2 : pf1 = pf2) *)

Lemma lt_eq : forall {m n} (pf1 pf2 : m < n), pf1 = pf2.
Proof.
  intros.
  destruct (m < n); simpl in *.
  destruct dhprop_hprop; simpl in *.
  destruct istrunc_trunctype_type with (x := pf1) (y := pf2).
  exact center.
Defined.


(* Depends on lt_contr *)
Lemma QType_size_pos : forall Q, 0 < QType_size Q.
Proof. 
  assert (P_Qubit : 0 < 1) by constructor.
  apply QType_rect with (P_Qubit := P_Qubit).
  - intros Q1 H1 Q2 H2. simpl.
    apply lt_trans with (QType_size Q2); auto.
    apply lt_plus_r; auto.
  - apply lt_eq.
Qed.


  


Inductive Exp (Γ : Set) : Set :=
| Var : Γ -> Exp Γ
| App : Exp Γ -> Exp Γ -> Exp Γ
| Abs : Exp (option Γ) -> Exp Γ
.
Arguments Var [Γ].
Arguments App [Γ].
Arguments Abs [Γ].

Fixpoint exp_fmap {A B : Set} (f : A -> B) (e : Exp A) : Exp B :=
  match e with
  | Var x => Var (f x)
  | App e1 e2 => App (exp_fmap f e1) (exp_fmap f e2)
  | Abs e' => Abs (exp_fmap (fmap f) e')
  end.
Instance expF : Functor Exp := {fmap := @exp_fmap}.


Definition exp_shift {A} (e : Exp A) : Exp (option A) := fmap (@Some A) e.
Definition exp_option_liftT {A B : Set} (f : A -> Exp B) (x : option A) 
                            : Exp (option B) :=
  match x with
  | None => Var None
  | Some y => exp_shift (f y)
  end.

Fixpoint exp_bind {A : Set} (e : Exp A) : forall {B : Set}, (A -> Exp B) -> Exp B :=
  match e with
  | Var x => fun B f => f x
  | App e1 e2 => fun B f => App (exp_bind e1 f) (exp_bind e2 f)
  | Abs e' => fun B f => Abs (exp_bind e' (exp_option_liftT f))
  end.

(* may not be the most efficient *)
Fixpoint exp_liftA {A B : Set} (f : Exp (A -> B)) (e : Exp A) : Exp B :=
  exp_bind f (fun f' => fmap f' e). 

Instance expA : Applicative Exp := {pure := Var;
                                    liftA := @exp_liftA}.
Instance expM : Monad Exp := {bind := @exp_bind}.

Definition subst_var {Γ} (e : Exp Γ) (x : option Γ) : Exp Γ :=
  match x with
  | None => e
  | Some y => Var y
  end.

(* Substitute e for the variable 0=None in e' *)
Definition subst {Γ} (e : Exp Γ) (e' : Exp (option Γ)) : Exp Γ :=
  do x ← e'; subst_var e x.

Fixpoint step1 {Γ} (e : Exp Γ) : option (Exp Γ) :=
  match e with
  | Var x => None
  | Abs e' => None
  | App (Abs e1) e2 => Some (subst e2 e1)
  | App e1 e2 => do e1' ← step1 e1; 
                 return_ (App e1' e2)
  end.


(* Linear typing judgment *)
Definition Ctx (X : Set) := X -> option QType.
Definition Merge {X : Set} (Γ1 Γ2 Γ : Ctx X) := forall x W,
  (Γ x = Some W) <-> ((Γ1 x = Some W /\ Γ2 x = None) \/ (Γ1 x = None /\ Γ2 x = Some W)).
Definition extend {X : Set} (Γ : Ctx X) (W : QType) : Ctx (option X) :=
  λ z· match z with
       | None => Some W
       | Some x => Γ x
       end.


Inductive LExp : forall {X : Set}, Ctx X -> Exp X -> QType -> Type :=
| LVar : forall {X} (Γ : Ctx X) (x : X) (Q : QType), 
         Γ x = Some Q -> LExp Γ (Var x) Q
| LApp : forall {X} (Γ1 Γ2 Γ : Ctx X) (Q1 Q2 : QType) e1 e2,
         Merge Γ1 Γ2 Γ ->
         LExp Γ1 e1 (Q1 ⊸ Q2) ->
         LExp Γ2 e2 Q1 ->
         LExp Γ (App e1 e2) Q2
| LAbs : forall {X} (Γ : Ctx X) Q1 Q2 e',
         LExp (extend Γ Q1) e' Q2 ->
         LExp Γ (Abs e') (Q1 ⊸ Q2)
.
Inductive QExp {X} (Γ : Ctx X) Q :=
| qexp : forall (e : Exp X), LExp Γ e Q -> QExp Γ Q.


Definition unitary {X} {Q1 Q2} (U : Q1 = Q2) {Γ : Ctx X} (e : QExp Γ Q1) : QExp Γ Q2 :=
  transport _ U e.

Definition Unitary (Q : QType) := Q = Q.

Lemma U_compose : forall (Q1 Q2 Q3 : QType) (U1 : Q1 = Q2) (U2 : Q2 = Q3)
                  {X} (Γ : Ctx X) (e : QExp Γ Q1),
      unitary U2 (unitary U1 e) = unitary (U1 @ U2) e.
Proof.
  destruct U1. intros. simpl. Search (1 @ _ = _). rewrite concat_1p. reflexivity.
Qed.

Lemma U_U_transpose : forall (Q : QType) (U : Unitary Q) {X} (Γ : Ctx X) (e : QExp Γ Q),
      unitary (U^) (unitary U e) = e.
Proof. 
  intros. rewrite U_compose. Search (?p @ ?p^). rewrite concat_pV. reflexivity.
Qed.

Lemma H_H_inverse : forall {X} (Γ : Ctx X) (e : QExp Γ Qubit), unitary H (unitary H e) = e.
Proof.
  intros. 
  apply (@concat _ _ (unitary H^ (unitary H e))).
  - rewrite H_dag; auto.
  - apply U_U_transpose.
Qed.

Definition QType_size (Q : QType) : nat.
Proof.
  apply 