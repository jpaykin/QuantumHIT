Require Import HoTT.
Add LoadPath "./LinearTypingContexts/" as LinearTypingContexts.
Require Import LinearTypingContexts.Monad.
Require Import LinearTypingContexts.NCM.
Require Import LinearTypingContexts.Permutation.
Require Import LinearTypingContexts.SetContext.

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
| Tensor (Q1 : QType) (Q2 : QType)
| Lolli (Q1 Q2 : QType)
| Lower : forall (τ : Type) `{DecidablePaths τ}, QType
(*| H : Qubit = Qubit
| H_dag : H^ = H.*)
.
Notation "Q1 ⊗ Q2" := (Tensor Q1 Q2) (at level 20).
Notation "Q1 ⊸ Q2" := (Lolli Q1 Q2) (at level 20).

Axiom H : Qubit = Qubit.
Axiom H_dag : H^ = H. 

Variable P : QType -> Type.
Variable P_Qubit : P Qubit. 
Variable P_Tensor : forall Q1, P Q1 -> forall Q2, P Q2 -> P (Q1 ⊗ Q2).
Variable P_Lolli : forall Q1, P Q1 -> forall Q2, P Q2 -> P (Q1 ⊸ Q2).
Variable P_Lower : forall (τ : Type) `{DecidablePaths τ}, P (Lower τ).
Variable P_H : transport P H P_Qubit = P_Qubit. 

Definition P_H' : transport P H^ P_Qubit = P_Qubit :=
  moveR_transport_V _ _ _ _ P_H^.
Variable P_H_dag : P_H' = transport2 _ H_dag P_Qubit @ P_H.


Fixpoint QType_rect (Q : QType) : P Q := 
  (match Q with
  | Qubit => fun _ _ => P_Qubit
  | Tensor Q1 Q2 => fun _ _ => P_Tensor _ (QType_rect Q1) _ (QType_rect Q2)
  | Lolli Q1 Q2 => fun _ _ => P_Lolli _ (QType_rect Q1) _ (QType_rect Q2)
  | Lower τ _ => fun _ _ => P_Lower τ _
  end) P_H P_H_dag.
Axiom QType_rect_H : apD QType_rect H = P_H.

(* bleh, this is super dense *)
Definition R :=  fun p => moveR_transport_V P H P_Qubit P_Qubit p^
                          = transport2 P H_dag P_Qubit @ p.

Definition P_H_dag' : apD QType_rect H^ 
                    = transport2 P H_dag (QType_rect Qubit) @ apD QType_rect H :=
  apD_V QType_rect H @ transport R QType_rect_H^ P_H_dag. 
Axiom QType_rect_H_dag : apD02 QType_rect H_dag = P_H_dag'.


End QType.
Check QType_rect_H.
Notation "Q1 ⊗ Q2" := (Tensor Q1 Q2) (at level 20).
Notation "Q1 ⊸ Q2" := (Lolli Q1 Q2) (at level 20).


(* Recursion *)
Section QType_rec.

Lemma moveR_transport_V_const : forall (A : Type) (C : Type) (x y : A) (p : y = x)
                                  (u v : C) (r : u = transport (fun _ => C) p v),
                                           (*( r : u = v ),*)
                                  moveR_transport_V (fun _ => C) p u v r 
                                = transport_const _ _ @ r @ transport_const _ _.
Proof.
  destruct p. intros.
  exact ((concat_1p _)^ @ (concat_p1 _)^).
Defined.

Variable C : Type.
Variable C_Qubit : C.
Variable C_Tensor : C -> C -> C.
Variable C_Lolli : C -> C -> C.
Variable C_Lower : Type -> C.

Variable C_H : C_Qubit = C_Qubit.
Variable C_H_dag : C_H^ = C_H.


Definition P := fun (_ : QType) => C.
Definition P_Qubit := C_Qubit.
Definition P_Tensor := fun (_ : QType) x (_ : QType) y => C_Tensor x y.
Definition P_Lolli := fun (_ : QType) x (_ : QType) y => C_Lolli x y.

Definition P_H : transport (fun _ => C) H C_Qubit = C_Qubit :=
    transport_const _ _ @ C_H.
Definition P_H_dag : P_H' (fun _ => C) C_Qubit P_H 
                  = transport2 (fun _=> C) H_dag C_Qubit @ P_H.
Proof.
    unfold P_H', P_H.
    refine (moveR_transport_V_const _ _ _ _ _ _ _ _ @ _).
    refine (_ @ (concat_p_pp _ _ _)^).
    rewrite (transport2_const H_dag C_Qubit)^. 
    refine ((concat_p_pp _ _ _)^ @ _).
    refine (idpath @@ _).
    refine (inv_pp _ _ @@ idpath @ _).
    refine ((concat_p_pp _ _ _)^ @ _).
    refine (idpath @@ concat_Vp _ @ _).
    refine (concat_p1 _ @ _).
    exact C_H_dag.
Defined.



Definition QType_rec : QType -> C.
(*  QType_rect _ C_Qubit (fun _ C1 _ C2 => C_Lolli C1 C2) C_H _ Q.*)
Proof. 
  exact (QType_rect P C_Qubit P_Tensor P_Lolli (fun τ _ => C_Lower τ) P_H P_H_dag).
Defined.

(* TODO: computation rules for QType_rec *)
Lemma QType_rec_Qubit : QType_rec Qubit = C_Qubit.
Proof.
  reflexivity.
Defined.

Lemma apD_const' : forall {A B} {x y : A} (f : A -> B) (p : x = y),
      ap f p = (transport_const p (f x))^ @ apD f p.
Proof.
  intros. 
  refine (_ @ (1 @@ (apD_const _ _)^ )). 
  refine (_ @ (concat_p_pp _ _ _)^).
  refine (_ @ ((concat_Vp _)^ @@ 1)).
  refine (concat_1p _)^.
Defined.

Lemma QType_rec_H : ap QType_rec H = C_H.
Proof. 
  unfold QType_rec.
  refine (apD_const' _ _ @ _); simpl.
  refine (1 @@ QType_rect_H _ _ _ _ _ _ _ @ _). 
  refine (concat_p_pp _ _ _ @ _).
  refine (concat_Vp _ @@ 1 @ _).
  refine (concat_1p _).
Defined.

(* Used in the type of QType_rec_H_dag *)
Lemma QType_rec_H' : ap QType_rec H^ = C_H^.
Proof. About inverse_ap.
  exact ((inverse_ap QType_rec H)^ @ ap inverse QType_rec_H).
Defined. 

About QType_rect_H_dag. Print P_H_dag'.


Print P_H_dag'.
Definition C_H_dag' : apD QType_rec H^ 
                    = transport2 P H_dag P_Qubit @ apD QType_rec H.
Proof.
  refine (apD_V _ _ @ _). 
  refine (transport (R P P_Qubit) _ P_H_dag).
  refine (QType_rect_H P P_Qubit P_Tensor P_Lolli (fun τ _ => C_Lower τ) P_H P_H_dag)^.
(*refine (apD_const _ _ @ _). 
  refine (1 @@ (QType_rec_H' @ C_H_dag) @ _).
  refine (_ @ (1 @@ (apD_const _ _)^)).
  refine (_ @ (1 @@ (1 @@ QType_rec_H^))).
  refine (_ @ (concat_p_pp _ _ _)^).
  refine (_ @@ 1).
  refine (transport2_const _ _). *)
Defined.


Lemma QType_rec_H_dag : apD02 QType_rec H_dag = C_H_dag'.
Proof.
  exact (QType_rect_H_dag P P_Qubit P_Tensor P_Lolli (fun τ _ => C_Lower τ) P_H P_H_dag).
Defined.

End QType_rec.
Arguments QType_rec C C_Qubit C_Tensor C_Lolli C_Lower C_H C_H_dag Q : assert.

(* We can define a recursion principle that collapses all unitaries,
   sending them all to 1. *)
Definition QType_rec_triv (C : Type) (C_Q : C) 
          (C_Tensor : C -> C -> C) (C_Lolli : C -> C -> C) (C_Lower : Type -> C)
                          : QType -> C :=
  QType_rec C C_Q C_Tensor C_Lolli C_Lower 1 1.


Definition toClassical (Q : QType) : Type :=
  QType_rec_triv _ Bool (fun τ1 τ2 => τ1 * τ2) 
                        (fun τ1 τ2 => τ1 -> τ2) 
                        (fun τ => τ) Q.
Definition QType_size : QType -> nat := 
    QType_rec_triv nat 1%nat (fun n1 n2 => n1+n2)%nat (fun n1 n2 => n1+n2)%nat 
      (fun _ => 1%nat).

Require Import Peano.
Open Scope nat.


Lemma lt_plus_r : forall m n, (0 < m -> 0 < m + n)%nat.
Proof.
  destruct m; intros; auto.
  contradiction.
Defined.


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

(* subsumed by library path_ishprop *)
Lemma lt_eq : forall {m n} (pf1 pf2 : m < n), pf1 = pf2.
Proof.
  intros. apply path_ishprop.
(*  intros.
  destruct (m < n); simpl in *.
  destruct dhprop_hprop; simpl in *.
  destruct istrunc_trunctype_type with (x := pf1) (y := pf2).
  exact center.*)
Defined.


(* Depends on lt_contr *)
Lemma QType_size_pos : forall Q, 0 < QType_size Q.
Proof. 
  set (P Q := 0 < QType_size Q).
  assert (P_Qubit : 0 < 1) by constructor. 
  assert (P_Tensor : forall Q1 (H1 : P Q1) Q2 (H2 : P Q2), P (Tensor Q1 Q2)).
  { 
    unfold P; intros; simpl.
    apply lt_plus_r. auto.
  } 
  assert (P_Lolli : forall Q1 (H1 : P Q1) Q2 (H2 : P Q2), P (Lolli Q1 Q2)).
  { 
    unfold P; intros; simpl.
    apply lt_plus_r. auto.
  } 
  assert (P_Lower : forall τ `{DecidablePaths τ}, P (Lower τ)).
  { 
    unfold P; intros; simpl. auto.
  }
  assert (P_H : transport P H P_Qubit = P_Qubit) by apply path_ishprop.
  assert (P_H_dag : P_H' P P_Qubit P_H = transport2 P H_dag P_Qubit @ P_H) 
    by apply path_ishprop.
  apply (QType_rect P P_Qubit P_Tensor P_Lolli P_Lower P_H P_H_dag).
Qed.

(* Decidability *)

Lemma option_Some_Some_inv : forall {A} (x y : A), Some x = Some y -> x = y.
Proof.
  intros A x y pf.
  set (P := fun (o' : option A) => match o' with
                                  | Some z => x = z
                                  | None => Empty
                                  end).
  exact (transport P pf idpath).
Defined.

Lemma option_Some_None_inv : forall {A} (x : A), Some x <> None.
Proof.
  intros A x H.
  set (P := fun (a : option A) => match a with
                                  | Some _ => Unit
                                  | None => Empty
                                  end).
  exact (transport P H tt).
Defined.


Instance decidable_unit : DecidablePaths Unit.
Proof.
  intros [] [].
  left. exact idpath.
Defined.

Instance decidable_option {A} `{DecidablePaths A} : DecidablePaths (option A).
Proof.
  intros [x | ] [y | ].
  - destruct (H0 x y). 
    * left. f_ap.
    * right. intros H. apply n. apply option_Some_Some_inv; auto.
  - right. apply option_Some_None_inv.
  - right. intros H. apply (@option_Some_None_inv A y). exact H^.
  - left. exact idpath.
Defined.

Instance decQType : DecidablePaths QType.
Proof.
  unfold DecidablePaths. 
  set (P := fun (Q : QType) => forall R, Decidable (Q = R)).
  change (forall (Q : QType), P Q).
  assert (P_Qubit : P Qubit). admit.
  assert (P_Tensor : forall Q1, P Q1 -> forall Q2, P Q2 -> P (Q1 ⊗ Q2)). admit.
  assert (P_Lolli : forall Q1, P Q1 -> forall Q2, P Q2 -> P (Q1 ⊸ Q2)). admit.
  assert (P_Lower : forall (τ : Type) `{DecidablePaths τ}, P (Lower τ)).
  { intros τ decτ.
    unfold P.
    admit.
  }
  assert (P_H : transport P H P_Qubit = P_Qubit). admit.
  assert (P_H_dag : P_H' P P_Qubit P_H = transport2 P H_dag P_Qubit @ P_H). admit.
  apply (QType_rect P P_Qubit P_Tensor P_Lolli P_Lower P_H P_H_dag). 
Admitted.



