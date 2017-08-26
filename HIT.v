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
  apD_V QType_rect H @ transport R QType_rect_H^ P_H_dag. 
Axiom QType_rect_H_dag : apD02 QType_rect H_dag = P_H_dag'.


End QType.
Check QType_rect_H.
(*Notation "Q1 ⊗ Q2" := (Tensor Q1 Q2) (at level 20).*)
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
Variable C_Lolli : C -> C -> C.
Variable C_H : C_Qubit = C_Qubit.
Variable C_H_dag : C_H^ = C_H.


Definition P := fun (_ : QType) => C.
Definition P_Qubit := C_Qubit.
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
  exact (QType_rect P C_Qubit P_Lolli P_H P_H_dag).
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
  refine (1 @@ QType_rect_H _ _ _ _ _ @ _). 
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
  refine (QType_rect_H P P_Qubit P_Lolli P_H P_H_dag)^.
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
  exact (QType_rect_H_dag P P_Qubit P_Lolli P_H P_H_dag).
Defined.

End QType_rec.
Arguments QType_rec C C_Qubit C_Lolli C_H C_H_dag Q : assert.

(* We can define a recursion principle that collapses all unitaries,
   sending them all to 1. *)
Definition QType_rec_triv (C : Type) (C_Q : C) (C_Lolli : C -> C -> C) 
                          : QType -> C :=
  QType_rec C C_Q C_Lolli 1 1.


Definition toClassical (Q : QType) : Type :=
  QType_rec_triv _ Bool (fun τ1 τ2 => τ1 -> τ2) Q.
Definition QType_size : QType -> nat := QType_rec_triv nat 1%nat (fun n1 n2 => n1+n2)%nat.

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
  assert (P_Lolli : forall Q1 (H1 : P Q1) Q2 (H2 : P Q2), P (Lolli Q1 Q2)).
  { 
    unfold P; intros; simpl.
    apply lt_plus_r. auto.
  } 
  assert (P_H : transport P H P_Qubit = P_Qubit) by apply path_ishprop.
  assert (P_H_dag : P_H' P P_Qubit P_H = transport2 P H_dag P_Qubit @ P_H) 
    by apply path_ishprop.
  apply (QType_rect P P_Qubit P_Lolli P_H P_H_dag).
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
  assert (P_Lolli : forall Q1, P Q1 -> forall Q2, P Q2 -> P (Q1 ⊸ Q2)). admit.
  assert (P_H : transport P H P_Qubit = P_Qubit). admit.
  assert (P_H_dag : P_H' P P_Qubit P_H = transport2 P H_dag P_Qubit @ P_H). admit.
  apply (QType_rect P P_Qubit P_Lolli P_H P_H_dag). 
Admitted.


(*
(************)
(** Syntax **)
(************)

Section Syntax.


Set Implicit Arguments.

Inductive Exp X :=
| Var : X -> Exp X
| App : Exp X -> Exp X -> Exp X
| Abs : Exp (option X) -> Exp X.


Inductive Exp' X : QType -> Type :=
| Var' : forall Q, X -> Exp' X Q
| App' : forall Q R, Exp' X (Q ⊸ R) -> Exp' X Q -> Exp' X R
| Abs' : forall Q R, Exp' (option X) R -> Exp' X (Q ⊸ R).

(*
Inductive LExp : forall {X} `{DecidablePaths X}, Ctx X QType -> QType -> Type :=
| LVar : forall {X} `{DecidablePaths X} {Γ : Ctx X QType} (x : X) {Q : QType},
         Γ = singleton x Q -> 
         LExp Γ Q 
| LApp : forall {X} `{DecidablePaths X} {Γ1 Γ2 Γ : Ctx X QType} {Q1 Q2 : QType},
         Γ = Γ1 · Γ2 ->
         LExp Γ1 (Q1 ⊸ Q2) ->
         LExp Γ2 Q1 ->
         LExp Γ Q2
| LAbs : forall {X} `{DecidablePaths X} {Γ : Ctx X QType} {Q1 Q2},
         LExp (extend Γ Q1) Q2 ->
         LExp Γ (Q1 ⊸ Q2)
.
*)

Definition exp_fmap {X Y : Type} (f : X -> Y) (e : Exp X) : Exp Y.
Proof.
  generalize dependent Y.
  induction e; intros Y f.
  - exact (Var (f x)).
  - exact (App (IHe1 Y f) (IHe2 Y f)).
  - exact (Abs (IHe (option Y) (fmap f))).
Defined.
Instance expF : Functor Exp := {fmap := @exp_fmap}.



Definition shift {A} (e : Exp A) : Exp (option A) := fmap (@Some A) e.
Definition exp_option_liftT {A B : Set} (f : A -> Exp B) (x : option A) 
                            : Exp (option B) :=
  match x with
  | None => Var None
  | Some y => shift (f y)
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

(* Shouldn't need congruence rules if we extend this to an equivalence relation *)
Inductive eq1 {X} : Exp X -> Exp X -> Type :=
| App_η : forall (e : Exp X), eq1 e (Abs (App (shift e) (Var None)))
| App_β : forall e1 e2, eq1 (App (Abs e1) e2) (subst e2 e1)
.

Inductive Val : Type :=
| VAbs : Exp (option Empty) -> Val.

Definition QCtx X := Ctx X QType.

Inductive WF_Exp : forall {X : Type} `{DecidablePaths X}, QCtx X -> Exp X -> QType -> Type :=
| WF_Var : forall {X : Type} `{DecidablePaths X} (Γ : QCtx X) (x : X) (Q : QType),
           Γ = singleton x Q -> WF_Exp Γ (Var x) Q
| WF_App : forall {X : Type} `{DecidablePaths X} (Γ1 Γ2 Γ : QCtx X) (Q R : QType) (e1 e2 : Exp X),
           Γ = Γ1 · Γ2 -> 
           WF_Exp Γ1 e1 (Q ⊸ R) ->
           WF_Exp Γ2 e2 Q ->
           WF_Exp Γ  (App e1 e2) R
| WF_Abs : forall {X : Type} `{DecidablePaths X} (Γ : QCtx X) Q R (e' : Exp (option X)),
           WF_Exp (extend Γ Q) e' R ->
           WF_Exp Γ (Abs e') (Q ⊸ R)
.

Inductive LExp : forall {X : Type}, QCtx X -> QType -> Type :=
| LVar : forall {X : Type} (Γ : QCtx X) (x : X) (Q : QType),
         Γ = singleton x Q -> LExp Γ Q
| LApp : forall {X : Type} `{DecidablePaths X} (Γ1 Γ2 Γ : QCtx X) (Q R : QType),
         Γ = Γ1 · Γ2 -> Γ <> None ->
         LExp Γ1 (Q ⊸ R) ->
         LExp Γ2 Q ->
         LExp Γ R
| LAbs : forall {X : Type} (Γ : QCtx X) Q R,
         LExp (extend Γ Q) R ->
         LExp Γ (Q ⊸ R)
.
Arguments LVar {X} {Γ} x {Q} : rename.
Arguments LApp {X} {decX} {Γ1 Γ2 Γ} {Q R} : rename.
Arguments LAbs {X} {Γ} {Q R} e : rename.


Definition lexp_fmap' {X Y : Type} `{DecidablePaths X} `{DecidablePaths Y}
                              (f : X -> Y) (Γ : Ctx X QType)
                              (Q: QType)
                              (e : LExp Γ Q) : LExp (fmap f Γ) Q.
  generalize dependent Y.
  induction e as [X Γ x Q pf1 | |]; intros Y HY f.
  - refine (LVar (f x) _). rewrite pf1. apply fmap_singleton; auto.
  - refine (LApp _ _ (IHe1 _ _ _ f) (IHe2 _ _ _ f)).
    * rewrite p. apply fmap_merge.
    * intros H.
      apply n.
      apply (fmap_None_inv _ _ _ _ H).
  - set (e' := IHe _ (option Y) _ (fmap f)).
    rewrite fmap_extend in e'; auto.
    refine (LAbs e').
Defined.

Definition EExp X Q := exists (Γ : QCtx X), LExp Γ Q.

Definition eVar {X} (x : X) (Q : QType) : EExp X Q.
  exists (singleton x Q). 
  exact (LVar x idpath).
Defined. 

About QType_rec.

Instance decQCtx {X} `{DecidablePaths X} : DecidablePaths (QCtx X).
Admitted.

Definition eApp {X} `{DecidablePaths X} Q R (e1 : EExp X (Q ⊸ R)) (e2 : EExp X Q) 
           : option (EExp X R).
Proof.
  destruct e1 as [Γ1 e1].
  destruct e2 as [Γ2 e2].
  destruct (dec_paths (Γ1 · Γ2) None) as [H | H].
  - exact None.
  - apply Some. exists (Γ1 · Γ2). exact (LApp idpath H e1 e2).
Defined.

(* goes in SetCtx.v *)
Definition lookup {X} (Γ : QCtx X) (x : X) : option QType.
Admitted.
Definition tail {X} (Γ : QCtx (option X)) : QCtx X.
Admitted.
Lemma extend_tail : forall {X} (Γ : QCtx (option X)) Q,
      lookup Γ None = Some Q -> extend (tail Γ) Q = Γ.
Admitted.


Definition eAbs {X} Q R (e' : EExp (option X) R) : option (EExp X (Q ⊸ R)).
Proof.
  destruct e' as [Γ e'].
  destruct (dec_paths (lookup Γ None) (Some Q)).
  - (* lookup Γ None = Some Q *)
    apply Some. exists (tail Γ). apply LAbs. rewrite (extend_tail p). exact e'.
  - exact None.
Defined.



Definition EExp_fmap {Q} {X Y : Type} `{DecidablePaths X} `{DecidablePaths Y}
                     (f : X -> Y) (e : EExp X Q) : EExp Y Q.
Proof.
  destruct e as [Γ e].
  exists (fmap f Γ). exact (lexp_fmap' f e).
Defined.
(* Can't give this a functor instance per se because it depends on the fact that X and Y are decidable. *)

Definition eshift {Q} {X} `{DecidablePaths X} (e : EExp X Q) : EExp (option X) Q := 
    EExp_fmap (@Some X) e.

Definition EExp_liftT {Q} {X Y : Type} `{DecidablePaths X} `{DecidablePaths Y} (f : X -> EExp Y Q)
                      (x : option X) : EExp (option Y) Q :=
  match x with
  | None => eVar None Q
  | Some x => eshift (f x)
  end.

Definition EExp_bind' {X : Type} {Q} (e : EExp X Q) : forall {Y : Type} {R}, 
                      (X -> EExp Y R) -> EExp Y R.
Proof.
  destruct e as [Γ e].
  induction e; intros Y R f.
  - exact (f x).
  - admit.
  - admit.
Admitted.

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

End Syntax.
*)