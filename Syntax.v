Require Import HoTT.
Add LoadPath "./LinearTypingContexts/" as LinearTypingContexts.
Require LinearTypingContexts.Monad.
Require Import LinearTypingContexts.Monad.
Require Import LinearTypingContexts.NCM.
Require Import LinearTypingContexts.Permutation.
Require Import LinearTypingContexts.SetContext.
Require Import HIT.

Section Syntax.
Set Implicit Arguments.

Inductive Extend {A} (a : A) (X : Type) : Type :=
| hd : Extend a X
| tl : X -> Extend a X.
Arguments hd {A} {a} {X}.
Arguments tl {A} {a} {X}.

Definition extend {X A : Type} (Γ : Ctx X A) (a : A) : Ctx (Extend a X) A :=
  fmap_Ctx tl Γ.


Definition extend_fmap {A : Type} (a : A) {X Y : Type} (f : X -> Y) 
                       (x : Extend a X) : Extend a Y :=
  match x with
  | hd => hd
  | tl x => tl (f x)
  end.

Instance extend_functor {A} (a : A) : Monad.Functor (Extend a) := 
         {fmap := @extend_fmap _ a}.

Inductive Exp X : QType -> Type :=
| Var : forall {Q}, X -> Exp X Q
| App : forall {Q R}, Exp X (Q ⊸ R) -> Exp X Q -> Exp X R
| Abs : forall {Q R}, Exp (Extend Q X) R -> Exp X (Q ⊸ R) 
| Pair : forall {Q R}, Exp X Q -> Exp X R -> Exp X (Q ⊗ R)
| LetPair : forall {Q1 Q2 R}, 
            Exp X (Q1 ⊗ Q2) -> Exp (Extend Q1 (Extend Q2 X)) R -> Exp X R
| Put : forall {τ} `{DecidablePaths τ}, τ -> Exp X (Lower τ)
| LetBang : forall {τ Q} `{DecidablePaths τ}, 
  Exp X (Lower τ) -> (τ -> Exp X Q) -> Exp X Q
| new  : Bool -> Exp X Qubit
| meas : Exp X Qubit -> Exp X (Lower Bool)
.

Arguments Var {X} {Q} x.
Arguments App {X} {Q R}.
Arguments Abs {X} {Q R}.
Arguments Pair {X} {Q R}.
Arguments LetPair {X} {Q1 Q2 R}.
Arguments Put {X} {τ} {decτ} (x) : rename.
Arguments LetBang {X τ Q} {decτ} : rename.
Arguments new {X}.
Arguments meas {X}.

(* These axioms should be incorporated into the equational theory *)
Axiom new_meas : forall X b, meas (@new X b) = Put (negb b).


Definition exp_fmap {X Y : Type} (f : X -> Y) {Q} (e : Exp X Q) : Exp Y Q.
Proof.
  generalize dependent Y.
  induction e; intros Y f.
  - exact (Var (f x)).
  - exact (App (IHe1 Y f) (IHe2 Y f)).
  - exact (Abs (IHe (Extend Q Y) (fmap f))).
  - exact (Pair (IHe1 _ f) (IHe2 _ f)).
  - exact (LetPair (IHe1 _ f) (IHe2 _ (fmap (fmap f)))).
  - exact (Put τ0).
  - exact (LetBang (IHe _ f) (fun x => X0 x _ f)).
  - exact (new b).
  - exact (meas (IHe _ f)).
Defined.

Definition shift {X} {Q R : QType} (e : Exp X R) : Exp (Extend Q X) R := 
    exp_fmap tl e.

Definition exp_option_lift {X Y : Type} {Q R} (f : X -> Exp Y R) (x : Extend Q X) 
                           : Exp (Extend Q Y) R :=
  match x with
  | hd => Var hd
  | tl x' => shift (f x') 
  end.


Definition exp_bind {X Q} (e : Exp X Q) : forall {Y} 
                    (f : forall S, X -> option (Exp Y S)),
                    option (Exp Y Q).
Proof.
  induction e; intros Y f.
  - exact (f _ x).
  - exact (do e1 ← IHe1 _ f;
           do e2 ← IHe2 _ f;
           return_ (App e1 e2)).
  - apply (fmap Abs).
    exact (IHe _ (fun S ext => match ext with
                               | hd => Some (Var hd)
                               | tl z => fmap shift (f _ z)
                               end)).
  - exact (do e1 ← IHe1 _ f;
           do e2 ← IHe2 _ f;
           return_ (Pair e1 e2)).
  - refine (do e1 ← IHe1 _ f;
            do e2 ← IHe2 _ _;
            return_ (LetPair e1 e2)).
    refine (fun S ext => match ext with
                         | hd => (* 0:Q1 ↦ Var 0 *) Some (Var hd)
                         | tl hd => Some (Var (tl hd)) (* 1:Q2 ↦ Var 1 *)
                         | tl (tl z) => fmap shift (fmap shift (f _ z))
                         end).
  - refine (Some (Put τ0)).
  - refine (do e1 ← IHe _ f; _).
    admit (*??? *).
  - refine (Some (new b)).
  - exact (do e' ← IHe _ f; return_ (meas e')).
Admitted.

Definition subst_var {X} {R} (e : Exp X R) (x : Extend R X) : Exp X R :=
  match x with
  | hd => e
  | tl y => Var y
  end.

Definition subst {X} {Q R} (e : Exp X R) (e' : Exp (Extend R X) Q) 
            : option (Exp X Q).
Proof.
  apply (exp_bind e').
  intros S x.
  destruct (dec_paths S R) as [H | H].
  - (* S = R *) rewrite H; clear S H.
    exact (Some (subst_var e x)).
  - (* S <> R *) exact None.
Defined.

Inductive exp_step : forall X Q, Exp X Q -> Exp X Q -> Type :=
| β_App : forall X Q R (e1 : Exp (Extend Q X) R) (e2 : Exp X Q) (e' : Exp X R),
          subst e2 e1 = Some e' ->
          exp_step (App (Abs e1) e2) e'
| η_App : forall X Q R (e : Exp X (Q ⊸ R)),
          exp_step e (Abs (App (shift e) (Var hd)))
.

Definition trunc_exp_step X Q : Exp X Q -> Exp X Q -> Type :=
  fun e1 e2 => Trunc -1 (exp_step e1 e2).
Definition ExpEq X Q := quotient (@trunc_exp_step X Q).

Notation "(| e |)" := (class_of (@trunc_exp_step _ _) e) (at level 40).

(* unitaries *)

Definition unitary {X} {Q1 Q2} (U : Q1 = Q2) (e : Exp X Q1) : Exp X Q2 :=
  transport _ U e.

Definition Unitary (Q : QType) := Q = Q.


Lemma U_compose : forall (Q1 Q2 Q3 : QType) (U1 : Q1 = Q2) (U2 : Q2 = Q3)
                  {X} (e : Exp X Q1),
      unitary U2 (unitary U1 e) = unitary (U1 @ U2) e.
Proof.
  destruct U1. intros. simpl. rewrite concat_1p. reflexivity.
Defined.

Lemma U_U_transpose : forall (Q : QType) (U : Unitary Q) {X} (e : Exp X Q),
      unitary (U^) (unitary U e) = e.
Proof. 
  intros. rewrite U_compose. rewrite concat_pV. reflexivity.
Defined.

Lemma H_H_inverse : forall {X} (e : Exp X Qubit), unitary H (unitary H e) = e.
Proof.
  intros.
  refine (_ @ U_U_transpose H e).
  set (P := fun U => unitary U (unitary H e) = unitary H^ (unitary H e)).
  apply (transport P H_dag idpath).
Defined.

Definition U_lolli Q1 Q1' Q2 Q2' (U1 : Q1 = Q1') (U2 : Q2 = Q2') : (Q1 ⊸ Q2) = (Q1' ⊸ Q2').
Proof.
  destruct U1.
  destruct U2.
  reflexivity.
Defined.


Lemma U_lolli_unitary' : forall X Q1 Q1' Q2 Q2' (U1 : Q1 = Q1') (U2 : Q2 = Q2') 
                        (e : Exp X (Q1 ⊸ Q2)),
      (| unitary (U_lolli U1 U2) e |)
    = (| Abs (unitary U2 (App (shift e) (unitary U1^ (Var hd)))) |).
Proof.
  destruct U1; destruct U2; intros.
  simpl. 
  apply related_classes_eq.
  apply tr.
  apply η_App.
Defined.

Definition abs {X} Q1 Q2 (f : Extend Q1 X -> Exp (Extend Q1 X) Q2) : Exp X (Q1 ⊸ Q2) :=
  Abs (f hd).
Notation "λ x ~> e" := (abs (fun x => e)) (left associativity, at level 40).
Notation "U1 -u⊸ U2" := (U_lolli U1 U2) (at level 30).
Notation "e1 `app` e2" := (App e1 e2) (at level 30).
  
Corollary U_lolli_unitary : forall X Q1 Q2 
                                   (U1 : Unitary Q1) (U2 : Unitary Q2)
                                   (e : Exp X (Q1 ⊸ Q2)),
          (| unitary (U1 -u⊸ U2) e |)
        = (| abs(fun x => unitary U2 (shift e `app` unitary U1^ (Var x))) |).
Proof.
  intros.
  apply U_lolli_unitary'.
Defined.

Lemma unitary_id : forall X Q (e : Exp X Q), e = unitary idpath e.
Proof. reflexivity. Defined.

(* CANNOT prove this *)
Lemma U_not_id : forall Q (U : Q = Q) X (e : Exp X Q),
                 unitary U e = e ->
                 U = 1%path.
Abort.


Instance toClassical_Deciable Q : DecidablePaths (toClassical Q).
Admitted.

Definition meas_any {Q : QType} {X} (e : Exp X Q) : Exp X (Lower (toClassical Q)).
Proof.
  generalize dependent X.
Admitted.

(* This was an axiom, but we can prove it instead! *)
Lemma unitary_discard : forall Q1 Q2 (U : Q1 = Q2) 
                        X Q (e : Exp X Q1) (e' : Exp X Q),
   LetBang (meas_any (unitary U e)) (fun _ => e') = LetBang (meas_any e) (fun _ => e').
Proof.
  induction U; reflexivity.
Defined.