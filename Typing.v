Require Import HoTT.
Add LoadPath "./LinearTypingContexts/" as LinearTypingContexts.
Require LinearTypingContexts.Monad.
Require Import LinearTypingContexts.Monad.
Require Import LinearTypingContexts.Monoid.
Require Import LinearTypingContexts.TypingContext.
(*Require Import LinearTypingContexts.SetContext.*)
Require Import QTypes Syntax.

(* Typing Judgment *)

Notation "x : q ∉ Γ" := (is_valid (Γ ∙ singleton x q)) (at level 30).

Section Typing.
  Variable Var' : Type.
  Variable Ctx : Type.
  Context `{TypingContext_Laws Var' QType Ctx}.

  Let Var (_ : QType) := Var'.


  Inductive WF_Exp : forall {q}, Ctx -> exp Var q -> Type :=
  | WF_Var {Γ q} (x : Var q) :
    Γ = singleton x q ->
    WF_Exp Γ (var x)

  | WF_Abs {Γ q r} (f : Var q -> exp Var r) :
    (forall (x : Var q), x : q ∉ Γ -> WF_Exp (Γ ∙ singleton x q) (f x)) ->
    WF_Exp Γ (abs f)

  | WF_App {Γ Γ1 Γ2 q r} (e : exp Var (q ⊸ r)) (e' : exp Var q) :
    WF_Exp Γ1 e -> WF_Exp Γ2 e' ->
    Γ = Γ1 ∙ Γ2 -> is_valid Γ ->
    WF_Exp Γ (app e e')

  | WF_Pair {Γ Γ1 Γ2} {q1 q2} (e1 : exp Var q1) (e2 : exp Var q2) :
    WF_Exp Γ1 e1 -> WF_Exp Γ2 e2 -> 
    Γ = Γ1 ∙ Γ2 -> is_valid Γ ->
    WF_Exp Γ (pair e1 e2)

  | WF_LetPair {Γ Γ1 Γ2} {q1 q2 r} (e : exp Var (q1 ⊗ q2)) 
                                   (f : Var q1 -> Var q2 -> exp Var r) :
    WF_Exp Γ1 e -> 
    (forall x1 x2, is_valid (Γ2 ∙ singleton x1 q1 ∙ singleton x2 q2) ->
                   WF_Exp (Γ2 ∙ singleton x1 q1 ∙ singleton x2 q2) (f x1 x2)) ->
    Γ = Γ1 ∙ Γ2 -> is_valid Γ ->
    WF_Exp Γ (let_pair e f)

  | WF_Put {τ} (x : τ) :
    WF_Exp ⊤ (put x)

  | WF_LetBang {τ} {Γ Γ1 Γ2} {q} (e : exp Var (Lower τ))
                                             (f : τ -> exp Var q) :
    WF_Exp Γ1 e ->
    (forall (x : τ), WF_Exp Γ2 (f x)) ->
    Γ = Γ1 ∙ Γ2 -> is_valid Γ ->
        WF_Exp Γ (let_bang e f)

  | WF_New b : WF_Exp ⊤ (new b)
  | WF_Meas {Γ} (e : exp Var Qubit) :
    WF_Exp Γ e ->
    WF_Exp Γ (meas e)
  .
    
End Typing.

