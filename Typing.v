Require Import HoTT.
Add LoadPath "./LinearTypingContexts/" as LinearTypingContexts.
Require LinearTypingContexts.Monad.
Require Import LinearTypingContexts.Monad.
Require Import LinearTypingContexts.NCM.
Require Import LinearTypingContexts.Permutation.
Require Import LinearTypingContexts.SetContext.
Require Import HIT.
Require Import Syntax.


(* Typing Judgment *)

Open Scope NCM_scope.

Definition QCtx X := Ctx X QType.
Inductive WF_Exp : forall {X Q}, QCtx X -> Exp X Q -> Type :=
| WF_Var : forall X (x : X) (Q : QType), 
           WF_Exp (singleton x Q : Ctx X QType) (@Var _ Q x)
| WF_App : forall X `{DecidablePaths X} (Γ1 Γ2 : QCtx X) Q R 
                  (e1 : Exp X (Q ⊸ R)) (e2 : Exp X Q),
           WF_Exp Γ1 e1 -> WF_Exp Γ2 e2 -> Γ1 · Γ2 <> 0 ->
           WF_Exp (Γ1 · Γ2) (App e1 e2)
| WF_Abs : forall X (Γ : QCtx X) Q R (e : Exp (Extend Q X) R),
           WF_Exp (extend Γ Q) e ->
           WF_Exp Γ (Abs e)
.

Definition wf_exp_fmap {X Y : Type} `{DecidablePaths X} `{DecidablePaths Y}
                       (f : X -> Y) {Q} (Γ : QCtx X) (e : Exp X Q) 
                       : WF_Exp Γ e -> WF_Exp (fmap f Γ) (exp_fmap f e).
Proof.
  intros H.
  generalize dependent Y.
  induction H; intros Y HY f.
  - rewrite fmap_singleton; auto.
    simpl. apply WF_Var.
  - erewrite fmap_merge.
    apply WF_App.
    * apply IHWF_Exp1; auto.
    * apply IHWF_Exp2; auto.
    * admit.
  - apply WF_Abs.
    set (H' := @fmap_extend QType X Y f _ _).
(*
    assert (H : fmap (fmap f) (extend Γ Q) = extend (fmap f Γ) Q).
*)
(*    apply IHWF_Exp.*)
Admitted.
