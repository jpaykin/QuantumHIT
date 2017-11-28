Require Import HoTT.
Require Import quotient1.
Require Import QTypes.


Section Exp.
  
  Variable Var : QType -> Type.

  Inductive exp : QType -> Type :=
  | var {q} : Var q -> exp q
  | abs {q r} : (Var q -> exp r) -> exp (q ⊸ r)
  | app {q r} : exp (q ⊸ r) -> exp q -> exp r
  | pair {q r} : exp q -> exp r -> exp (q ⊗ r)
  | let_pair {q r s} : exp (q ⊗ r) -> (Var q -> Var r -> exp s) -> exp s
  | put {τ} `{IsHSet τ} : τ -> exp (Lower τ)
  | let_bang {τ} `{IsHSet τ} {q} : exp (Lower τ) -> (τ -> exp q) -> exp q
  | new : Bool -> exp Qubit
  | meas : exp Qubit -> exp (Lower Bool)
  .

  Inductive is_value : forall {q}, exp q -> Type :=
  | v_abs {q r} (f : Var q -> exp r) : is_value (abs f)
  | v_pair {q r} (e1 : exp q) (e2 : exp r) : is_value e1 -> 
                                             is_value e2 -> 
                                             is_value (pair e1 e2)
  | v_put {τ} `{IsHSet τ} (x : τ) : is_value (put x)
  | v_new (b : Bool) : is_value (new b)
  .

End Exp.

Arguments var {Var} {q}.
Arguments abs {Var} {q r}.
Arguments app {Var} {q r}.
Arguments pair {Var} {q r}.
Arguments let_pair {Var} {q r s}.
Arguments put {Var} {τ} {hset} : rename.
Arguments let_bang {Var} {τ} {hset} {q} : rename.
Arguments new {Var}.
Arguments meas {Var}.


(**************)
(* flattening *)
(**************)

Section Squash.
  Variable Var : QType -> Type.

  Fixpoint squash {q} (e : exp (exp Var) q) : exp Var q.
  Proof.
    destruct e as [ q x | q r f | q r e1 e2 (* abstraction *)
                  | q r e1 e2 | q r s e e' (* pairs *)
                  | τ H x | τ H q e e' (* let! *)
                  | | e (* new *) ].
    * exact x.
    * exact (abs (fun x => squash _ (f (var x)))).
    * exact (app (squash _ e1) (squash _ e2)).
    * exact (pair (squash _ e1) (squash _ e2)).
    * exact (let_pair (squash _ e) (fun x1 x2 => squash _ (e' (var x1) (var x2)))).
    * exact (put x).
    * exact (let_bang (squash _ e) (fun x => squash _ (e' x))).
    * exact (new b).
    * exact (meas (squash _ e)).
  Defined.
End Squash.
Arguments squash {Var} {q}.

(* Polymorphic expressions *)

Definition Exp q := forall Var, exp Var q.
Definition Exp1 q r := forall Var, Var q -> exp Var r.
Definition Exp2 q r s := forall Var, Var q -> Var r -> exp Var s.
Notation "q --o r" := (Exp1 q r) (at level 30).

Definition Subst {q r} (f : q --o r) (e : Exp q) : Exp r := fun Var =>
  squash (f (exp Var) (e Var)).

Definition Subst2 {q r s} (f : Exp2 q r s) (e1 : Exp q) (e2 : Exp r) : Exp s := 
  fun Var => squash (f (exp Var) (e1 Var) (e2 Var)).


Definition Abs {q r} (f : q --o r) : Exp (q ⊸ r) := fun Var =>
    abs (f Var).
Definition App {q r} (e : Exp (q ⊸ r)) (e' : Exp q) : Exp r := fun Var =>
    app (e Var) (e' Var).

Definition Pair {q r} (e1 : Exp q) (e2 : Exp r) : Exp (q ⊗ r) := fun Var =>
    pair (e1 Var) (e2 Var).
Definition Let_Pair {q r s} (e : Exp (q ⊗ r)) (f : Exp2 q r s) : Exp s := fun Var =>
    let_pair (e Var) (f Var).

Definition Put {τ} `{IsHSet τ} (x : τ) : Exp (Lower τ) := fun _ => put x.
Definition Let_Bang {τ} `{IsHSet τ} {q} 
           (e : Exp (Lower τ)) (f : τ -> Exp q) : Exp q := fun Var =>
    let_bang (e Var) (fun x => f x Var).

Definition New (b : Bool) : Exp Qubit := fun _ => new b.
Definition Meas (e : Exp Qubit) : Exp (Lower Bool) := fun Var =>
    meas (e Var).


(*************************)
(* Operational semantics *)
(*************************)

Inductive β : forall {q}, Exp q -> Exp q -> Type :=
| β_lolli {q r} (f : q --o r) (e : Exp q) : 
    β (App (Abs f) e) (Subst f e)

| β_tensor {q r s} (e1 : Exp q) (e2 : Exp r) (f : Exp2 q r s) : 
    β (Let_Pair (Pair e1 e2) f) (Subst2 f e1 e2)

| β_lower {τ} `{IsHSet τ} {q} (x : τ) (f : τ -> Exp q) :
    β (Let_Bang (Put x) f) (f x)

| β_qubit (b : Bool) :
    β (Meas (New b)) (Put b)
.

Instance β_relation : forall q, is_mere_relation (Exp q) β.
Admitted. (* should be true because β is type directed *)

About quotient.
About class_of.
About related_classes_eq.
Definition βExp q := quotient (@β q).

About class_of.
Notation "[ e ]" := (class_of β e).
Notation "e1 ≡ e2" := ([e1] = [e2]) (at level 50).

Lemma equiv_trans : forall {q} (e1 e2 e3 : Exp q),
      e1 ≡ e2 -> e2 ≡ e3 -> e1 ≡ e3.
Proof.
  intros.
  transitivity ([e2]); auto.
Qed.

Lemma β_lolli' : forall q r (f : q --o r) (e : Exp q),
      App (Abs f) e ≡ Subst f e.
Proof.
  intros q r f e.
  apply related_classes_eq.
  apply β_lolli.
Qed.

(* Note: We do not expect progress to hold! *)


(*************)
(* unitaries *)
(*************)

Definition unitary {q r} (U : q = r) (e : Exp q) : Exp r := transport _ U e.
Definition Unitary (q : QType) := q = q.


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

Axiom H' : UnitaryMatrix Qubit' Qubit'.
Axiom H'_dag : (H'^ = H')%groupoid.
Definition H : Unitary Qubit := cell _ H'.
Lemma H_dag : H^ = H.
Proof.
  unfold H.
  Local Open Scope groupoid_scope.
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

Section meas_all.

  Variable Var : QType -> Type.
  Context `{Univalence}. (* need this for to_classical *)

  Definition to_classical_QType q := Lower (to_classical q).
  
  Lemma to_classical_lolli : forall q r, to_classical (q ⊸ r) = BuildhSet Unit.
  Admitted.

  Lemma to_classical_tensor : forall q r, 
        to_classical (q ⊗ r) = BuildhSet (to_classical q * to_classical r).
  Admitted.

  Fixpoint meas_all {q} (e : exp to_classical q) : exp Var (Lower (to_classical q)).
  Proof.
    destruct e as [ q x | q r f | q r e1 e2 (* abstraction *)
                  | q r e1 e2 | q r s e e' (* pairs *)
                  | τ H x | τ H q e e' (* let! *)
                  | | e (* new *) ].
    * exact (put x).
    * rewrite to_classical_lolli. 
      exact (put tt).
    * admit (* not sure what to do here *) (*!!!!!*).
    * rewrite to_classical_tensor. simpl.
      exact (let_bang (meas_all _ e1) (fun x1 =>
              let_bang (meas_all _ e2) (fun x2 =>
              put (x1, x2)))).
    * set (e0 := meas_all _ e). 
      rewrite to_classical_tensor in e0. simpl in e0.
      exact (let_bang e0 (fun z => let (x,y) := z in
                                   meas_all _ (e' x y))).
    * exact (put x).
    * exact (let_bang (meas_all _ e) (fun x => meas_all _ (e' x))).
    * exact (put b).
    * set (e' := meas_all _ e). simpl in e'.
      simpl in *. 
      (*exact e'.*)
      admit (* the only problem is a difference in the argumenent that Bool is
               1-truncated.. *).
  Admitted.

End meas_all.

Definition Meas_All `{Univalence} {q} (e : Exp q) : Exp (Lower (to_classical q)) :=
  fun Var => meas_all Var (e _).
  

Lemma unitary_discard `{Univalence} : 
      forall q1 q2 (U : q1 = q2) q (e1 : Exp q1) (e : Exp q),
      Let_Bang (Meas_All (unitary U e1)) (fun _ => e) 
    = Let_Bang (Meas_All e1) (fun _ => e).
Proof.
  destruct U; intros.
  reflexivity.
Qed.
