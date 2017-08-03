Require Import MyNotations.
Require Import HoTT.
Set Implicit Arguments.

(** * The Functor Type Class *)

Class Functor (f : Type -> Type) : Type :=
{ fmap         : ∀ {A B}, (A -> B) -> f A -> f B }. 
Class Functor_Correct (f : Type -> Type) `{F : Functor f} :=
{ fmap_id      : ∀ A, fmap (λ (x:A) · x) = (λ x · x);
  fmap_compose : ∀ A B C (g : A -> B) (f : B -> C), 
                 fmap (f ∘ g) = fmap f ∘ fmap g
}.
Class Applicative (f : Type -> Type) `{F : Functor f} : Type :=
{ pure : ∀ {A}, A -> f A;
  liftA : ∀ {A B}, f (A -> B) -> f A -> f B
}.
Notation "f <*> a" := (liftA f a) (left associativity, at level 25).


Class Applicative_Correct (f : Type -> Type) `{Applicative f} :=
{ applicative_id : ∀ A, liftA (pure (λ (x:A) · x)) = (λ x · x);
  applicative_composition : forall {A B C} (u : f (B -> C)) (v : f (A -> B)) (w : f A),
    pure (λ x · λ y · x ∘ y) <*> u <*> v <*> w = u <*> (v <*> w);
  applicative_homomorphism : forall {A B} (f : A -> B) (x : A),
    pure f <*> pure x = pure (f x);
  applicative_interchange : forall {A B} (u : f (A -> B)) (y : A),
    u <*> pure y = pure (fun x => x y) <*> u
}.

Class Monad (m: Type → Type) `{M : Applicative m} : Type :=
{ bind: ∀ {A}, m A → ∀ {B}, (A → m B) → m B
}.
Definition return_ {m : Type -> Type} `{M : Monad m} {A : Type} : A -> m A := pure.
Notation "a >>= f" := (bind a f) (at level 50, left associativity).


Class Monad_Correct (m : Type -> Type) `{M : Monad m} := {
  right_unit: ∀ A (a: m A), a = a >>= return_;
  left_unit: ∀ A (a: A) B (f: A → m B),
             f a = return_ a >>= f;
  associativity: ∀ A (ma: m A) B f C (g: B → m C),
                 bind ma (λ x· f x >>= g) = (ma >>= f) >>= g
}.

Arguments Applicative f [F].
Arguments Monad m [F] [M].
About Monad.

Section monadic_functions.
 Variable m : Type → Type. 
 Variable F : Functor m.
 Variable A : Applicative m.
 Variable M : Monad m.

 Definition wbind {A: Type} (ma: m A) {B: Type} (mb: m B) :=
 ma >>= λ _·mb.

 Definition liftM {A B: Type} (f: A→B) (ma: m A): m B :=
 ma >>= (λ a · return_ (f a)).

 Definition join {A: Type} (mma: m (m A)): m A :=
 mma >>= (λ ma · ma).
End monadic_functions.

Notation "a >> f" := (wbind _ a f) (at level 50, left associativity).
Notation "'do' a ← e ; c" := (e >>= (λ a · c)) (at level 60, right associativity).

(** * Some classic Monads *)
(** ** The Maybe monad (using option type) *) 

Definition option_fmap {A B} (f : A -> B) (x : option A) : option B :=
  match x with
  | None => None
  | Some a => Some (f a)
  end.
Definition option_liftA {A B} (f : option (A -> B)) (x : option A) : option B :=
  match f, x with
  | Some f', Some a => Some (f' a)
  | _, _ => None
  end.
Instance optionF : Functor option := { fmap := @option_fmap}.
Instance optionA : Applicative option := { pure := @Some;
                                           liftA := @option_liftA}.
Instance optionM : Monad option :=
  { bind := λ A m B f · match m with None => None | Some a => f a end
  }.
(*
(* Checking the 3 laws *)
 - (* unit_left *)
   abstract (intros A a; case a; split).
 - (* unit_right *)
   abstract (split).
 - (* associativity *)
   abstract (intros A m B f C g; case m; split).
Defined.
*)

(* Monad Transformer *)
Class MonadTrans (t : (Type -> Type) -> (Type -> Type)) :=
  { liftT : forall {m} `{Monad m} {A}, m A -> t m A }.


(** Option monad transformer *)
Definition optionT m (A : Type) : Type := m (option A).

Definition optionT_liftT {m} `{Monad m} {A} (x : m A) : optionT m A.
Proof.
  unfold optionT.
  refine (do a ← x; return_ (Some a)).
Defined.
Instance optionT_T : MonadTrans optionT := {liftT := @optionT_liftT}.

Definition optionT_fmap {f} `{Functor f} 
                        {A B} (g : A -> B) (x : optionT f A) : optionT f B :=
  @fmap f _ _ _ (fmap g) x.
Definition optionT_liftA {f} `{Applicative f}
                         {A B} (g : optionT f (A -> B)) (x : optionT f A) 
                       : optionT f B.
(*  @liftA f _ _ _ _ (fmap liftA g) x.*)
Proof. 
  unfold optionT in *.
  exact (fmap liftA g <*> x).
Defined. 
Definition optionT_pure {f} `{Applicative f}
                        {A} (a : A) : optionT f A := @pure f _ _ _ (pure a).
Definition optionT_bind {m} `{Monad m}
                        {A} (ma : optionT m A) {B} (f : A -> optionT m B)
                        : optionT m B.
  unfold optionT in *.
  exact (do oa ← ma; 
         match oa with
         | None => pure None
         | Some a => f a
         end
  ).
Defined.

Instance optionT_F {f} `{Functor f} : Functor (optionT f) := 
    {fmap := @optionT_fmap f _}.
Instance optionT_A {f} `{Applicative f} : Applicative (optionT f) :=
  { pure := @optionT_pure f _ _;
    liftA := @optionT_liftA f _ _ }.
Instance optionT_M {m} `{Monad m} : Monad (optionT m) :=
  { bind := @optionT_bind m _ _ _ }.

(** The Reader monad *)
Axiom Eta: ∀ A (B: A → Type) (f: ∀ a, B a), f = λ a·f a.

Definition Reader (E : Type) := λ X · E -> X.
Definition reader_fmap E A B (f : A -> B) (r : Reader E A) : Reader E B :=
  fun x => f (r x).
Definition reader_liftA E A B (f : Reader E (A -> B)) (r : Reader E A) :=
  fun x => (f x) (r x).
Definition reader_bind E A (r : Reader E A) B (f : A -> Reader E B) : Reader E B :=
  fun x => f (r x) x.
  
Instance readerF E : Functor (Reader E) :=
 { fmap := @reader_fmap E }.
Instance readerA E : Applicative (Reader E) :=
 { pure := λ A (a:A) e· a;
   liftA := @reader_liftA E }.
Instance readerM (E : Type): Monad (Reader E) :=
 { bind := @reader_bind E }.
(*
(* Checking the 3 laws *)
 - (* unit_left *)
   intros; apply Eta.
 - (* unit_right *)
   intros; apply Eta.
 - (* associativity *)
   reflexivity.
Defined.
*)
(** ** The State monad *)

Axiom Ext: ∀ A (B: A→Type) (f g: ∀ a, B a), (∀ a, f a = g a) → f = g.

Definition State (S : Type) (A : Type) := S → A * S.
Definition state_fmap S A B (f : A -> B) (st : State S A) : State S B :=
  λ s · let (a,s) := st s in (f a,s).
Definition state_liftA S A B (st_f : State S (A -> B)) (st_a : State S A) :=
  λ s · let (f,s) := st_f s in
        let (a,s) := st_a s in
        (f a,s).
Definition state_bind S A (st_a : State S A) B  (f : A -> State S B) :=
  λ s · let (a,s) := st_a s in
        f a s.

Instance stateF S : Functor (State S) :=
  { fmap := @state_fmap S }.
Instance stateA S : Applicative (State S) :=
  { pure := λ A a s· (a,s);
    liftA := @state_liftA S }.
Instance stateM S : Monad (State S) :=
  { bind := @state_bind S }.

(*
(* Checking the 3 laws *)
 (* unit_left *)
 abstract (intros;apply Ext;intros s;destruct (a s);split).
 (* unit_right *)
 abstract (intros;apply Eta).
 (* associativity *)
 abstract (intros;apply Ext;intros s;destruct (ma s);reflexivity).
Defined.
*)

(*

(** ** The tree monad *)
Inductive Tree (A:  Type) :=
| Leaf: A → Tree A
| Branch: Tree A → Tree A → Tree A
.

Definition bind_tree {A B: Type} (f: A → Tree B) :=
 fix bind_tree t :=
 match t with
 | Leaf a => f a
 | Branch t1 t2 => Branch (bind_tree t1) (bind_tree t2)
 end.

Instance tree : Monad Tree.
refine {| return_ := Leaf;
  bind := λ A t B f · bind_tree f t
|}.
(* Checking the 3 laws *)
 (* unit_left *)
 Lemma tree_unit_left: ∀ A a, a = bind_tree (@Leaf A) a.
 Proof.
    intros A. induction a; auto. 
    simpl. f_ap. 
 Qed.
 exact tree_unit_left.
 (* unit_right *)
 Lemma tree_unit_right: ∀ A a B (f : A → Tree B), f a = bind_tree f (Leaf a).
 Proof.
  simpl; split.
 Qed.
 exact tree_unit_right.
 (* associativity *)
 Lemma tree_associativity: ∀ A (m : Tree A) B f C (g : B → Tree C),
 bind_tree (bind_tree g ∘ f) m = bind_tree g (bind_tree f m).
 Proof.
  induction m; intros; simpl; auto.
  f_ap. 
 Qed.
 exact tree_associativity.
Defined.


(** ** A light version of the IO monad *)
Require Import Ascii.
Open Scope char_scope.

CoInductive stream: Type :=
| Stream: ascii → stream → stream
| EmptyStream.

Record std_streams: Type :=
{ stdin: stream;
  stdout: stream;
  stderr: stream
}.

Definition io (A: Type) := std_streams → (A * std_streams).

Instance IO : Monad io :=
{| return_ := λ A (a: A) s · (a, s);
   bind := λ A a B (f: A → io B) s · let (a, s) := (a s) in f a s
|}.
(* Checking the 3 laws *)
 (* unit_left *)
 Lemma io_unit_left:
 ∀ A (a: io A), a = (λ s : std_streams · let (a, s) := a s in (a, s)).
 Proof.
 intros; apply Ext.
 intros s; case (a s); split.
Qed.
 exact io_unit_left.
 (* unit_right *)
 Lemma io_unit_right:
 ∀ A a B (f : A → io B), f a = (λ s : std_streams · f a s).
 Proof.
 intros; apply Ext.
 split.
Qed.
 exact io_unit_right.
 (* associativity *)
 Lemma io_associativity: ∀ A (m : io A) B (f: A → io B) C (g : B → io C),
 (λ s · let (a, s0) := m s in let (a0, s1) := f a s0 in g a0 s1) =
 (λ s · let (a, s0) := let (a, s0) := m s in f a s0 in g a s0).
 Proof.
 intros; apply Ext.
 intros; case (m a); split.
Qed.
 exact io_associativity.
Defined.

Definition getchar: io ascii :=
 λ i·
 let (c, stdin) :=
 match i.(stdin) with
 | EmptyStream => ("#", EmptyStream) (*I do not remember the code of EOF *)
 | Stream a i => (a, i)
 end
 in (c, {|stdin := stdin; stdout := i.(stdout); stderr := i.(stderr)|}).

Definition putchar (a: ascii): io unit :=
 λ i·
 let stdout :=
 (cofix putchar i :=
 match i with
 | EmptyStream => Stream a EmptyStream
 | Stream a i => Stream a (putchar i)
 end) i.(stdout)
 in (tt, {|stdin:=i.(stdin); stdout:=stdout; stderr:=i.(stderr)|}).

Definition err_putchar (a: ascii): io unit :=
 λ i·
 let stderr :=
 (cofix putchar i :=
 match i with
 | EmptyStream => Stream a EmptyStream
 | Stream a i => Stream a (putchar i)
 end) i.(stderr)
 in (tt, {|stdin:=i.(stdin); stdout:=i.(stdout); stderr:=stderr|}).


Require Import Datatypes.
Require Import Data.List.
(*Require Import List.*)

Fixpoint lts l :=
match l with
| nil => EmptyString
| c::l => String c (lts l)
end.

Fixpoint ltS l :=
match l with
| nil => EmptyStream
| c::l => Stream c (ltS l)
end.

Example some_std_streams :=
{| stdin := ltS ("H"::"e"::"l"::"l"::"o"::","::" "::"W"::"o"::"r"::"l"::"d"::
                 "!"::nil);
   stdout := EmptyStream;
   stderr := EmptyStream
|}.

Example prog :=
 (do h    ← getchar;
  do e    ← getchar;
  do l1   ← getchar;
  do l2   ← getchar;
  do o1   ← getchar;
  do coma ← getchar;
  putchar "E" >>
  do space← getchar;
  do w    ← getchar;
  do o2   ← getchar;
  putchar "n" >>
  do r    ← getchar;
  do l3   ← getchar;
  do d    ← getchar;
  putchar d >>
  do bang ← getchar;
  do eof1 ← getchar;
  do eof2 ← getchar;
  do eof3 ← getchar;
  return_ (lts (h::e::l1::l2::o1::coma::space::w::o2::r::l3::d::
                bang::eof1::eof2::eof3::nil))).

Eval compute in (prog some_std_streams).
Eval compute in (let out := (snd (prog some_std_streams)).(stdout) in
                prog {|stdin := out;
                       stdout := EmptyStream;
                       stderr := EmptyStream|}).

*)