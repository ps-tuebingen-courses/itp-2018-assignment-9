
(* We have the type of natural numbers, and function types.
For function types we add the special notation "==>" which associates to the right. *)
Inductive Types :=
| Nat : Types
| Fun : Types -> Types -> Types.
Notation "t1 ==> t2" := (Fun t1 t2) (at level 80, right associativity).

Example example_type1 : Types := Nat ==> Nat ==> Nat.
Example example_type2 : Types := (Nat ==> Nat) ==> Nat.

(* Expressions are build up from the five constants, and are combined with App. Expressions are 
   inherently typed, so it is not possible to form ill-typed expressions.
   Note that the type arguments are marked as implicit, so Coq tries to infer them automatically,
   For application we use the special notation "@" which associates to the left. *)

(* Task 1: Extend the following inductive datatype with the constructors for K and O. *)
Inductive Expr : Types ->  Type :=
(*| K : ... *)
| S : forall {x y z : Types}, Expr ((x ==> (y ==> z)) ==> (x ==> y) ==> (x ==> z))
(*| O : ... *)
| Succ : Expr (Nat ==> Nat)
| iterate : forall {x : Types}, Expr (Nat ==> (x ==> x) ==> x ==> x)
| App : forall {x y : Types}, Expr (x ==> y) -> Expr x -> Expr y. 
Notation "e1 @ e2" := (App e1 e2) (at level 81, left associativity).

Example one : Expr Nat := Succ @ O.
Example two : Expr Nat := Succ @ (Succ @ O).
Example three : Expr Nat := Succ @ (Succ @ (Succ @ O)).
Example four : Expr Nat := Succ @ (Succ @ (Succ @ (Succ @ O))).

(* As an additional example, consider the defined term I = SKK with reduction behaviour "I x = x".
   Note that we have to annotate some term (in this case, K) to get the type inference of
   Coq to work. *)
Example I :forall (t : Types), Expr (t ==> t) := fun t =>  S @ K @ (@K t t).

(* The reduction semantics is given by the following inductive relation.
   Observe that the type of the relation guarantees that the reduction
   does not change the type of the expression. *)

(* Task 2: Extend the evaluate relation with the missing cases for S and iterate succ *)
Inductive evaluate : forall (x : Types), Expr x -> Expr x -> Prop :=
| eval_cong_left : forall (t1 t2 : Types) (e1 e1': Expr (t1 ==> t2)) (e2 : Expr t1),
    evaluate (t1 ==> t2) e1 e1' ->
    evaluate t2 (e1 @ e2) (e1' @ e2)
| eval_cong_right : forall (t1 t2 : Types) (e1 : Expr (t1 ==> t2)) (e2 e2': Expr t1),
    evaluate t1 e2 e2' ->
    evaluate t2 (e1 @ e2) (e1 @ e2')
| eval_K : forall (t1 t2 : Types) (e1 : Expr t1) (e2 : Expr t2),
    evaluate t1
             (K @ e1 @ e2)
             e1
(*| eval_S : ... *)
(*| eval_iterate_succ : *)
| eval_iterate_zero : forall (t : Types) (f : Expr ( t ==> t)) (ex : Expr t),
    evaluate t
             (iterate @ O @  f @ ex)
             ex.

(* evaluate_tr is the transitive-reflexive closure of evaluate *)
Inductive evaluate_tr : forall (x : Types), Expr x -> Expr x -> Prop :=
  eval_refl : forall t e, evaluate_tr t e e
| eval_step : forall t e1 e2,
    evaluate t e1 e2 -> evaluate_tr t e1 e2
| eval_trans : forall t e1 e2 e3,
    evaluate t e1 e2 ->
    evaluate_tr t e2 e3 ->
    evaluate_tr t e1 e3.

(* Task 3: Prove that I works, i.e. that (I e) evaluates to e *)
Lemma I_works : forall (t : Types) (e : Expr t), evaluate_tr t ((@I t) @ e) e.
Proof.
  admit.
Admitted.

(* Task 4a: The constant K takes two arguments, and ignores its second argument.
   Write an expression K' which takes two arguments and ignores its first argument.
   Hint: You should solve this exercise on paper first. *)
Definition K' : forall {t1 t2 : Types},  Expr (t1 ==> t2 ==> t2) := (* TODO *)

(* Task 4b: Prove that your construction for K' works. *)
Lemma K'_works : forall (t1 t2 : Types) (e1 : Expr t1) (e2 : Expr t2),
    evaluate_tr t2 (K' @ e1 @ e2) e2.
Proof.
  admit.
Admitted.

(* Task 5a: Define an expression of type "Nat ==> Nat" which applied
   to a natural number evaluates to that number + 2. *)
Definition plus_two : Expr (Nat ==> Nat) := (* TODO *).

(* Task 5b: Prove that your construction works. *)
Lemma plus_two_works : evaluate_tr Nat (plus_two @ O) two.
Proof.
  admit.
Admitted.

(* Task 6a: Define an expression of type "Nat ==> Nat" which applied
   to a natural number doubles that number. *)
Definition double : Expr (Nat ==> Nat) := (* TODO *).

(* Task 6b: Prove your construction correct. *)
Lemma double_works : evaluate_tr Nat (double @ one) two.
Proof.
  admit.
Admitted.


