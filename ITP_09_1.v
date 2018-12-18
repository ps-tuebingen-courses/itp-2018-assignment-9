(* Task 1.1 : GADTs: Types as type parameters *)

Require Import Coq.Strings.String.

Inductive expr : Type :=
  | E_N_Lit : nat -> expr
  | E_S_Lit : string -> expr
  | E_Add : expr -> expr -> expr
  | E_Repeat : expr -> expr -> expr.

Inductive type : Type := T_Nat | T_String.

Inductive typechecks : expr -> type -> Prop :=
  | T_N_Lit : forall n, typechecks (E_N_Lit n) T_Nat
  | T_S_Lit : forall s, typechecks (E_S_Lit s) T_String
  | T_Add : forall e1 e2,
      typechecks e1 T_Nat ->
      typechecks e2 T_Nat ->
      typechecks (E_Add e1 e2) T_Nat
  | T_Repeat : forall e1 e2,
      typechecks e1 T_String ->
      typechecks e2 T_Nat ->
      typechecks (E_Repeat e1 e2) T_String.

(* Your task: Fill in the following two definitions such that the lemmas below hold,
   and prove the lemmas.
 *)
Inductive expr_t : type -> Type :=.

Fixpoint erase {t : type} (e : expr_t t) : expr. Admitted.

Lemma erased_expr_t_typechecks : forall (t : type) (e : expr_t t), typechecks (erase e) t.
Proof.
  admit.
Admitted.

(* Slightly advanced. *)
Lemma erase_surjective_over_tc : forall (t : type) (e : expr),
  typechecks e t ->
  exists (e' : expr_t t), erase e' = e.
Proof.
  admit.
Admitted.

(* Task 1.2 : Relations : values as type parameters *)

Require Import Coq.Lists.List.

Inductive sublist {A} (prefix : list A) : list A -> list A -> Prop :=
  | S_Nil : forall l, sublist prefix nil ((rev prefix) ++ l)
  | S_Cons : forall a l' l, sublist (a :: prefix) l' l -> sublist prefix (a :: l') l.

(* Your task: Prove the following two lemmas. *)
(* Hint: Try to first understand the definition of sublist.
   For instance, find out what the parameter prefix is used for.
 *)

(* Advanced *)
(* Hint: use app_assoc, app_eq_nil, and app_cons_not_nil *)
Lemma sublist_correct : forall {A} (prefix l' l : list A),
  sublist prefix l' l ->
  exists l0, l = (rev prefix) ++ l' ++ l0.
Proof.
  admit.
Admitted.

(* Slightly advanced *)
(* Hint: use rev_involutive *)
Lemma sublist_complete : forall {A} (prefix l l' l0 : list A),
  l = (rev prefix) ++ l' ++ l0 ->
  sublist prefix l' l.
Proof.
  admit.
Admitted.

(* Finally, here's how the two lemmas can be combined to show
   that our sublist relation indeed does exactly what we expect from it.
 *)

Lemma sublist_equivalent : forall {A} (l' l : list A),
  (exists prefix, sublist prefix l' l) <->
  exists l1 l0, l = l1 ++ l' ++ l0.
Proof with auto.
intros. split; intros.
- destruct H. exists (rev x). apply sublist_correct...
- destruct H as [l1 [l0 H]]. exists (rev l1).
  apply sublist_complete with (l3:=l0). rewrite rev_involutive...
Qed.


(* Task 1.3 : Option and partial maps *)

(* Consider again [erase] from task 1.
   Write a function that is the inverse of erase, but where you can select the type.
   Its result is of type option since not all expr are in the image of erase
   (and even less when considering only a specific type t).
 *)
Fixpoint unerase (t : type) (e : expr) : option (expr_t t). Admitted.

(* Finally, show that the functions and the relation behave as expected: *)

Lemma unerase_erase : forall (t : type) (e : expr_t t),
  unerase t (erase e) = Some e.
Proof.
  admit.
Admitted.


