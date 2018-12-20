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

(* Task 1: Give the missing constructors of expr_t. *)
Inductive expr_t : type -> Type :=
  (* | Et_N_Lit : .... *)
  (* | Et_S_Lit : ... *)
  (* | Et_Add :  ... *)
  | Et_Repeat : expr_t T_String -> expr_t T_Nat -> expr_t T_String.

(* Task 2: Implement the function erase which maps the typed expressions to their untyped corresponding expressions. *)
Fixpoint erase {t : type} (e : expr_t t) : expr := (* TODO *).


(* Task 3: Proof that a typed expression whose types have been erased is still typeable. *)
Lemma erased_expr_t_typechecks : forall (t : type) (e : expr_t t), typechecks (erase e) t.
Proof.
  admit.
Admitted.

(* Task 4: (Slightly advanced) Show that every typeable term is in the image of erase. *)
Lemma erase_surjective_over_tc : forall (t : type) (e : expr),
  typechecks e t ->
  exists (e' : expr_t t), erase e' = e.
Proof.
  admit.
Admitted.

