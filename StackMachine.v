Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* Arithmetic expressions and string expressions. *)

(* Arithmetic expressions which evaluate to natural numbers *)
Inductive aexpr : Type :=
  AE_Lit : forall (n : nat), aexpr
| AE_Add : aexpr -> aexpr -> aexpr
| AE_Mult : aexpr -> aexpr -> aexpr.

(* Task 1: Write a function which evaluates an aexpr to a natural number. *)
Fixpoint eval_aexpr (ae : aexpr) : nat. Admitted.

(* Expressions which evaluate to strings. *)
Inductive strexpr : Type :=
  SE_Lit : forall (s : string), strexpr
| SE_Append : strexpr -> strexpr -> strexpr
| SE_Repeat : aexpr -> strexpr -> strexpr.

(* Helper function: Repeat a string n times. *)
Fixpoint repeat_str (num : nat) (str : string) : string :=
  match num with
  | O => ""%string
  | S n' => String.append str (repeat_str n' str)
  end.

(* Task 2: Write a function which evaluates a strexpr to a string. *)
Fixpoint eval_strexpr (se : strexpr) : string. Admitted.

(* The Stack Machine *)

(* We formalize a model of a simple stack machine. The stack itself is a list of strings and nats.
   The following instructions for our stack machine are available:
   - Push_nat : Push a nat on the stack.
   - Push_string : Push a string on the stack.
   - Add  : Pop two nats from the stack, add them and push the result on the stack.
   - Mult : Pop two nats from the stack, multiply them and push the result on the stack.
   - Append : Pop two strings from the stack, append them and push the result on the stack.
   - Repeat : Pop a string and a nat from the stack, repeat the string n times and push
              the result on the stack.

  Note that the behaviour of the stack machine is undefined if the required operands of an
  operation cannot be popped from the stack.
 *)

Inductive instruction : Type :=
| Push_nat : forall (n : nat), instruction
| Push_string : forall (s : string), instruction
| Add : instruction
| Mult : instruction
| Append : instruction
| Repeat : instruction.

Definition stack : Type := list (nat + string).
Definition program : Type := list instruction.
Definition state : Type := stack * program.

(* Execute one instruction from the program *)
(* Task 3: Fill in the missing cases *)
Inductive execute_step : state -> state -> Prop :=
| exec_push_nat : forall (n : nat)(st : stack)(pr : program),
    execute_step (st, Push_nat n :: pr) (inl n :: st, pr)
| exec_add : forall (n m : nat) (st : stack) (pr : program),
    execute_step (inl n :: inl m :: st, Add :: pr) (inl (n + m) :: st, pr).

Example push_nat_example : execute_step ([], [Push_nat 3]) ([inl 3],[]).
Proof.
  apply exec_push_nat.
Qed.

(* Execute all the instructions from the program. This results with the state
   of the stack at the end of execution. *)
Inductive execute : state -> stack -> Prop :=
  execute_nop : forall (st : stack), execute (st, []) st
| execute_cons : forall (s s' : state) (st : stack),
    execute_step s s' ->
    execute s' st ->
    execute s st.

(* Task 4: Give a proof of the following example. *)
Example addition_example : execute ([], [Push_nat 2; Push_nat 4; Add]) [inl 6].
Proof.
  admit.
Admitted.

(* Compiling expressions into stack programs. *)

(* We now have expressions for nats and strings, a stack machine, and want to relate them by
   a compilation step. We want to be able to compile expressions into programs for our
   stack machine. *)

(* Task 5: Define the following two compilation functions. *)
Fixpoint compile_aexpr (ae : aexpr) : program. Admitted.

Fixpoint compile_strexpr (se : strexpr) : program. Admitted.

Definition example_prog : program :=
  (compile_strexpr (SE_Repeat (AE_Add (AE_Lit 1) (AE_Lit 1)) (SE_Append (SE_Lit "Hello ") (SE_Lit "World ")))).


(* Task 6: Define the tactic "execute_tac" which can solve the goal below.
   You should use "match goal" for this. Alternatively, you can solve this goal by hand. *)
Ltac execute_tac := idtac.

Lemma example_prog_execute : execute ([], example_prog) [inr "Hello World Hello World "%string].
Proof.
  unfold example_prog. simpl.
  repeat execute_tac.
  admit.
Admitted.

