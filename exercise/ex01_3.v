Require Import Coq.Arith.Arith.

Inductive binop : Set :=
| Plus  : binop
| Times : binop.

Definition var := nat.
Definition vars := var -> nat.
Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v'.
Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenote (vs : vars) (e : exp) : nat :=
  match e with
  | Const n => n
  | Var v => vs v
  | Binop b e1 e2 => (binopDenote b) (expDenote vs e1) (expDenote vs e2)
  end.

Fixpoint fold (vs : vars) (e : exp) : exp :=
  match e with
  | Const _ => e
  | Var v => Const (vs v)
  | Binop b e1 e2 => (match (fold vs e1, fold vs e2) with
    | (Const n1, Const n2) => Const ((binopDenote b) n1 n2)
    | (e1', e2') => Binop b e1' e2'
    end)
  end.

Theorem fold_correct : forall vs e,
  expDenote vs e = expDenote vs (fold vs e).
Proof.
  (* intros vs e. generalize dependent vs. *)
  induction e; try reflexivity.
  - (* Binop *)
  intros. simpl. rewrite IHe1. rewrite IHe2.
  destruct (fold vs e1); try reflexivity.
  destruct (fold vs e2); try reflexivity.
Qed.
