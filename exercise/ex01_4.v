Inductive binop : Set :=
| Plus : binop
| Mult : binop.

Definition var := nat.
Definition nvars := nat -> nat.
Definition bvars := nat -> bool.

Inductive bool_exp : Set :=
| BConst : bool -> bool_exp
| BVar : var -> bool_exp.

Inductive nat_exp : Set :=
| NConst : nat -> nat_exp
| NVar : var -> nat_exp
| Binop : binop -> nat_exp -> nat_exp -> nat_exp
| If : bool_exp -> nat_exp -> nat_exp -> nat_exp.

Inductive exp : Set :=
| B : bool_exp -> exp
| N : nat_exp -> exp.

Inductive imm : Set :=
| Bi : bool -> imm
| Ni : nat -> imm.

Definition binopDenote (b : binop) :=
  match b with
  | Plus => plus
  | Mult => mult
  end.

Fixpoint bexpDenote (nv : nvars) (bv : bvars) (e : bool_exp) :=
  match e with
  | BConst b => b
  | BVar v => bv v
  end.

Fixpoint nexpDenote (nv : nvars) (bv : bvars) (e : nat_exp) :=
  match e with
  | NConst n => n
  | NVar v => nv v
  | Binop b e1 e2 => (binopDenote b) (nexpDenote nv bv e1) (nexpDenote nv bv e2)
  | If b e1 e2 =>
    if bexpDenote nv bv b then nexpDenote nv bv e1 else nexpDenote nv bv e2
  end.

Fixpoint expDenote nv bv (e : exp) :=
  match e with
  | B e' => Bi (bexpDenote nv bv e')
  | N e' => Ni (nexpDenote nv bv e')
  end.

Fixpoint bfold (nv : nvars) (bv : bvars) (e : bool_exp) :=
  match e with
  | BConst _ => e
  | BVar v => BConst (bv v)
  end.

Fixpoint nfold (nv : nvars) (bv : bvars) (e : nat_exp) :=
  match e with
  | NConst _ => e
  | NVar v => NConst (nv v)
  | Binop b e1 e2 => match (nfold nv bv e1, nfold nv bv e2) with
    | (NConst n1, NConst n2) => NConst ((binopDenote b) n1 n2)
    | (e1', e2') => Binop b e1' e2'
    end
  | If b e1 e2 => match bfold nv bv b with
    | BConst true  => nfold nv bv e1
    | BConst false => nfold nv bv e2
    | b' => If b' (nfold nv bv e1) (nfold nv bv e2)
    end
  end.

Fixpoint fold (nv : nvars) (bv : bvars) (e : exp) :=
  match e with
  | B e => B (bfold nv bv e)
  | N e => N (nfold nv bv e)
  end.

Theorem bfold_correct : forall nv bv e,
  bexpDenote nv bv e = bexpDenote nv bv (bfold nv bv e).
Proof.
  destruct e; reflexivity.
Qed.

Theorem nfold_correct : forall nv bv e,
  nexpDenote nv bv e = nexpDenote nv bv (nfold nv bv e).
Proof.
  induction e; try reflexivity.
  - (* Binop *)
    inversion IHe1. inversion IHe2. clear IHe1 IHe2.
    simpl. rewrite H0. rewrite H1.
    destruct (nfold nv bv e1); try reflexivity.
    destruct (nfold nv bv e2); try reflexivity.
  - (* If *)
    inversion IHe1. inversion IHe2. clear IHe1 IHe2.
    simpl. rewrite H0. rewrite H1.
    destruct (bfold nv bv b) eqn:H2.
    { (* BConst *)
      assert (bexpDenote nv bv b = b0). {
        rewrite bfold_correct. rewrite H2. reflexivity. }
      rewrite H. destruct b0; reflexivity. }
    { (* BVar *)
      simpl. rewrite bfold_correct. rewrite H2. reflexivity. }
Qed.

Theorem fold_correct : forall nv bv e,
  expDenote nv bv e = expDenote nv bv (fold nv bv e).
Proof.
  destruct e; simpl.
  - rewrite <- bfold_correct. reflexivity.
  - rewrite <- nfold_correct. reflexivity.
Qed.
