Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Theorem discriminate : forall nt1 n nt2,
  NLeaf <> NNode nt1 n nt2.
Proof.
  intros. intros H. inversion H.
Qed.

Theorem injectivity : forall nt1 nt2 nt3 nt4 n m,
  NNode nt1 n nt2 = NNode nt3 m nt4 -> n = m.
Proof.
  intros. inversion H. reflexivity.
Qed.
