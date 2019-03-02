Inductive nat_tree : Set :=
| Leaf : nat -> nat_tree
| Node : (nat -> nat_tree) -> nat_tree.

Fixpoint increment (nt : nat_tree) : nat_tree :=
  match nt with
  | Leaf n => Leaf (n + 1)
  | Node t => Node (fun i => increment (t i))
  end.

Fixpoint leapfrog (i : nat) (nt : nat_tree) : nat :=
  match nt with
  | Leaf n => n
  | Node t => leapfrog (i + 1) (t i)
  end.

Theorem leapfrog_increment : forall nt i,
  leapfrog i nt + 1 = leapfrog i (increment nt).
Proof.
  induction nt.
  - reflexivity.
  - simpl. intros. rewrite <- H. reflexivity.
Qed.
