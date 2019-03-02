Inductive even_nat : Set :=
| O : even_nat
| Se : odd_nat -> even_nat
with odd_nat : Set :=
| So : even_nat -> odd_nat.

Fixpoint sum_even (n1 n2 : even_nat) : even_nat :=
  match (n1, n2) with
  | (O, _) => n2
  | (_, O) => n1
  | (Se m1, Se m2) => Se (So (sum_odd m1 m2))
  end
with sum_odd (m1 m2 : odd_nat) : even_nat :=
  match (m1, m2) with
  | (So k1, So k2) => Se (So (sum_even k1 k2))
  end.

Scheme even_nat_mut := Induction for even_nat Sort Prop
  with odd_nat_mut  := Induction for odd_nat Sort Prop.

Theorem sum_even_comm : forall n m,
  sum_even n m = sum_even m n.
Proof.
  Check even_nat_mut.
  apply (even_nat_mut
    (fun n => forall m, sum_even n m = sum_even m n)
    (fun n => forall m, sum_odd n m = sum_odd m n)).
  - simpl. destruct m; reflexivity.
  - intros. simpl. destruct m; simpl.
    + reflexivity.
    + rewrite H. reflexivity.
  - intros. destruct m. simpl. rewrite H. reflexivity.
Qed.
