Require Import List.

Section slist.
  Variable T : Set.

  Inductive slist : Set :=
  | S_Nil : slist
  | S_Single : T -> slist
  | S_Concat : slist -> slist -> slist.

  Fixpoint flatten (ls : slist) : list T :=
    match ls with
    | S_Nil => nil
    | S_Single n => n :: nil
    | S_Concat l1 l2 => (flatten l1) ++ (flatten l2)
    end.

  Theorem flatten_distr : forall l1 l2,
    flatten (S_Concat l1 l2) = (flatten l1) ++ (flatten l2).
  Proof.
    intros. simpl. reflexivity.
  Qed.
End slist.
