Set Implicit Arguments.
Require Import Arith.

Section btree.
  Variable T : Set.

  Inductive btree : Set :=
  | BLeaf : T -> btree
  | BNode : btree -> btree -> btree.
End btree.

Section map.
  Variables T S : Set.
  Variable f : T -> S.

  Fixpoint map (bt : btree T) : btree S :=
    match bt with
    | BLeaf t => BLeaf (f t)
    | BNode t1 t2 => BNode (map t1) (map t2)
    end.
End map.

Inductive trexp : Set :=
| Leaf : nat -> trexp
| Tree : btree trexp -> trexp.

Fixpoint count (t : btree nat) : nat :=
  match t with
  | BLeaf n => n
  | BNode t1 t2 => (count t1) + (count t2)
  end.

Fixpoint total (t : trexp) : nat :=
  match t with
  | Leaf n => n
  | Tree bt => count (map total bt)
  end.

Fixpoint increment (t : trexp) : trexp :=
  match t with
  | Leaf n => Leaf (n + 1)
  | Tree bt => Tree (map increment bt)
  end.

Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (ls : btree T) : Prop :=
    match ls with
      | BLeaf n => P n
      | BNode t1 t2 => (All t1) /\ (All t2)
    end.
End All.

Section trexp_ind'.
  Variable P : trexp -> Prop.

  Hypothesis Leaf_case : forall n, P (Leaf n).
  Hypothesis Tree_case : forall (bt : btree trexp),
    All P bt -> P (Tree bt).

  Fixpoint trexp_ind' (tr : trexp) : P tr :=
    match tr with
    | Leaf n => Leaf_case n
    | Tree bt => Tree_case bt
        ((fix btree_trexp_ind (bt : btree trexp) : All P bt :=
         match bt with
         | BLeaf t => trexp_ind' t (* <- nested recursion *)
         | BNode t1 t2 => conj (btree_trexp_ind t1) (btree_trexp_ind t2)
         end) bt)
    end.
End trexp_ind'.

Theorem increment_ge : forall t,
  total (increment t) >= total t.
Proof.
  unfold ge. intros.
  apply (trexp_ind' (fun t => total t <= total (increment t))); simpl.
  - intros. rewrite plus_comm. simpl. apply le_n_Sn.
  - induction bt; simpl.
    + trivial.
    + intros [H1 H2]. apply plus_le_compat; auto.
Qed.
