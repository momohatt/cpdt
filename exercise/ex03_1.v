Set Implicit Arguments.
Require Import Bool.

Section inftree.
  Variable T : Set.

  CoInductive inftree : Set :=
  | INode : T -> inftree -> inftree -> inftree.

  CoFixpoint everywhere (v : T) : inftree :=
    INode v (everywhere v) (everywhere v).
End inftree.

Section map.
  Variables T S U : Set.
  Variable f : T -> S -> U.

  CoFixpoint map (t1 : inftree T) (t2 : inftree S) :=
    match (t1, t2) with
    | (INode v1 t1' t2', INode v2 s1' s2') =>
        INode (f v1 v2) (map t1' s1') (map t2' s2')
    end.
End map.

Definition falses := everywhere false.

CoFixpoint true_falses : inftree bool :=
  INode true false_trues false_trues
  with false_trues : inftree bool :=
  INode false true_falses true_falses.

Section inftree_eq.
  Variable T : Set.

  CoInductive inftree_eq : inftree T -> inftree T -> Prop :=
  | Eq :
      forall v t1 t2 s1 s2,
      inftree_eq t1 s1 ->
      inftree_eq t2 s2 ->
      inftree_eq (INode v t1 t2) (INode v s1 s2).
End inftree_eq.

Definition val T (t : inftree T) : T :=
  match t with
  | INode v _ _ => v
  end.

Definition right T (t : inftree T) : inftree T :=
  match t with
  | INode _ t1 _ => t1
  end.

Definition left T (t : inftree T) : inftree T :=
  match t with
  | INode _ _ t2 => t2
  end.

Section inftree_eq_coind.
  Variable A : Set.
  Variable R : inftree A -> inftree A -> Prop.

  Hypothesis INode_case_val : forall t1 t2,
    R t1 t2 -> (val t1) = (val t2).
  Hypothesis INode_case_right : forall t1 t2,
    R t1 t2 -> R (right t1) (right t2).
  Hypothesis INode_case_left : forall t1 t2,
    R t1 t2 -> R (left t1) (left t2).

  Theorem inftree_eq_coind : forall t1 t2,
    R t1 t2 -> inftree_eq t1 t2.
  Proof.
    cofix. intros. destruct t1. destruct t2.
    assert (a = a0). {
      apply INode_case_val in H. simpl in H. apply H. }
    subst. apply Eq.
    - apply inftree_eq_coind.
      apply INode_case_right in H. simpl in H. apply H.
    - apply inftree_eq_coind.
      apply INode_case_left in H. simpl in H. apply H.
  Qed.
End inftree_eq_coind.

Theorem map_orb_equal :
  inftree_eq (map orb falses true_falses) true_falses.
Proof.
  apply (inftree_eq_coind
    (fun t1 t2 =>
      (t1 = map orb falses true_falses /\ t2 = true_falses) \/
      (t1 = map orb falses false_trues /\ t2 = false_trues))).
  - intros. destruct H; (destruct H; subst; reflexivity).
  - intros. destruct H; (destruct H; subst).
    + right. split; reflexivity.
    + left. split; reflexivity.
  - intros. destruct H; (destruct H; subst).
    + right. split; reflexivity.
    + left. split; reflexivity.
  - left. split; reflexivity.
Qed.
