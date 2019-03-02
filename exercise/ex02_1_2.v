(* 1 *)
Example a :
  (True \/ False) /\ (False \/ True).
Proof.
  split.
  - left. apply I.
  - right. apply I.
Qed.

Example b : forall P : Prop,
  P -> not (not P).
Proof.
  intros P H H0. apply H0. apply H.
Qed.

Example c : forall P Q R : Prop,
  P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R [H1 H2]. destruct H2.
  - left. split; assumption.
  - right. split; assumption.
Qed.

(* 2 *)
Example a : forall (T : Type) p x q f,
  p x ->
  (forall x : T, p x -> exists y, q x y) ->
  (forall x y, q x y -> q y (f y)) ->
  exists z, q z (f z).
Proof.
  intros. apply H in X. destruct X as [y X].
  apply H0 in X.
  exists y. apply X.
Qed.
