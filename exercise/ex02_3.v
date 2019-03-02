Require Import Plus.

Inductive foo6 : nat -> Prop :=
| O6 : foo6 6
| S6 : forall m, foo6 m -> foo6 (6 + m).

Inductive foo10 : nat -> Prop :=
| O10 : foo10 10
| S10 : forall m, foo10 m -> foo10 (10 + m).

Inductive foo : nat -> Prop :=
| Six : forall n, foo6 n -> foo n
| Ten : forall n, foo10 n -> foo n.

Example thirteen_not_foo :
  ~ (foo 13).
Proof.
  intros H. inversion H; subst.
  - inversion H0; subst. inversion H2; subst. inversion H3.
  - inversion H0; subst. inversion H2.
Qed.

Inductive odd : nat -> Prop :=
| SO : odd 1
| SSo : forall m, odd m -> odd (S (S m)).

(* dirty... *)
Theorem foo_not_odd : forall n,
  foo n -> ~ (odd n).
Proof.
  intros n H H0. inversion H; subst; clear H.
  - induction H1; subst.
    + inversion H0; subst; clear H0.
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      inversion H1.
    + apply IHfoo6.
      inversion H0; subst; clear H0.
      inversion H2; subst; clear H2.
      inversion H0; subst; clear H0.
      assumption.
  - induction H1; subst.
    + inversion H0; subst; clear H0.
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      inversion H1.
    + apply IHfoo10.
      inversion H0; subst; clear H0.
      inversion H2; subst; clear H2.
      inversion H0; subst; clear H0.
      inversion H2; subst; clear H2.
      inversion H0; subst; clear H0.
      assumption.
Qed.
