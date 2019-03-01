Require Import List.
Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* Chapter 5. Infinite Data and Proofs *)
(* 5.1 Computing with Infinite Data *)

Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

CoFixpoint trues_falses : stream bool := Cons true falses_trues
  with falses_trues : stream bool := Cons false trues_falses.

Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
    | O => nil
    | S n' =>
      match s with
        | Cons h t => h :: approx t n'
      end
  end.

Eval simpl in approx zeroes 10.
Eval simpl in approx trues_falses 10.
(* CoFixpoint looper : stream nat := looper. *)

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
      | Cons h t => Cons (f h) (map t)
    end.

(*
  (* cannot define *)
  CoFixpoint filter (s : stream A) (p : A -> bool) : stream A :=
    match s with
    | Cons h t => match p h with
        | true  => Cons h (filter t p)
        | false => filter t p
        end
    end.
*)
End map.

Section interleave.
  Variable A : Type.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
      | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

Section map'.
  Variables A B : Type.
  Variable f : A -> B.
(*
  CoFixpoint map' (s : stream A) : stream B :=
    match s with
      | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))
    end.
*)
End map'.

Definition tl A (s : stream A) : stream A :=
  match s with
    | Cons _ s' => s'
  end.

(*
CoFixpoint bad : stream nat := tl (Cons 0 bad).
*)

(* 5.2 Infinite Proofs *)

CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map S zeroes.

Theorem ones_eq : ones = ones'.
Abort.

(* define equivalence relation *)
Section stream_eq.
  Variable A : Type.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
    stream_eq t1 t2
    -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Theorem ones_eq : stream_eq ones ones'.
  cofix ones_eq.
  assumption.
  (* Guarded. *)
  Undo.
  simpl.
Abort.

Definition frob A (s : stream A) : stream A :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem frob_eq : forall A (s : stream A), s = frob s.
  destruct s; reflexivity.
Qed.

(* Fixpoints only reduce when enough is known about the definitions of
   their arguments. Dually, co-fixpoints only reduce when enough is known about
   how their results will be used. *)
Theorem ones_eq : stream_eq ones ones'.
  cofix ones_eq.
  rewrite (frob_eq ones).
  rewrite (frob_eq ones').
  simpl.
  constructor.
  assumption.
Qed.

(* automation makes similar mistakes *)
Theorem ones_eq' : stream_eq ones ones'.
  cofix ones_eq; crush.
  (* Guarded. *)
Abort.

Definition hd A (s : stream A) : A :=
  match s with
    | Cons x _ => x
  end.

Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.

  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).

  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
    cofix. destruct s1. destruct s2. intro.
    generalize (Cons_case_hd H). intro Heq. simpl in Heq. rewrite Heq.
    constructor.
    apply stream_eq_coind.
    apply (Cons_case_tl H).
  Qed.
End stream_eq_coind.

Print stream_eq_coind.
(*
  stream_eq_coind = 
  fun (A : Type) (R : stream A -> stream A -> Prop)
    (Cons_case_hd : forall s1 s2 : stream A, R s1 s2 -> hd s1 = hd s2)
    (Cons_case_tl : forall s1 s2 : stream A, R s1 s2 -> R (tl s1) (tl s2)) =>
  cofix stream_eq_coind (s1 : stream A) :
    forall s2 : stream A, R s1 s2 -> stream_eq s1 s2 :=
    match s1 as s return (forall s2 : stream A, R s s2 -> stream_eq s s2) with
    | Cons a s2 =>
        fun s3 : stream A =>
        match s3 as s return (R (Cons a s2) s -> stream_eq (Cons a s2) s) with
        | Cons a0 s4 =>
            fun H : R (Cons a s2) (Cons a0 s4) =>
            (fun Heq : hd (Cons a s2) = hd (Cons a0 s4) =>
             eq_ind_r (fun a1 : A => stream_eq (Cons a1 s2) (Cons a0 s4))
               (Stream_eq a0
                  (stream_eq_coind s2 s4
                     (Cons_case_tl (Cons a s2) (Cons a0 s4) H))) Heq)
              (Cons_case_hd (Cons a s2) (Cons a0 s4) H)
        end
    end
       : forall (A : Type) (R : stream A -> stream A -> Prop),
         (forall s1 s2 : stream A, R s1 s2 -> hd s1 = hd s2) ->
         (forall s1 s2 : stream A, R s1 s2 -> R (tl s1) (tl s2)) ->
         forall s1 s2 : stream A, R s1 s2 -> stream_eq s1 s2
*)

Theorem ones_eq'' : stream_eq ones ones'.
  apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')); crush.
Qed.

(* Is there a way where we don't have to explicitly write the predicate ? *)
Section stream_eq_loop.
  Variable A : Type.
  Variables s1 s2 : stream A.

  Hypothesis Cons_case_hd : hd s1 = hd s2.
  Hypothesis loop1 : tl s1 = s1.
  Hypothesis loop2 : tl s2 = s2.

  Theorem stream_eq_loop : stream_eq s1 s2.
    apply (stream_eq_coind (fun s1' s2' => s1' = s1 /\ s2' = s2)); crush.
  Qed.
End stream_eq_loop.

Print stream_eq_loop.
(*
  forall (A : Type) (s1 s2 : stream A),
         hd s1 = hd s2 -> tl s1 = s1 -> tl s2 = s2 -> stream_eq s1 s2
*)

Theorem ones_eq''' : stream_eq ones ones'.
  apply stream_eq_loop; crush.
Qed.

(* ---------- *)
Require Import Arith.
Print fact.

CoFixpoint fact_slow' (n : nat) := Cons (fact n) (fact_slow' (S n)).
Definition fact_slow := fact_slow' 1.

(* use memoization in fact_slow *)
CoFixpoint fact_iter' (cur acc : nat) := Cons acc (fact_iter' (S cur) (acc * cur)).
Definition fact_iter := fact_iter' 2 1.

Eval simpl in approx fact_iter 5.
Eval simpl in approx fact_slow 5.
(** Now, to prove that the two versions are equivalent, it is helpful to prove (and add as a proof hint) a quick lemma about the computational behavior of [fact].  (I intentionally skip explaining its proof at this point.) *)

Lemma fact_def : forall x n,
  fact_iter' x (fact n * S n) = fact_iter' x (fact (S n)).
  simpl. intros. f_equal. ring.
Qed.

Hint Resolve fact_def.

Lemma fact_eq' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  intro.
  apply (stream_eq_coind
    (* still have to write the predicate... *)
    (fun s1 s2 => exists n, s1 = fact_iter' (S n) (fact n) /\ s2 = fact_slow' n)).
  - intros s1 s2 [n0 [H1 H2]]. subst. simpl. reflexivity.
  - intros s1 s2 [n0 [H1 H2]]. subst. exists (S n0). split; simpl.
    + rewrite <- mult_n_Sm. rewrite plus_comm. rewrite mult_comm. reflexivity.
    + reflexivity.
  - exists n. split; reflexivity.
Qed.

Theorem fact_eq : stream_eq fact_iter fact_slow.
  apply fact_eq'.
Qed.

Section stream_eq_onequant.
  Variables A B : Type.
  Variables f g : A -> stream B.
  Hypothesis Cons_case_hd : forall x, hd (f x) = hd (g x).
  Hypothesis Cons_case_tl : forall x, exists y, tl (f x) = f y /\ tl (g x) = g y.

  Theorem stream_eq_onequant : forall x, stream_eq (f x) (g x).
    intro.
    apply (stream_eq_coind (fun s1 s2 => exists x, s1 = f x /\ s2 = g x)).
    - intros s1 s2 [x0 [H1 H2]]; subst. apply Cons_case_hd.
    - intros s1 s2 [x0 [H1 H2]]; subst. apply Cons_case_tl.
    - exists x. split; reflexivity.
  Qed.
End stream_eq_onequant.

Print stream_eq_onequant.
(*
  forall (A B : Type) (f g : A -> stream B),
         (forall x : A, hd (f x) = hd (g x)) ->
         (forall x : A, exists y : A, tl (f x) = f y /\ tl (g x) = g y) ->
         forall x : A, stream_eq (f x) (g x)
*)

Lemma fact_eq'' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  apply stream_eq_onequant; intros.
  - simpl. reflexivity.
  - exists (S x). split.
    + simpl. rewrite <- mult_n_Sm. rewrite plus_comm. rewrite mult_comm.
      reflexivity.
    + simpl. reflexivity.
Qed.


(* 5.3 Simple Modeling of Non-Terminating Programs *)

Definition var := nat.
Definition vars := var -> nat.
(* set variable's value in a map *)
Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v'.

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (vs : vars) (e : exp) : nat :=
  match e with
    | Const n => n
    | Var v => vs v
    | Plus e1 e2 => evalExp vs e1 + evalExp vs e2
  end.

Inductive cmd : Set :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.

CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e,
  evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall vs1 vs2 vs3 c1 c2,
  evalCmd vs1 c1 vs2
  -> evalCmd vs2 c2 vs3
  -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c,
  evalExp vs e = 0
  -> evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c,
  evalExp vs1 e <> 0
  -> evalCmd vs1 c vs2
  -> evalCmd vs2 (While e c) vs3
  -> evalCmd vs1 (While e c) vs3.

Section evalCmd_coind.
  Variable R : vars -> cmd -> vars -> Prop.

  Hypothesis AssignCase : forall vs1 vs2 v e,
    R vs1 (Assign v e) vs2
    -> vs2 = set vs1 v (evalExp vs1 e).

  Hypothesis SeqCase : forall vs1 vs3 c1 c2,
    R vs1 (Seq c1 c2) vs3
    -> exists vs2, R vs1 c1 vs2 /\ R vs2 c2 vs3.

  Hypothesis WhileCase : forall vs1 vs3 e c,
    R vs1 (While e c) vs3
    -> (evalExp vs1 e = 0 /\ vs3 = vs1)
    \/ exists vs2, evalExp vs1 e <> 0 /\ R vs1 c vs2 /\ R vs2 (While e c) vs3.

  Theorem evalCmd_coind : forall vs1 c vs2, R vs1 c vs2 -> evalCmd vs1 c vs2.
    cofix. intros. destruct c.
    - (* Assign *)
      rewrite (AssignCase H); constructor.
    - (* Seq *)
      destruct (SeqCase H) as [? [? ?]]. apply EvalSeq with (vs2:=x); auto.
    - (* While *)
      destruct (WhileCase H) as [[? ?] | [? [? [? ?]]]]; subst.
      + apply EvalWhileFalse. assumption.
      + apply EvalWhileTrue with (vs2:=x).
          assumption.
          apply evalCmd_coind; assumption.
          apply evalCmd_coind; assumption.
Qed.
End evalCmd_coind.

Fixpoint optExp (e : exp) : exp :=
  match e with
    | Plus (Const 0) e => optExp e
    | Plus e1 e2 => Plus (optExp e1) (optExp e2)
    | _ => e
  end.

Fixpoint optCmd (c : cmd) : cmd :=
  match c with
    | Assign v e => Assign v (optExp e)
    | Seq c1 c2 => Seq (optCmd c1) (optCmd c2)
    | While e c => While (optExp e) (optCmd c)
  end.

Lemma optExp_correct : forall vs e, evalExp vs (optExp e) = evalExp vs e.
Proof.
  induction e; crush;
    repeat (match goal with
            | [ |- context[match ?E with Const _ => _ | _ => _ end] ] => destruct E
            | [ |- context[match ?E with O => _ | S _ => _ end] ] => destruct E
            end; crush).
Restart.
  intros. generalize dependent vs. induction e; simpl; try reflexivity.
  - (* Plus *)
    intros. destruct e1; simpl.
    + destruct n; simpl.
        apply IHe2.
        rewrite IHe2. reflexivity.
    + rewrite IHe2. reflexivity.
    + rewrite IHe1. simpl. rewrite IHe2. reflexivity.
Qed.

Hint Rewrite optExp_correct.

Ltac finisher := match goal with
                   | [ H : evalCmd _ _ _ |- _ ] => ((inversion H; [])
                     || (inversion H; [|])); subst
                 end; crush; eauto 10.

Print evalCmd_coind.
(*
  forall R : vars -> cmd -> vars -> Prop,
  (forall (vs1 vs2 : vars) (v : var) (e : exp),
   R vs1 (Assign v e) vs2 -> vs2 = set vs1 v (evalExp vs1 e)) ->
  (forall (vs1 vs3 : vars) (c1 c2 : cmd),
   R vs1 (Seq c1 c2) vs3 ->
   exists vs2 : vars, R vs1 c1 vs2 /\ R vs2 c2 vs3) ->
  (forall (vs1 vs3 : vars) (e : exp) (c : cmd),
   R vs1 (While e c) vs3 ->
   evalExp vs1 e = 0 /\ vs3 = vs1 \/
   (exists vs2 : vars,
      evalExp vs1 e <> 0 /\ R vs1 c vs2 /\ R vs2 (While e c) vs3)) ->
  forall (vs1 : vars) (c : cmd) (vs2 : vars),
  R vs1 c vs2 -> evalCmd vs1 c vs2
*)

Lemma optCmd_correct1 : forall vs1 c vs2,
  evalCmd vs1 c vs2 -> evalCmd vs1 (optCmd c) vs2.
Proof.
  intros.
  apply (evalCmd_coind (fun vs1 c' vs2 => exists c, evalCmd vs1 c vs2
    /\ c' = optCmd c)); eauto; crush;
    match goal with
      | [ H : _ = optCmd ?E |- _ ] => destruct E; simpl in *; discriminate
        || injection H; intros; subst
    end; finisher.
Restart.
  intros.
  apply (evalCmd_coind
    (* R: *)
    (fun vs1 c' vs2 => exists c, evalCmd vs1 c vs2 /\ c' = optCmd c)).
  - (* Assign *)
    intros vs3 vs4 v e [c0 [H1 H2]].
    destruct c0; inversion H2; subst.
    inversion H1; subst. rewrite optExp_correct. reflexivity.
  - (* Seq *)
    intros vs3 vs4 c1 c2 [c0 [H1 H2]].
    destruct c0; inversion H2; subst.
    inversion H1; subst. exists vs5. split.
    + exists c0_1. auto.
    + exists c0_2. auto.
  - (* While *)
    intros vs3 vs4 e c0 [c1 [H1 H2]].
    destruct c1; inversion H2; subst.
    rewrite optExp_correct.
    inversion H1; subst.
    + (* EvalWhileFalse *)
      left. split; auto.
    + (* EvalWhileTrue *)
      right. exists vs5. split; try assumption.
      split.
        exists c1; auto.
        exists (While e0 c1); auto.
  - exists c; auto.
Qed.

Lemma optCmd_correct2 : forall vs1 c vs2,
  evalCmd vs1 (optCmd c) vs2 -> evalCmd vs1 c vs2.
  intros; apply (evalCmd_coind (fun vs1 c vs2 => evalCmd vs1 (optCmd c) vs2));
    crush; finisher.
Restart.
  intros.
  apply (evalCmd_coind (fun vs1 c vs2 => evalCmd vs1 (optCmd c) vs2)).
  - (* Assign *)
    simpl. intros vs3 vs4 v e H0. inversion H0; subst.
    rewrite optExp_correct. reflexivity.
  - (* Seq *)
    simpl. intros vs3 vs4 c1 c2 H0. inversion H0; subst.
    exists vs5. auto.
  - (* While *)
    simpl. intros vs3 vs4 e c0 H0. inversion H0; subst.
    + (* EvalWhileFalse *)
      left. rewrite optExp_correct in H5. auto.
    + (* EvalWhileTrue *)
      right. rewrite optExp_correct in H3. exists vs5. auto.
  - assumption.
Qed.

Theorem optCmd_correct : forall vs1 c vs2,
  evalCmd vs1 (optCmd c) vs2 <-> evalCmd vs1 c vs2.
  intuition; apply optCmd_correct1 || apply optCmd_correct2; assumption.
Qed.
