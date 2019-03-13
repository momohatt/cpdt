Require Import Arith List Omega.
Require Import Cpdt.CpdtTactics Cpdt.Coinductive.
Require Coq.extraction.Extraction.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* Chapter 7. General Recursion *)

(* 7.1 Well-Founded Recursion *)

(*
(mathematical concept)         (Coq technique)
well-founded relation  ---  well-founded recursion
*)

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
      | nil => x :: nil
      | h :: ls' =>
          if le x h
          then x :: ls
          else h :: insert x ls'
    end.

  (* (less efficiently) merge two sorted list *)
  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
      | nil => ls2
      | h :: ls' => insert h (merge ls' ls2)
    end.

  (* split a list arbitrarily into two pieces of approximately equal length. *)
  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
      | nil => (nil, nil)
      | h :: nil => (h :: nil, nil)
      | h1 :: h2 :: ls' =>
          let (ls1, ls2) := split ls' in
          (h1 :: ls1, h2 :: ls2)
    end.

  (*
  (* rejected!! *)
  Fixpoint mergeSort (ls : list A) : list A :=
    if leb (length ls) 1
      then ls
      else let lss := split ls in
      merge (mergeSort (fst lss)) (mergeSort (snd lss)).
  *)

  (* how well-foundedness is formalized in the Coq STL *)
  Print well_founded.
  (*
    well_founded =
    fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
         : forall A : Type, (A -> A -> Prop) -> Prop
  *)
  Print Acc. (* accessibility relation *)
  (*
    Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
        Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x
  *)
  (* an element [x] is accessible for a relation [R] if every element
     "less than" [x] according to [R] is also accessible *)

  (* [Acc] is defined inductively
     => any accessibility proof involves a finite chain of invocations *)

  CoInductive infiniteDecreasingChain A (R : A -> A -> Prop) : stream A -> Prop :=
  | ChainCons : forall x y s,
      infiniteDecreasingChain R (Cons y s) ->
      R y x ->
      infiniteDecreasingChain R (Cons x (Cons y s)).

  (* any accessible element cannot be the beginning of
     any infinite decreasing chain *)
  Lemma noBadChains' : forall A (R : A -> A -> Prop) x,
    Acc R x ->
    forall s, ~infiniteDecreasingChain R (Cons x s).
  Proof.
    induction 1. crush.
      match goal with
        | [ H : infiniteDecreasingChain _ _ |- _ ] => inversion H; eauto
      end.
  Restart.
    intros A0 R x H. induction H.
    - intros s H1. inversion H1; subst. apply (H0 y H5 s0 H4).
  Qed.

  (* the absence of infinite decreasing chains in well-founded sets *)
  Theorem noBadChains : forall A (R : A -> A -> Prop),
    well_founded R -> forall s, ~infiniteDecreasingChain R s.
  Proof.
    destruct s; apply noBadChains'; auto.
  Qed.

  (* Absence of infinite decreasing chains implies absence of infinitely nested
     recursive calls (for any recursive definition that respects
     the well-founded relation) *)
  Check Fix.
  (*
    Fix
         : forall (A : Type) (R : A -> A -> Prop),
           well_founded R ->
           (* P : possibly dependent range type of the function we build *)
           forall P : A -> Type,
           (* encoding of the function body *)
           (* x stands for the function argument *)
           (* "forall y : A, R y x -> P y" stands for the function we're defining *)
           (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
           forall x : A, P x
  *)

  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  Hint Constructors Acc.

  Lemma lengthOrder_wf' : forall len, forall ls,
    length ls <= len -> Acc lengthOrder ls.
  Proof.
    unfold lengthOrder; induction len; crush.
  (*
  Restart.
    unfold lengthOrder. induction len; intros.
    - inversion H. apply Acc_intro. intros. rewrite H1 in H0. inversion H0.
    - inversion H.
      + apply Acc_intro. intros. apply IHlen. rewrite H1 in H0.
        apply lt_n_Sm_le in H0. assumption.
      + apply IHlen. assumption.
  *)
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
  Proof.
    unfold well_founded. intro a.
    apply lengthOrder_wf' with (len:= length a). auto.
  Defined. (* <- to make the proof transparent *)

  (* [split] respects the [lengthOrder] relation *)
  Lemma split_wf : forall len ls,
    2 <= length ls <= len ->
    let (ls1, ls2) := split ls in
    lengthOrder ls1 ls /\ lengthOrder ls2 ls.
  Proof.
    unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
      destruct (le_lt_dec 2 (length ls));
        repeat (match goal with
                  | [ _ : length ?E < 2 |- _ ] => destruct E
                  | [ _ : S (length ?E) < 2 |- _ ] => destruct E
                  | [ IH : _ |- context[split ?L] ] =>
                    specialize (IH L); destruct (split L); destruct IH
                end; crush).
  Restart.
    unfold lengthOrder. induction len.
    - (* len = 0 *) destruct ls.
      + (* ls = nil *) simpl. intros. destruct H. inversion H.
      + intros.  simpl in H. destruct H. inversion H0.
    - (* len = n -> len = S n *) destruct ls.
      + (* ls = nil *) simpl. intros. destruct H. inversion H.
      + destruct ls.
        { (* ls = [a] *) simpl. intros. destruct H. inversion H. inversion H2. }
        { (* length ls >= 2 *)
          simpl. intros. destruct ls.
          - simpl. split; auto.
          - destruct ls.
            + simpl. split; auto.
            + remember (a1 :: a2 :: ls) as ls'. specialize (IHlen ls').
              destruct (split ls'). simpl.
              assert (2 <= length ls' <= len). {
                destruct H. split.
                - rewrite Heqls'. simpl. apply le_n_S. apply le_n_S.
                  assert (len_pos: forall (T : Type) (l : list T), 0 <= length l). {
                    induction l1; simpl. auto.
                    eapply le_trans; auto. }
                  apply len_pos.
                - inversion H0. auto.
                  apply le_trans with (m:=S (S (length ls'))); auto. }
              apply IHlen in H0. destruct H0. split.
              { apply lt_n_S. apply lt_trans with (m:=length ls'); auto. }
              { apply lt_n_S. apply lt_trans with (m:=length ls'); auto. }
        }
  Defined.

  Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
    destruct (split ls); destruct 1; crush.

  Lemma split_wf1 : forall ls, 2 <= length ls
    -> lengthOrder (fst (split ls)) ls.
    split_wf.
  Defined.

  Lemma split_wf2 : forall ls, 2 <= length ls
    -> lengthOrder (snd (split ls)) ls.
    split_wf.
  Defined.

  Hint Resolve split_wf1 split_wf2.

  Definition mergeSort : list A -> list A.
    refine (Fix lengthOrder_wf (fun _ => list A)
      (fun (ls : list A)
        (mergeSort : forall ls' : list A, lengthOrder ls' ls -> list A) =>
        if le_lt_dec 2 (length ls)
        then let lss := split ls in
            merge (mergeSort (fst lss) _) (mergeSort (snd lss) _)
        else ls)); subst lss; eauto.
  Defined.
End mergeSort.

Eval compute in mergeSort leb (1 :: 2 :: 36 :: 8 :: 19 :: nil).

(* prove that mergeSort does expected behavior *)
Theorem mergeSort_eq : forall A (le : A -> A -> bool) ls,
  mergeSort le ls =
    if le_lt_dec 2 (length ls)
    then let lss := split ls in
      merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
    else ls.
Proof.
  intros. apply (Fix_eq (@lengthOrder_wf A) (fun _ => list A)). intros.

  (* The library theorem [Fix_eq] imposes one more strange subgoal upon us.
     We must prove that the function body is unable to distinguish between
     "self" arguments that map equal inputs to equal outputs. One might think
     this should be true of any Gallina code, but in fact this general
     _function extensionality_ property is neither provable nor disprovable
     within Coq. The type of [Fix_eq] makes clear what we must show manually: *)
  Check Fix_eq.
  (*
  Fix_eq
       : forall (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R)
           (P : A -> Type)
           (F : forall x : A, (forall y : A, R y x -> P y) -> P x),
         (forall (x : A) (f g : forall y : A, R y x -> P y),
          (forall (y : A) (p : R y x), f y p = g y p) -> F x f = F x g) ->
         forall x : A,
         Fix Rwf P F x = F x (fun (y : A) (_ : R y x) => Fix Rwf P F y)
  *)

  match goal with
    | [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
  end; simpl; f_equal; auto.
  (* https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.f-equal *)
Restart.
  intros. apply (Fix_eq (@lengthOrder_wf A) (fun _ => list A)). intros.
  destruct (le_lt_dec 2 (length x)); try auto.
  simpl. f_equal; auto.
Qed.

Extract Inductive sumbool => "bool" ["true" "false"].
(* Extract Constant le_lt_dec "'a" "'b" => "'a <= 'b". *)
Extraction mergeSort.

(* corresponding induction rule *)
Check well_founded_induction.
(*
well_founded_induction
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Set,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       forall a : A, P a
*)


(* 7.2 A Non-Termination Monad Inspired by Domain Theory *)

(*
idea of approximation ordering on computation results (borrowed from domain theory)
ex)
* "the program does not terminate" is an approximation of
  "the program termintates with the answer 5"
* "the program terminates with the answer 5" is _not_ an approximation of
  "the program terminates with the answer 6"
*)

Section computation.
  Variable A : Type. (* result of a comptation, if it terminates *)

  Definition computation :=
    {f : nat (* approximation level *) -> option A
      | forall (n : nat) (v : A),
          f n = Some v
          -> forall (n' : nat), n' >= n
          -> f n' = Some v}.
  (*
    1. a call to [f] may return [None] to indicate that [n] was not high enough
       to run the computation to completion
    2. [f] is _monotone_ in an appropriate sense
  *)

  (* terminate at level n & result is v *)
  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.

  (* terminate & result is v *)
  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.
End computation.

(* some helpful tactics and lemmas (not explained) *)
Hint Unfold runTo.

Ltac run' := unfold run, runTo in *; try red; crush;
  repeat (match goal with
            | [ _ : proj1_sig ?E _ = _ |- _ ] =>
              match goal with
                | [ x : _ |- _ ] =>
                  match x with
                    | E => destruct E
                  end
              end
            | [ |- context[match ?M with exist _ _ => _ end] ] =>
              let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; try subst
            | [ _ : context[match ?M with exist _ _ => _ end] |- _ ] =>
              let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; subst
            | [ H : forall n v, ?E n = Some v -> _,
                _ : context[match ?E ?N with Some _ => _ | None => _ end] |- _ ] =>
              specialize (H N); destruct (E N);
              try rewrite (H _ (eq_refl _)) by auto; try discriminate
            | [ H : forall n v, ?E n = Some v -> _, H' : ?E _ = Some _ |- _ ] =>
              rewrite (H _ _ H') by auto
          end; simpl in *); eauto 7.

Ltac run := run';
  repeat (match goal with
  | [ H : forall n v, ?E n = Some v -> _
  |- context[match ?E ?N with Some _ => _ | None => _ end] ] =>
  specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto;
  try discriminate
  end; run').

Lemma ex_irrelevant : forall P : Prop, P -> exists n : nat, P.
exists 0; auto.
Qed.

Hint Resolve ex_irrelevant.

Require Import Max.

Theorem max_spec_le : forall n m, n <= m /\ max n m = m \/ m <= n /\ max n m = n.
  induction n; destruct m; simpl; intuition;
    specialize (IHn m); intuition.
Qed.

Ltac max := intros n m; generalize (max_spec_le n m); crush.

Lemma max_1 : forall n m, max n m >= n.
  max.
Qed.

Lemma max_2 : forall n m, max n m >= m.
  max.
Qed.

Hint Resolve max_1 max_2.

Lemma ge_refl : forall n, n >= n.
  crush.
Qed.

Hint Resolve ge_refl.

Hint Extern 1 => match goal with
                   | [ H : _ = exist _ _ _ |- _ ] => rewrite H
                 end.

(* infinite loop (doesn't terminate for any approximation level) *)
Section Bottom.
  Variable A : Type.

  Definition Bottom : computation A.
    (* use abstract to create a new opaque lemma for the proof
       found by the run tactic *)
    exists (fun _ : nat => @None A); abstract run.
  Defined.

  Theorem run_Bottom : forall v, ~run Bottom v.
    run.
  Restart.
    intros v contra. destruct contra as [n contra]. inversion contra.
  Qed.
End Bottom.

(* always terminate (at every approximation level) *)
Section Return.
  Variable A : Type.
  Variable v : A.

  Definition Return : computation A.
    intros; exists (fun _ : nat => Some v); abstract run.
  Defined.

  Theorem run_Return : run Return v.
    run.
  Restart.
    unfold run. exists 0. unfold runTo. reflexivity.
  Qed.
End Return.

Section Bind.
  Variables A B : Type.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.

  Definition Bind : computation B.
    exists (fun n =>
      let (f1, _) := m1 in
      match f1 n with
      | None => None
      | Some v =>
          let (f2, _) := m2 v in
          f2 n
      end); abstract run.
  Defined.

  Theorem run_Bind : forall (v1 : A) (v2 : B),
    run m1 v1
    -> run (m2 v1) v2
    -> run Bind v2.
  Proof.
    run; match goal with
           | [ x : nat, y : nat |- _ ] => exists (max x y)
         end; run.
  Qed.
End Bind.

Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

Definition meq A (m1 m2 : computation A) :=
  forall n, proj1_sig m1 n = proj1_sig m2 n.

(*
  monad law
  1. left identity  (return x >>= f  [is]  f x)
  2. right identity (m >>= return  [is]  m)
  3. associativity  ((m >>= f) >>= g  [is] m >>= (\x -> f x >>= g))
*)
Theorem left_identity : forall A B (a : A) (f : A -> computation B),
  meq (Bind (Return a) f) (f a).
  run.
Qed.

Theorem right_identity : forall A (m : computation A),
  meq (Bind m (@Return _)) m.
  run.
Qed.

Theorem associativity : forall A B C (m : computation A)
  (f : A -> computation B) (g : B -> computation C),
  meq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g)).
  run.
Qed.

Section lattice.
  Variable A : Type.

  (* terminates with the same value, or x doesn't terminate *)
  Definition leq (x y : option A) :=
    forall v, x = Some v -> y = Some v.
End lattice.

(* a new [Fix] combinator that does not require a termination proof,
   and in fact admits recursive definition of functions that fail to terminate
   on some or all inputs. *)
Section Fix.
  (* function domain and range types *)
  Variables A B : Type.

  (* function body, which is written as though it can be parameterized over itself,
     for recursive calls. *)
  Variable f : (A -> computation B) -> (A -> computation B).

  (* when [f] terminates according to one recursive version of itself,
     it also terminates with the same result at the same approximation level
     when passed a recursive version that refines the original, according to leq *)
  (*
     n : nat (approximation level)
     v1, v2 : A -> computation B
     v : A (result of computation)
  *)
  Hypothesis f_continuous : forall n v v1 x,
    runTo (f v1 x) n v ->
    forall (v2 : A -> computation B),
      (* proj1_sig (v1 x) : takes one element from a sig of type computation B *)
      (forall x, leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n)) ->
    runTo (f v2 x) n v.

  (* The computational part of the [Fix] combinator.
     At approximation level 0, we diverge; at higher levels,
     we run the body with a functional argument drawn from the next lower level *)
  Fixpoint Fix' (n : nat) (x : A) : computation B :=
    match n with
      | O => Bottom _
      | S n' => f (Fix' n') x
    end.

  Hint Extern 1 (_ >= _) => omega.
  Hint Unfold leq.

  Lemma Fix'_ok : forall steps n x v,
    proj1_sig (Fix' n x) steps = Some v ->
    forall n', n' >= n ->
    proj1_sig (Fix' n' x) steps = Some v.
  Proof.
    unfold runTo in *; induction n; crush;
      match goal with
        | [ H : _ >= _ |- _ ] => inversion H; crush; eauto
      end.
  Restart.
    unfold runTo in *. induction n.
    - crush.
    - simpl. intros. inversion H0.
      + simpl. assumption.
      + simpl. eapply f_continuous.
        apply H.
        unfold leq. intros. apply IHn. assumption.
        apply le_trans with (S n); auto.
  Qed.

  Hint Resolve Fix'_ok.

  Hint Extern 1 (proj1_sig _ _ = _) => simpl;
    match goal with
      | [ |- proj1_sig ?E _ = _ ] => eapply (proj2_sig E)
    end.

  Definition Fix : A -> computation B.
    intro x; exists (fun n => proj1_sig (Fix' n x) n); abstract run.
  Defined.

  Theorem run_Fix : forall x v,
    run (f Fix x) v -> run (Fix x) v.
  Proof.
    run. match goal with
           | [ n : nat |- _ ] => exists (S n); eauto
         end.
  Qed.
End Fix.

Lemma leq_Some : forall A (x y : A),
  leq (Some x) (Some y) -> x = y.
  intros ? ? ? H; generalize (H _ (eq_refl _)); crush.
Qed.

Lemma leq_None : forall A (x y : A),
  leq (Some x) None -> False.
  intros ? ? ? H; generalize (H _ (eq_refl _)); crush.
Qed.

Ltac mergeSort' := run;
  repeat (match goal with
            | [ |- context[match ?E with O => _ | S _ => _ end] ] => destruct E
          end; run);
  repeat match goal with
           | [ H : forall x, leq (proj1_sig (?f x) _) (proj1_sig (?g x) _) |- _ ] =>
             match goal with
               | [ H1 : f ?arg = _, H2 : g ?arg = _ |- _ ] =>
                 generalize (H arg); rewrite H1; rewrite H2;
                 clear H1 H2; simpl; intro
             end
         end; run;
         repeat match goal with
                  | [ H : _ |- _ ] =>
                      (apply leq_None in H; tauto) || (apply leq_Some in H; subst)
                end; auto.

Definition mergeSort' : forall A,
  (A -> A -> bool) -> list A -> computation (list A).
  refine (fun A le => Fix
    (fun (mergeSort : list A -> computation (list A))
      (ls : list A) =>
      if le_lt_dec 2 (length ls)
      then let lss := split ls in
          ls1 <- mergeSort (fst lss);
          ls2 <- mergeSort (snd lss);
          Return (merge le ls1 ls2)
      else Return ls) _); abstract mergeSort'.
Defined.

Lemma test_mergeSort' : run (mergeSort' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil))
  (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  exists 4; reflexivity.
Qed.

(* we can now write recursive functions that sometimes fail to terminate,
   without losing easy reasoning principles for the terminating cases *)
Ltac looper := unfold leq in *; run;
  repeat match goal with
           | [ x : unit |- _ ] => destruct x
           | [ x : bool |- _ ] => destruct x
         end; auto.

Definition looper : bool -> computation unit.
  refine (Fix (fun looper (b : bool) =>
    if b then Return tt else looper b) _); abstract looper.
Defined.

Lemma test_looper : run (looper true) tt.
  exists 1; reflexivity.
Qed.


(* 7.3 Co-Inductive Non-Termination Monads *)

(* we can leverage that co-induction support for encoding of general recursive definitions, by adding layers of co-inductive syntax *)

(* computations that may be forced to yield results, if they terminate *)
CoInductive thunk (A : Type) : Type :=
| Answer : A -> thunk A
| Think : thunk A -> thunk A.
(*
  terminating computation     : Think (Think ... (Think (Answer a)) ... )
  non-terminating computation : Think (Think ...
*)

(* "bind" operation *)
CoFixpoint TBind A B (m1 : thunk A) (m2 : A -> thunk B) : thunk B :=
  match m1 with
    | Answer x => m2 x
    | Think m1' => Think (TBind m1' m2)
  end.
(* the definition would violate the co-recursion guardedness restriction
   if we left out [Think] on the righthand side of the second [match] branch. *)

(* proof that [Answer] and [TBind] form a monad for [thunk] (???) *)
CoInductive thunk_eq A : thunk A -> thunk A -> Prop :=
| EqAnswer : forall x, thunk_eq (Answer x) (Answer x)
| EqThinkL : forall m1 m2, thunk_eq m1 m2 -> thunk_eq (Think m1) m2
| EqThinkR : forall m1 m2, thunk_eq m1 m2 -> thunk_eq m1 (Think m2).

Section thunk_eq_coind.
  Variable A : Type.
  Variable P : thunk A -> thunk A -> Prop.

  Hypothesis H : forall m1 m2,
    P m1 m2 -> match m1, m2 with
               | Answer x1, Answer x2 => x1 = x2
               | Think m1', Think m2' => P m1' m2'
               | Think m1', _ => P m1' m2
               | _, Think m2' => P m1 m2'
               end.

  Theorem thunk_eq_coind : forall m1 m2, P m1 m2 -> thunk_eq m1 m2.
    cofix; intros;
      match goal with
        | [ H' : P _ _ |- _ ] => specialize (H H'); clear H'
      end; destruct m1; destruct m2; subst; repeat constructor; auto.
  Qed.
End thunk_eq_coind.

(* silly function to provoke reduction of co-recursive call *)
Definition frob A (m : thunk A) : thunk A :=
  match m with
    | Answer x => Answer x
    | Think m' => Think m'
  end.

Theorem frob_eq : forall A (m : thunk A), frob m = m.
  destruct m; reflexivity.
Qed.

Theorem thunk_eq_frob : forall A (m1 m2 : thunk A),
  thunk_eq (frob m1) (frob m2)
  -> thunk_eq m1 m2.
  intros; repeat rewrite frob_eq in *; auto.
Qed.

Ltac findDestr :=
  match goal with
    | [ |- context[match ?E with Answer _ => _ | Think _ => _ end] ] =>
      match E with
        | context[match _ with Answer _ => _ | Think _ => _ end] => fail 1
        | _ => destruct E
      end
  end.

Theorem thunk_eq_refl : forall A (m : thunk A), thunk_eq m m.
  intros; apply (thunk_eq_coind (fun m1 m2 => m1 = m2)); crush; findDestr; reflexivity.
Qed.

Hint Resolve thunk_eq_refl.

Theorem tleft_identity : forall A B (a : A) (f : A -> thunk B),
  thunk_eq (TBind (Answer a) f) (f a).
  intros; apply thunk_eq_frob; crush.
Qed.

Theorem tright_identity : forall A (m : thunk A),
  thunk_eq (TBind m (@Answer _)) m.
  intros; apply (thunk_eq_coind (fun m1 m2 => m1 = TBind m2 (@Answer _))); crush;
    findDestr; reflexivity.
Qed.

Lemma TBind_Answer : forall (A B : Type) (v : A) (m2 : A -> thunk B),
  TBind (Answer v) m2 = m2 v.
  intros; rewrite <- (frob_eq (TBind (Answer v) m2));
    simpl; findDestr; reflexivity.
Qed.

Hint Rewrite TBind_Answer.

Theorem tassociativity :
  forall A B C (m : thunk A) (f : A -> thunk B) (g : B -> thunk C),
  thunk_eq (TBind (TBind m f) g) (TBind m (fun x => TBind (f x) g)).
Proof.
  intros. apply (thunk_eq_coind (fun m1 m2 => (exists m,
    m1 = TBind (TBind m f) g
    /\ m2 = TBind m (fun x => TBind (f x) g))
  \/ m1 = m2)); crush; eauto; repeat (findDestr; crush; eauto).
Qed.

(* example of tail-recursive factorial function *)
CoFixpoint fact (n acc : nat) : thunk nat :=
  match n with
    | O => Answer acc
    | S n' => Think (fact n' (S n' * acc))
  end.

(* evaluation relation *)
Inductive eval A : thunk A -> A -> Prop :=
| EvalAnswer : forall x, eval (Answer x) x
| EvalThink : forall m x, eval m x -> eval (Think m) x.

Hint Rewrite frob_eq.

Lemma eval_frob : forall A (c : thunk A) x,
  eval (frob c) x -> eval c x.
  crush.
Qed.

Example eval_fact : eval (fact 5 1) 120.
  repeat (apply eval_frob; simpl; constructor).
Qed.

Notation "x <- m1 ; m2" :=
  (TBind m1 (fun x => m2)) (right associativity, at level 70).

(*
(* guardedness condition is violated *)
CoFixpoint fib (n : nat) : thunk nat :=
  match n with
    | 0 => Answer 1
    | 1 => Answer 1
    | _ => n1 <- fib (pred n);
      n2 <- fib (pred (pred n));
      Answer (n1 + n2)
  end.
*)
(* The two recursive calls are immediate arguments to [TBind],
   but [TBind] is not a constructor of [thunk]. Rather, it is a defined function.
   The [fact] example succeeded because it was already tail recursive,
   meaning no further computation is needed after a recursive call. *)

(* define a new type family where "bind" is a constructor *)
(* taking advantage of Coq's support for "recursively non-uniform parameters" *)
CoInductive comp (A : Type) : Type :=
| Ret : A -> comp A
| Bnd : forall B, comp B -> (B -> comp A) -> comp A.

Inductive exec A : comp A -> A -> Prop :=
| ExecRet : forall x, exec (Ret x) x
| ExecBnd : forall B (c : comp B) (f : B -> comp A) x1 x2,
  exec (A := B) c x1 -> (* <- ??? *)
  exec (f x1) x2 ->
  exec (Bnd c f) x2.

(* prove that Ret and Bnd form a monad according to a notion of comp equality
   based on exec *)
Hint Constructors exec.

Definition comp_eq A (c1 c2 : comp A) := forall r, exec c1 r <-> exec c2 r.

Ltac inverter := repeat match goal with
                                                           (* ??? v *)
                          | [ H : exec _ _ |- _ ] => inversion H; []; crush
                        end.

Theorem cleft_identity : forall A B (a : A) (f : A -> comp B),
  comp_eq (Bnd (Ret a) f) (f a).
  red. crush; inverter; eauto.
Qed.

Theorem cright_identity : forall A (m : comp A),
  comp_eq (Bnd m (@Ret _)) m.
  red; crush; inverter; eauto.
Qed.

Lemma cassociativity1 : forall A B C (f : A -> comp B) (g : B -> comp C) r c,
  exec c r
  -> forall m, c = Bnd (Bnd m f) g
  -> exec (Bnd m (fun x => Bnd (f x) g)) r.
  induction 1; crush.
  match goal with
    | [ H : Bnd _ _ = Bnd _ _ |- _ ] => injection H; clear H; intros; try subst
  end.
  try subst B. (* This line expected to fail in Coq 8.4 and succeed in Coq 8.6. *)
  crush.
  inversion H; clear H; crush.
  eauto.
Qed.

Lemma cassociativity2 : forall A B C (f : A -> comp B) (g : B -> comp C) r c,
  exec c r
  -> forall m, c = Bnd m (fun x => Bnd (f x) g)
  -> exec (Bnd (Bnd m f) g) r.
  induction 1; crush.
  match goal with
    | [ H : Bnd _ _ = Bnd _ _ |- _ ] => injection H; clear H; intros; try subst
  end.
  try subst A. (* Same as above *)
  crush.
  inversion H0; clear H0; crush.
  eauto.
Qed.

Hint Resolve cassociativity1 cassociativity2.

Theorem cassociativity : forall A B C (m : comp A) (f : A -> comp B) (g : B -> comp C),
  comp_eq (Bnd (Bnd m f) g) (Bnd m (fun x => Bnd (f x) g)).
  red; crush; eauto.
Qed.

(* refined version of mergeSort *)
Notation "x <- m1 ; m2" := (Bnd m1 (fun x => m2)).

CoFixpoint mergeSort'' A (le : A -> A -> bool) (ls : list A) : comp (list A) :=
  if le_lt_dec 2 (length ls)
    then let lss := split ls in
      ls1 <- mergeSort'' le (fst lss);
      ls2 <- mergeSort'' le (snd lss);
      Ret (merge le ls1 ls2)
    else Ret ls.

Definition frob' A (c : comp A) :=
  match c with
    | Ret x => Ret x
    | Bnd _ c' f => Bnd c' f
  end.

Lemma exec_frob : forall A (c : comp A) x,
  exec (frob' c) x -> exec c x.
  destruct c; crush.
Qed.

Example test_mergeSort'' :
  exec (mergeSort'' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil))
  (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  repeat (apply exec_frob; simpl; econstructor).
Qed.

(* [comp] still has a serious expressivity weakness!! *)
Definition curriedAdd (n : nat) := Ret (fun m : nat => Ret (n + m)).

(* following shouldn't work... *)
Definition testCurriedAdd := Bnd (curriedAdd 2) (fun f => f 3).
Eval simpl in testCurriedAdd.
(*
  violating Coq's predicativity restriction (no quantifier in an inductive or
  co-inductive type's definition may ever be instantiated with a term that
  contains the type being defined)
*)


(* 7.4 Comparing the Alternatives *)

(*
Four different approaches to encode general recursive definitions in Coq
1. use well-founded relation
2. non-termination monad inspired by domain theory
3. use co-inductive
3'. add Bind as a constructor (comp monad)
*)

(*
. automatic integration with normal Coq programming
. evaluation of function calls can take place entirely inside
  Coq's built-in computation machinery
  => only in 1. (well-founded recursion) that...

. a function and its termination argument may be developed separately
  (allow defining functions that fail to terminate on some or all inputs)
. able to write recursive definitions in natural syntax
  => enabled in 2, 3, 3'

. 1 and 2 impose proof obligations to define functions
  . 1 requires proof of extensionality
  . 2 requires proof of continuity

. 3' does not support the effective mixing of higher-order functions and
  general recursion, while all the other techniques do
*)

Definition curriedAdd' (n : nat) := Return (fun m : nat => Return (n + m)).
Definition testCurriedAdd' := Bind (curriedAdd' 2) (fun f => f 3).

Fixpoint map A B (f : A -> computation B) (ls : list A) : computation (list B) :=
  match ls with
    | nil => Return nil
    | x :: ls' =>
      Bind (f x) (fun x' =>
        Bind (map f ls') (fun ls'' =>
          Return (x' :: ls'')))
  end.

Theorem test_map : run (map (fun x => Return (S x)) (1 :: 2 :: 3 :: nil))
  (2 :: 3 :: 4 :: nil).
  exists 1; reflexivity.
Qed.

(*
. disadvantage of 3': cannot prove an inversion lemma for executions of [Bind]
  without appealing to an axiom

[sum up]
trade-off between
. functional programming expressiveness and compatibility with
  normal Coq types and computation
. the level of proof obligations one is willing to handle at
  function definition time
*)
