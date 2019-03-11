Require Import List.
Require Import Cpdt.CpdtTactics.
Require Coq.extraction.Extraction.
Set Implicit Arguments.
Set Asymmetric Patterns.
Extraction Language OCaml.

(* PART 2: Programming with Dependent Types *)
(* Chapter 6. Subset Types and Variations *)

Extraction pred.
(*
(** val pred : nat -> nat **)
let pred = function
  | O -> O
  | S u -> u
*)

(* We might like to be sure that we never try to take the predecessor of 0.
   We can enforce this by giving pred a stronger, dependent type.  *)

Lemma zgtz : 0 > 0 -> False.
  crush.
Qed.

Definition pred_strong1 (n : nat) : n > 0 (* : proof *) -> nat :=
  match n with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

(* argument n of pred strong1 can be made implicit,
   since it can be deduced from the type of the second argument *)
Theorem two_gt0 : 2 > 0.
  crush.
Qed.

Eval compute in pred_strong1 two_gt0.

Lemma zero_gt0 : 0 > 0. (* absurd! *)
Admitted.
Eval compute in pred_strong1 zero_gt0.
(*
    = match zgtz zero_gt0 return nat with
      end
    : nat
*)

(*
(* following example fails to type-check *)
Definition pred_strong1' (n : nat) (pf : n > 0) : nat :=
  match n with
    | O => match zgtz pf with end
    | S n' => n'
  end.
*)

(* Coq's heuristics had inferred [return n > 0 -> nat] in the above example. *)
Definition pred_strong1' (n : nat) : n > 0 -> nat :=
  match n return n > 0 -> nat with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

Extraction pred_strong1.

(* Curry-Howard twin of ex (sig : Type, ex : Prop) *)
Print sig.
(*
  Inductive sig (A : Type) (P : A -> Prop) : Type :=
      exist : forall x : A, P x -> { x : A | P x }
  (Argument A is implicit)
*)
(* cf. *)
Print ex.
(*
  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
      ex_intro : forall x : A, P x -> exists y, P y
  (Argument A is implicit)
*)

Locate "{ _ : _ | _ }".
(*
  Notation
  "{ x : A  |  P }" := sig (fun x : A => P)
*)

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist O pf => match zgtz pf with end
    | exist (S n') _ => n'
  end.

                                 (* v "P" in the definition of sig *)
Eval compute in pred_strong2 (exist _ 2 two_gt0).
                             (* ^ constructor of sig *)
(* ... the above is the same as this: *)
Eval compute in pred_strong2 (exist (fun n => n > 0) 2 two_gt0).
Extraction pred_strong2.

(*
  Definition proj1_sig (e:sig P) := match e with
                                    | exist _ a b => a
                                    end.

  : function to extract the first argument of sig (the value that 'exists')
*)
Definition pred_strong3 (s : {n : nat | n > 0}) : {m : nat | (proj1_sig s) = S m} :=
  match s return {m : nat | proj1_sig s = S m} with
    | exist 0 pf => match zgtz pf with end
    | exist (S n') pf => exist _ n' (eq_refl _)
  end.

Eval compute in proj1_sig (exist _ 2 two_gt0). (* 2 *)
Eval compute in pred_strong3 (exist _ 2 two_gt0).
(*
  = exist (fun m : nat => 2 = S m) 1 eq_refl
  : {m : nat | proj1_sig (exist (lt 0) 2 two_gt0) = S m}

  ** eq_refl: law of 'reflexivity'
*)

Extraction pred_strong3.

Check False_rec.
(* forall P : Set, False -> P *)

(* tactic-based theorem proving
   cf) https://softwarefoundations.cis.upenn.edu/lf-current/ProofObjects.html#lab268 *)
Definition pred_strong4 : forall n : nat, n > 0 -> {m : nat | n = S m}.
  (* refine _term_ : provide _term_ as proof.
                     _term_ should have the same type as the goal. *)
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end).
  crush.
  reflexivity.
Restart.
  destruct n as [| n']; intros.
  - apply exist with (x:=0). inversion H.
  - apply exist with (x:=n'). reflexivity.
Defined. (* <- by using 'Defined', proof will remain transparent
               (using 'Qed' instead will make the proof opaque) *)

Print pred_strong4.
Eval compute in pred_strong4 two_gt0.

Definition pred_strong4' : forall n : nat, n > 0 -> {m : nat | n = S m}.
  (* abstract : produces shorter terms, by automatically abstracting subgoals
                into named lemmas (???) *)
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end); abstract crush.
Defined.

Print pred_strong4'.
(*
  pred_strong4' =
  fun n : nat =>
  match n as n0 return (n0 > 0 -> {m : nat | n0 = S m}) with
  | 0 =>
      fun _H : 0 > 0 =>
      False_rec {m : nat | 0 = S m} (pred_strong4'_subproof n _H)
  | S n' =>
      fun _H : S n' > 0 =>
      exist (fun m : nat => S n' = S m) n' (pred_strong4'_subproof0 n _H)
  end
       : forall n : nat, n > 0 -> {m : nat | n = S m}
*)
Print pred_strong4'_subproof.
(*
  pred_strong4'_subproof = 
  fun g : 0 > 0 =>
  Bool.diff_false_true
    (Bool.absurd_eq_true false
       (Bool.diff_false_true
          (Bool.absurd_eq_true false (pred_strong4'_subproof_subproof g))))
       : 0 > 0 -> False
*)
Print pred_strong4'_subproof0.
(*
  pred_strong4'_subproof0 = 
  fun n' : nat => eq_refl
       : forall n' : nat, S n' = S n'
*)

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Definition pred_strong5 : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => !
      | S n' => fun _ => [n']
    end); crush.
Defined.

Eval compute in pred_strong5 two_gt0.

(* using Coq's new feature [Program] *)
(* cf: https://sites.google.com/site/suharahiromichi/program-ing-coq/coq_subset *)
(* TODO: understand *)
Obligation Tactic := crush.
Program Definition pred_strong6 (n : nat) (_ : n > 0) : {m : nat | n = S m} :=
  match n with
    | O => _
    | S n' => n'
  end.

Eval compute in pred_strong6 two_gt0.

(* 6.2 Decidable Proposition Types *)

(* another type in STL which captures the idea of program values *)
Print sumbool.
(*
Inductive sumbool (A : Prop) (B : Prop) : Set :=
    left : A -> {A} + {B} | right : B -> {A} + {B}
*)

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).
(* ^ The [if] form actually works when the test expression has any two-constructor inductive type. *)

Definition eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
  refine (fix f (n m : nat) : {n = m} + {n <> m} :=
    match n, m with
      | O, O => Yes
      | S n', S m' => Reduce (f n' m')
      | _, _ => No
    end); congruence.
    (* congruence: http://proofcafe.org/sf/UseAuto_J.html *)
Restart.
  induction n.
  - destruct m.
    + left. reflexivity.
    + right. congruence.
  - induction m.
    + right. congruence.
    + destruct (IHn m).
      { left. congruence. }
      { right. congruence. }
Defined.

Eval compute in eq_nat_dec 2 2.
Eval compute in eq_nat_dec 2 3.
(* Note: Yes and No notations are hiding proofs establishing the correctness of the outputs. *)

Extraction eq_nat_dec.
(*
(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> Left
              | S n0 -> Right)
    | S n' -> (match m with
                 | O -> Right
                 | S m' -> eq_nat_dec n' m')
*)

(* Proving this kind of decidable equality result is so common that Coq comes with a tactic for automating it.
 https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.decide-equality
*)
Definition eq_nat_dec' (n m : nat) : {n = m} + {n <> m}.
  decide equality.
Defined.
Extraction eq_nat_dec'.

(* use "true" and "false" instead of "Left" and "Right" *)
Extract Inductive sumbool => "bool" ["true" "false"].
Extraction eq_nat_dec'.

Notation "x || y" := (if x then Yes else Reduce y).

(* function to decide list membership *)
Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}. (* ??? *)

  Definition In_dec : forall (x : A) (ls : list A), {In x ls} + {~ In x ls}.
    refine (fix f (x : A) (ls : list A) : {In x ls} + {~ In x ls} :=
      match ls with
      | nil => No
      | x' :: ls' => A_eq_dec x x' || f x ls'
      end); crush.
  Restart.
    induction ls.
    - right. intros contra. inversion contra.
    - simpl. destruct (A_eq_dec a x).
      + subst. left. left. reflexivity.
      + destruct IHls.
        { left. right. assumption. }
        { right. intros contra. destruct contra; auto. }
  Defined.
End In_dec.

Eval compute in In_dec eq_nat_dec 2 (1 :: 2 :: nil).
Eval compute in In_dec eq_nat_dec 3 (1 :: 2 :: nil).
Extraction In_dec.
(*
(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec a_eq_dec x = function
  | Nil -> false
  | Cons (x', ls') ->
      (match a_eq_dec x x' with
         | true -> true
         | false -> in_dec a_eq_dec x ls')
*)


(* 6.3 Partial Subset Types *)

(* use 'maybe' to allow obligation-free failure *)
Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

Definition pred_strong7 : forall n : nat, {{m | n = S m}}.
  refine (fun n =>
    match n return {{m | n = S m}} with
      | O => ??
      | S n' => [|n'|]
    end); trivial.
Defined.

Eval compute in pred_strong7 2.
Eval compute in pred_strong7 0.

(* How to make sure we'll allow [Unknown] only when the result is really unknown?
   => ex. [sumor]
   *)

Print sumor.
(*
Inductive sumor (A : Type) (B : Prop) : Type :=
    inleft : A -> A + {B} | inright : B -> A + {B}

  : sumor is either value of A or proofs of B.
*)
Locate "_ + { _ }".

Notation "!!" := (inright _ _). (* proof *)
Notation "[|| x ||]" := (inleft _ [x]). (* value *)
(* ^ supecialized to [sumor]s whose [A] params are instantiated with regular subset types *)

(* possibly failing predecessor ([sumor]-based, maximally expressive) *)
Definition pred_strong8 : forall n : nat, {m : nat | n = S m} + {n = 0}.
  refine (fun n =>
    match n with
      | O => !!
      | S n' => [||n'||]
    end); trivial.
Defined.

Eval compute in pred_strong8 2.
Eval compute in pred_strong8 0.


(* 6.4 Monadic Notations *)

(* "bind"-like notation *)
Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60).

(* a function to take the predecessors of two naturals at once *)
Definition doublePred : forall n1 n2 : nat,
  {{p | n1 = S (fst p) /\ n2 = S (snd p)}}.
  refine (fun n1 n2 =>
    m1 <- pred_strong7 n1;
    m2 <- pred_strong7 n2;
    [|(m1, m2)|]); tauto.
Defined.

(* [sumor] version of the "bind" notation *)
Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).

Definition doublePred' : forall n1 n2 : nat,
  {p : nat * nat | n1 = S (fst p) /\ n2 = S (snd p)}
  + {n1 = 0 \/ n2 = 0}.
  refine (fun n1 n2 =>
    m1 <-- pred_strong8 n1;
    m2 <-- pred_strong8 n2;
    [||(m1, m2)||]); tauto.
Defined.


(* 6.5 A Type-Checking Example *)

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

Inductive type : Set := TNat | TBool.

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n,
  hasType (Nat n) TNat
| HtPlus : forall e1 e2,
  hasType e1 TNat
  -> hasType e2 TNat
  -> hasType (Plus e1 e2) TNat
| HtBool : forall b,
  hasType (Bool b) TBool
| HtAnd : forall e1 e2,
  hasType e1 TBool
  -> hasType e2 TBool
  -> hasType (And e1 e2) TBool.

(* function to compare two types *)
Definition eq_type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

(* notation for "assertion" *)
Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60).

(* every [[|e|]] expression adds a [hasType] proof obligation *)
Definition typeCheck : forall e : exp, {{t | hasType e t}}.
  (* Note: {{t | hasType e t}} = maybe (fun t => hasType e t) *)
  Hint Constructors hasType.
  refine (fix F (e : exp) : {{t | hasType e t}} :=
    match e return {{t | hasType e t}} with
      | Nat _ => [|TNat|]
      | Plus e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TNat;;
        eq_type_dec t2 TNat;;
        [|TNat|]
      | Bool _ => [|TBool|]
      | And e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TBool;;
        eq_type_dec t2 TBool;;
        [|TBool|]
    end); crush.
Defined.

Eval simpl in typeCheck (Nat 0).
Eval simpl in typeCheck (Plus (Nat 1) (Nat 2)).
Eval simpl in typeCheck (Plus (Nat 1) (Bool false)).
Extraction typeCheck.
(*
(** val typeCheck : exp -> type0 maybe **)

let rec typeCheck = function
  | Nat n -> Found TNat
  | Plus (e1, e2) ->
      (match typeCheck e1 with
         | Unknown -> Unknown
         | Found t1 ->
             (match typeCheck e2 with
                | Unknown -> Unknown
                | Found t2 ->
                    (match eq_type_dec t1 TNat with
                       | true ->
                           (match eq_type_dec t2 TNat with
                              | true -> Found TNat
                              | false -> Unknown)
                       | false -> Unknown)))
  | Bool b -> Found TBool
  | And (e1, e2) ->
      (match typeCheck e1 with
         | Unknown -> Unknown
         | Found t1 ->
             (match typeCheck e2 with
                | Unknown -> Unknown
                | Found t2 ->
                    (match eq_type_dec t1 TBool with
                       | true ->
                           (match eq_type_dec t2 TBool with
                              | true -> Found TBool
                              | false -> Unknown)
                       | false -> Unknown)))
*)

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60).

(* det = deterministic *)
Lemma hasType_det : forall e t1,
  hasType e t1 ->
  forall t2, hasType e t2 ->
  t1 = t2.
Proof.
  induction 1; inversion 1; crush.
Restart.
  induction e; intros.
  - (* Nat *)  inversion H. inversion H0. reflexivity.
  - (* Plus *) inversion H. inversion H0. reflexivity.
  - (* Bool *) inversion H. inversion H0. reflexivity.
  - (* And *)  inversion H. inversion H0. reflexivity.
Qed.

Definition typeCheck' : forall e : exp, {t : type | hasType e t} + {forall t, ~ hasType e t}.
  Hint Constructors hasType.
  Hint Resolve hasType_det.
  (* Since its statement includes [forall]-bound variables that do not appear in its conclusion, only [eauto] will apply this hint. *)

  refine (fix F (e : exp) : {t : type | hasType e t} + {forall t, ~ hasType e t} :=
    match e return {t : type | hasType e t} + {forall t, ~ hasType e t} with
      | Nat _ => [||TNat||]
      | Plus e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TNat;;;
        eq_type_dec t2 TNat;;;
        [||TNat||]
      | Bool _ => [||TBool||]
      | And e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TBool;;;
        eq_type_dec t2 TBool;;;
        [||TBool||]
    end); clear F; crush' tt hasType; eauto.
  (* We clear [F], the local name for the recursive function, to avoid strange proofs that refer to recursive calls that we never make.  Such a step is usually warranted when defining a recursive function with [refine].  The [crush] variant [crush'] helps us by performing automatic inversion on instances of the predicates specified in its second argument.  Once we throw in [eauto] to apply [hasType_det] for us, we have discharged all the subgoals. *)
Restart.
  induction e.
  - left. exists TNat. (* somehow worked! *) constructor.
  - destruct IHe1 as [IHe1' | IHe1'].
    + destruct IHe2 as [IHe2' | IHe2'].
      { inversion IHe1' as [t1 H1]. inversion IHe2' as [t2 H2].
        destruct t1.
        - (* t1 = TNat *) destruct t2.
          + (* t2 = TNat *) left. exists TNat. auto.
          + (* t2 = TBool *) right. intros t H. inversion H; subst.
            apply hasType_det with (t1:=TNat) in H2. inversion H2. trivial.
        - (* t1 = TBool *) right. intros t H. inversion H; subst.
          apply hasType_det with (t1:=TNat) in H1. inversion H1. trivial. }
      { (* e2 is untypable *)
         right. intros t H. inversion H; subst. apply IHe2' in H4. auto. }
    + (* e1 is untypable *)
      right. intros t H. inversion H; subst. apply IHe1' in H2. auto.
  - left. exists TBool. constructor.
  - destruct IHe1 as [IHe1' | IHe1'].
    + destruct IHe2 as [IHe2' | IHe2'].
      { inversion IHe1' as [t1 H1]. inversion IHe2' as [t2 H2].
        destruct t1.
        - (* t1 = TNat *) right. intros t H. inversion H; subst.
          apply hasType_det with (t1:=TBool) in H1. inversion H1. trivial.
        - (* t1 = TBool *) destruct t2.
          + (* t2 = TNat *) right. intros t H. inversion H; subst.
            apply hasType_det with (t1:=TBool) in H2. inversion H2. trivial.
          + (* t2 = TBool *) left. exists TBool. auto. }
      { (* e2 is untypable *)
         right. intros t H. inversion H; subst. apply IHe2' in H4. auto. }
    + (* e1 is untypable *)
      right. intros t H. inversion H; subst. apply IHe1' in H2. auto.
Defined.

Eval simpl in typeCheck' (Nat 0).
Eval simpl in typeCheck' (Plus (Nat 1) (Nat 2)).
Eval simpl in typeCheck' (Plus (Nat 1) (Bool false)).
(* Extraction typeCheck'. *)
