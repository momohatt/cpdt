Inductive truth : Set :=
| Yes : truth
| No : truth
| Maybe : truth.

Fixpoint not (t : truth) : truth :=
  match t with
  | Yes => No
  | No => Yes
  | Maybe => Maybe
  end.

Fixpoint and (t1 t2 : truth) : truth :=
  match t1 with
  | Yes => t2
  | No => No
  | Maybe => (match t2 with
      | No => No
      | _ => Maybe
      end)
  end.

Fixpoint or (t1 t2 : truth) : truth :=
  match t1 with
  | Yes => Yes
  | No => t2
  | Maybe => (match t2 with
      | Yes => Yes
      | _ => Maybe
      end)
  end.

Theorem and_comm : forall t1 t2 t3,
  and (and t1 t2) t3 = and t1 (and t2 t3).
Proof.
  destruct t1; destruct t2; destruct t3; reflexivity.
Qed.

Theorem and_or_dist : forall t1 t2 t3,
  and (or t1 t2) t3 = or (and t1 t3) (and t2 t3).
Proof.
  destruct t1; destruct t2; destruct t3; reflexivity.
Qed.
