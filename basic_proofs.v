Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
intros f H b. rewrite H. rewrite H. reflexivity. Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) ->
      forall (b : bool), f (f b) = b.
Proof.
intros f H b. rewrite H. rewrite H. destruct b eqn:Eqb.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.



Theorem andb_eq_orb :
  forall (b c : bool),
    (andb b c = orb b c) -> b = c.
Proof. intros b c H. destruct b.
  - simpl in H. rewrite H. reflexivity.
  - simpl in H. rewrite H. reflexivity.
Qed.

Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l : letter) (m : modifier).

Inductive comparison : Type :=
  | Eq | Lt | Gt.

Definition letter_comp (l1 l2 : letter) : comparison :=
 match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, F => Gt
  | D, D => Eq
  | D, _ => Lt
  | F, F => Eq
  | F, _ => Lt
 end.

Theorem letter_comp_eq :
  forall l : letter, letter_comp l l = Eq.
Proof.
  intros l. destruct l eqn:Eql.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

End LateDays.