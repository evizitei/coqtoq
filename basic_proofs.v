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

Definition mod_comp (m1 m2 : modifier) : comparison :=
  match m1, m2 with
    | Plus, Plus => Eq
    | Plus, _ => Gt
    | Natural, Plus => Lt
    | Natural, Natural => Eq
    | Natural, Minus => Gt
    | Minus, Minus => Eq
    | Minus, _ => Lt
  end.
  
Definition grade_comp (g1 g2 : grade) : comparison :=
  match g1, g2 with
    | Grade l1 m1, Grade l2 m2 =>
      let lc := letter_comp l1 l2 in
      match lc with
        | Eq => mod_comp m1 m2
        | _ => lc
      end
  end.

Example test_grade_comp1 :
  grade_comp (Grade A Minus) (Grade B Plus) = Gt.
Proof. reflexivity. Qed.

Example test_grade_comp2 :
  grade_comp (Grade A Minus) (Grade A Plus) = Lt.
Proof. reflexivity. Qed.

Example test_grade_comp3 :
  grade_comp (Grade F Plus) (Grade F Plus) = Eq.
Proof. reflexivity. Qed.

Definition lower_letter (l : letter) : letter :=
match l with
    | A => B
    | B => C
    | C => D
    | D => F
    | F => F
end.

Theorem lower_letter_lowers :
    forall (l : letter),
        letter_comp F l = Lt ->
        letter_comp (lower_letter l) l = Lt.
    Proof.
        intros l H. destruct l eqn:El.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - simpl. rewrite <- H. reflexivity.
    Qed.

Definition lower_grade (g : grade) : grade :=
  match g with
    | Grade l Plus => (Grade l Natural)
    | Grade l Natural => (Grade l Minus)
    | Grade F Minus => (Grade F Minus)
    | Grade l Minus => (Grade (lower_letter l) Plus)
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
  Proof. reflexivity. Qed.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
  Proof. reflexivity. Qed.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
  Proof. reflexivity. Qed.
  
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
  Proof. reflexivity. Qed.

Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
  Proof. reflexivity. Qed.

Theorem lower_grade_F_Minus :
  lower_grade (Grade F Minus) = (Grade F Minus).
  Proof. simpl. reflexivity. Qed.

End LateDays.
