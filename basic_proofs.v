

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

Fixpoint eqb (n m : nat) : bool :=
  match n with
    | O => match m with
      | O => true
      | S m' => false
      end
    | S n' => match m with
      | O => false
      | S m' => eqb n' m'
      end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Definition ltb (n m : nat) : bool :=
  leb (S n) m.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.




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

Theorem plus_to_nat :
  forall (l : letter) (m : modifier),
    m = Plus -> lower_grade (Grade l m) = (Grade l Natural).
  Proof. intros l m. intros H. rewrite H. destruct l.
   - reflexivity.
   - reflexivity.
   - reflexivity.
   - reflexivity.
   - reflexivity.
   Qed.

Theorem nat_to_minus :
  forall (l : letter) (m : modifier),
    m = Natural -> lower_grade (Grade l m) = (Grade l Minus).
  Proof. intros l m. intros H. rewrite H. destruct l.
   - reflexivity.
   - reflexivity.
   - reflexivity.
   - reflexivity.
   - reflexivity.
   Qed.

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comp (Grade F Minus) g = Lt ->
    grade_comp (lower_grade g) g = Lt.
Proof.
  intros g H.
  destruct g as [l m] eqn:Eqg.
  destruct m eqn:Eqm.
  - rewrite plus_to_nat. simpl. rewrite letter_comp_eq. reflexivity. reflexivity.
  - rewrite nat_to_minus. simpl. rewrite letter_comp_eq. reflexivity. reflexivity.
  - destruct l eqn:Eql.
    + simpl lower_grade. simpl grade_comp. reflexivity.
    + simpl lower_grade. simpl grade_comp. reflexivity.
    + simpl lower_grade. simpl grade_comp. reflexivity.
    + simpl lower_grade. simpl grade_comp. reflexivity.
    + rewrite lower_grade_F_Minus. rewrite H. reflexivity.
  Qed.

Definition apply_late_policy (late_days : nat) ( g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

Theorem apply_late_policy_unfold : 
  forall (late_days : nat) (g : grade),
    apply_late_policy late_days g =
      if late_days <? 9 then g
      else if late_days <? 17 then lower_grade g
      else if late_days <? 21 then lower_grade (lower_grade g)
      else lower_grade (lower_grade (lower_grade g)).
  Proof. intros. reflexivity. Qed.
End LateDays.