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













