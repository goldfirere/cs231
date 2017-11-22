Require Import demo.

(* Compute a list of pairs of factors that multiply to a number. For example,
   factor_pairs 6 includes (1,6), (2,3), (3,2), and (6,1). *)
Fixpoint build_factor_pairs n d :=
  match d with
  | 0 => nil
  | S d' => if n mod d =? 0
            then cons (d, n / d) (build_factor_pairs n d')
            else build_factor_pairs n d'
  end.

Definition factor_pairs n := build_factor_pairs n n.

(* This lemma asserts that every pair in factor_pairs indeed multiplies to the original number *)
Lemma build_factor_pairs_correct : forall n d pair,
    In pair (build_factor_pairs n d) -> (fst pair * snd pair = n).
Proof.
  intro n. intro d.
  induction d.
  - intro pair.
    simpl.
    intro contra.
    contradiction.
  - intro pair.
    destruct pair.
    simpl.
    remember (divmod n d 0 d).
    destruct p.
    simpl.
    destruct (eq_nat_dec d n3).
    + subst.
      rewrite <- minus_diag_reverse.
      simpl.
      intro H.
      destruct H.
      * inversion H.
        subst.
        pose proof (Nat.divmod_spec n n3 0 n3).
        assert (n3 <= n3) by omega.
        specialize (H0 H1).
        rewrite <- Heqp in H0.
        rewrite <- minus_diag_reverse in H0.
        rewrite <- mult_n_O in H0.
        rewrite <- plus_n_O in H0.
        rewrite <- plus_n_O in H0.
        rewrite <- plus_n_O in H0.
        destruct H0.
        symmetry.
        assumption.
      * apply IHd with (pair := (n0,n1)).
        assumption.
    + pose proof (Nat.divmod_spec n d 0 d).
      assert (d <= d) by omega.
      specialize (H H0).
      rewrite <- Heqp in H.
      destruct H.
      replace (d - n3 =? 0) with false.
      intro H2.
      apply IHd with (pair := (n0,n1)).
      assumption.
      clear H IHd Heqp H0.
      symmetry.
      rewrite Nat.eqb_neq.
      omega.
Qed.

Lemma build_factors_1 : forall n d, n >= d -> d >= 1 -> In (1, n) (build_factor_pairs n d).
Proof.
  intro n. intro d.
  induction d.
  - omega.
  - intro Hnd. intro Hd1.
    simpl.
    destruct d.
    + simpl.
      left.
      replace (fst (Nat.divmod n 0 0 0)) with n.
      reflexivity.

      pose proof (Nat.divmod_spec n 0 0 0).
      assert (0 <= 0) by omega.
      specialize (H H0).
      remember (divmod n 0 0 0).
      destruct p.
      simpl.
      omega.

    + destruct (S d - snd (divmod n (S d) 0 (S d)) =? 0).
      * simpl.
        right.
        apply IHd.
        omega.
        omega.
      * apply IHd.
        omega.
        omega.
Qed.

Lemma build_factors_first_step :
  forall n, build_factor_pairs (S n) (S n) = cons (S n, 1) (build_factor_pairs (S n) n).
Proof.
  intro n.
  unfold build_factor_pairs.
  replace (S n mod S n =? 0) with true.
  replace (S n / S n) with 1.
  reflexivity.

  symmetry.
  apply Nat.div_same.
  omega.

  symmetry.
  rewrite Nat.eqb_eq.
  apply Nat.mod_same.
  omega.
Qed.
  
Lemma factors_len_ge_2 : forall n, n > 1 -> In (n, 1) (factor_pairs n) /\ In (1, n) (factor_pairs n).
Proof.
  intro n.
  destruct n; [omega |].
  destruct n; [omega |].
  intro Hgt.
  unfold factor_pairs.
  split.
  - rewrite build_factors_first_step.
    unfold In.
    left.
    reflexivity.
  - apply build_factors_1.
    omega.
    omega.
Qed.
    
Theorem prime_or_composite : forall n, n > 1 -> prime n \/ composite n.
Proof.
  intro n.
  intro greater.
  remember (factor_pairs n).
  unfold factor_pairs in Heql.
  destruct n; [omega |].
  rewrite build_factors_first_step in Heql.
  destruct l.
  inversion Heql.
  inversion Heql.
  destruct l.
  pose proof (build_factors_1 (S n) n).
  assert (In (1, S n) (build_factor_pairs (S n) n)).
  apply H.
  omega.
  omega.
  rewrite <- H1 in H2.
  inversion H2.
  destruct p0.
  destruct (eq_nat_dec n0 1).
  - left.
    admit.
  - right.
    unfold composite.
    exists n0.
    exists n1.
    split.
    + pose proof (build_factor_pairs_correct (S n) n (n0, n1)).
      simpl in H.
      assert (n0 * n1 = S n).
      apply H.
      rewrite <- H1.
      simpl.
      left.
      reflexivity.
      
  set (len := length factors).
  

Definition 
