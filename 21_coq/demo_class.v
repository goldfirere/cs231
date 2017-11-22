(* Discrete Mathematics in Coq, based on definitions in Epp, 4th Edition *)

Require Import Omega.
Require Import Nat.
Require Import List.
Require Import Arith.
Require Import Coq.Program.Wf.

(* Section 2.1 *)

(* This is the encoding of a definition of a statement, p. 24.
   It's called "lem" because the formal name for this property is the
   "Law of the Excluded Middle."

   Not all logics include this notion, so it's not built into Coq. Instead,
   we declare it as an axiom. A logic that doesn't have L.E.M. is called
   constructive. A logic that does include L.E.M. is called classical. *)
Axiom lem : forall p, p \/ ~p.

Theorem and_comm : forall p q, p /\ q <-> q /\ p.
Proof.
  intro p.
  intro q.
  split.
  - intro p_and_q.
    destruct p_and_q.
    split.
    + assumption.
    + assumption.
  - intro q_and_p.
    destruct q_and_p.
    split.
    + assumption.
    + assumption.
Qed.
  
Theorem or_comm : forall p q, p \/ q <-> q \/ p.
Proof.
  intro p. intro q.
  split.
  - intro p_or_q.
    destruct p_or_q.
    + right.
      assumption.
    + left.
      assumption.
  - intro q_or_p.
    destruct q_or_p.
    + right.
      assumption.
    + left.
      assumption.
Qed.

Theorem and_assoc : forall p q r, (p /\ q) /\ r <-> p /\ (q /\ r).
Proof.
  intro p. intro q. intro r.
  split.
  - intro pq_r.
    destruct pq_r.
    destruct H.
    split.
    + assumption.
    + split.
      * assumption.
      * assumption.
  - intro p_qr.
    destruct p_qr.
    destruct H0.
    split.
    + split.
      * assumption.
      * assumption.
    + assumption.
Qed.

Theorem or_assoc : forall p q r, (p \/ q) \/ r <-> p \/ (q \/ r).
Proof.
  intro p. intro q. intro r.
  split.
  - intro pq_r.
    destruct pq_r.
    + destruct H.
      * left.
        assumption.
      * right.
        left.
        assumption.
    + right.
      right.
      assumption.
  - intro p_qr.
    destruct p_qr.
    + left.
      left.
      assumption.
    + destruct H.
      * left.
        right.
        assumption.
      * right.
        assumption.
Qed.

Theorem and_distrib : forall p q r,
    p /\ (q \/ r) <-> (p /\ q) \/ (p /\ r).
Proof.
  intro p. intro q. intro r.
  split.
  - intro and_or.
    destruct and_or.
    destruct H0.
    + left.
      split.
      * assumption.
      * assumption.
    + right.
      split.
      * assumption.
      * assumption.
  - intro and_or_and.
    destruct and_or_and.
    + destruct H.
      split.
      * assumption.
      * left.
        assumption.
    + destruct H.
      split.
      * assumption.
      * right.
        assumption.
Qed.

Theorem or_distrib : forall p q r, p \/ (q /\ r) <-> (p \/ q) /\ (p \/ r).
Proof.
  intro p. intro q. intro r.
  split.
  - intro or_and.
    destruct or_and.
    + split.
      * left.
        assumption.
      * left.
        assumption.
    + destruct H.
      split.
      * right.
        assumption.
      * right.
        assumption.
  - intro or_and_or.
    destruct or_and_or.
    destruct H.
    + left.
      assumption.
    + destruct H0.
      * left.
        assumption.
      * right.
        split.
        -- assumption.
        -- assumption.
Qed.

Theorem and_ident : forall p, p /\ True <-> p.
Proof.
  intro p.
  split.
  - intro p_and_true.
    destruct p_and_true.
    assumption.
  - intro pf_p.
    split.
    + assumption.
    + constructor.
Qed.

Theorem or_ident : forall p, p \/ False <-> p.
Proof.
  intro p.
  split.
  - intro p_or_false.
    destruct p_or_false.
    + assumption.
    + contradiction.
  - intro pf_p.
    left.
    assumption.
Qed.

Theorem and_neg : forall p, p /\ ~p <-> False.
Proof.
  intro p.
  split.
  - intro p_and_not_p.
    destruct p_and_not_p.
    contradiction.
  - intro false.
    contradiction.
Qed.

Theorem or_neg : forall p, p \/ ~p <-> True.
Proof.
  intro p.
  split.
  - intro p_or_not_p.
    constructor.
  - intro true.
    apply lem.
Qed.

Theorem double_neg : forall p, ~(~p) <-> p.
Proof.
  intro p.
  split.
  - intro not_not_p.
    pose proof (lem p).
    destruct H.
    + assumption.
    + contradiction.
  - intro pf_p.
    intro not_p.
    contradiction.
Qed.

Theorem and_idempotent : forall p, p /\ p <-> p.
Admitted. (* This is what you tell Coq when you don't want to prove it.
             Here, I'm leaving this as an exercise. *)

Theorem or_idempotent : forall p, p \/ p <-> p.
Admitted.

Theorem and_bound : forall p, p /\ False <-> False.
Admitted.

Theorem or_bound : forall p, p \/ True <-> True.
Admitted.

Theorem and_deMorgan : forall p q, ~(p /\ q) <-> ~p \/ ~q.
Proof.
  intro p. intro q.
  split.
  - intro not_p_and_q.
    pose proof (lem p) as lem_p.
    pose proof (lem q) as lem_q.
    destruct lem_p.
    + destruct lem_q.
      * exfalso. (* Use this when you know you have a contradiction *)
        apply not_p_and_q. (* If you're proving False, you can apply a ~(...) to
                              change the goal to prove (...). *)
        split.
        -- assumption.
        -- assumption.
      * right.
        assumption.
    + left.
      assumption.
  - intro not_p_or_not_q.
    destruct not_p_or_not_q.
    + intro p_and_q.
      destruct p_and_q.
      contradiction.
    + intro p_and_q.
      destruct p_and_q.
      contradiction.
Qed.

Theorem or_deMorgan : forall p q, ~(p \/ q) <-> ~p /\ ~q.
Proof.
  intro p. intro q.
  split.
  - intro not_p_or_q.
    split.
    + intro pf_p.
      apply not_p_or_q.
      left.
      assumption.
    + intro pf_q.
      apply not_p_or_q.
      right.
      assumption.
  - intro not_p_and_not_q.
    destruct not_p_and_not_q.
    intro p_or_q.
    destruct p_or_q.
    + contradiction.
    + contradiction.
Qed.

Theorem and_absorption : forall p q, p /\ (p \/ q) <-> p.
Admitted.

Theorem or_absorption : forall p q, p \/ (p /\ q) <-> p.
Admitted.

Theorem not_true : ~ True <-> False.
Proof.
  split.
  - intro not_true.
    contradiction.
  - intro false.
    contradiction.
Qed.

Theorem not_false : ~ False <-> True.
Proof.
  split.
  - intro not_false.
    constructor.
  - intro true.
    intro false.
    contradiction.
Qed.

Theorem problem_2_1_53 : forall p q, ~((~p /\ q) \/ (~p /\ ~q)) \/ (p /\ q) <-> p.
Proof.
  intro p. intro q.
  rewrite or_deMorgan. (* rewrite uses a proof of equivalence to rewrite the goal *)
  rewrite and_deMorgan.
  rewrite and_deMorgan.
  rewrite double_neg.
  rewrite double_neg.
  rewrite <- or_distrib. (* this variant rewrites right-to-left *)
  rewrite and_comm.
  rewrite and_neg.
  rewrite or_ident.
  rewrite or_absorption.
  reflexivity. (* this solves a reflexive equivalence goal *)
Qed.

Theorem problem_2_1_52 : forall p q, ~(p \/ ~q) \/ (~p /\ ~q) <-> ~p.
Admitted. (* Exercise *)

(* Section 2.2 *)

Theorem implication : forall (p q : Prop), (p -> q) <-> (~p \/ q).
(* Note that Coq allows us to say what we're quantifying over. Above, it could
   always infer it. But, (->) is overloaded, so we need to tell Coq. *)
Proof.
  intro p. intro q.
  split.
  - intro implic.
    pose proof (lem p) as lem_p.
    destruct lem_p.
    + right.
      (* Here, we know (p -> q) and we're trying to prove q. If we `apply implic`, then
         our goal will reduce to just p. *)
      apply implic.
      assumption.
    + left.
      assumption.
  - intro or.
    intro pf_p. (* we can assume p here, because we're proving (p -> q) *)
    destruct or.
    + contradiction.
    + assumption.
Qed.

Theorem neg_implication : forall (p q : Prop), ~(p -> q) <-> p /\ ~q.
Admitted.

Theorem contrapositive : forall (p q : Prop), (p -> q) <-> (~q -> ~p).
Proof.
  intro p. intro q.
  rewrite implication.
  rewrite implication.
  rewrite double_neg.
  rewrite or_comm.
  reflexivity.
Qed.

(* Section 3.2 *)

Theorem forall_deMorgan : forall {A} {P : A -> Prop}, ~(forall x, P x) <-> exists y, ~(P y).
Proof.
  intro A. intro P.
  split.
  - intro not_forall.
    rewrite <- double_neg.
    intro not_exists.
    apply not_forall.
    intro x.
    rewrite <- double_neg.
    intro not_pred.
    apply not_exists.
    exists x. (* This is how we choose the value of an existential variable. *)
    assumption.
  - intro ex.
    destruct ex. (* You can use destruct to get a given existential variable. *)
    intro all.
    specialize (all x). (* instantiate a forall *)
    contradiction.
Qed.

Theorem exists_deMorgan : forall {A} {P : A -> Prop}, ~(exists x, P x) <-> forall y, ~(P y).
Proof.
  intro A. intro P.
  split.
  - intro not_exists.
    intro y.
    intro pred_y.
    apply not_exists.
    exists y.
    assumption.
  - intro all.
    intro ex.
    destruct ex.
    specialize (all x).
    contradiction.
Qed.

(* Section 3.3 *)

(* There exists a positive integer m such that for all positive integers n, m <= n. *)
Theorem example_3_3_5 : exists m, m > 0 /\ forall n, n > 0 -> m <= n.
 
(* Section 4.1 *)
Definition even n := exists k, n = 2 * k.
Definition odd n  := exists k, n = 2 * k + 1.

Definition prime n := n > 1 /\ forall r s, (r > 0 /\ s > 0 /\ n = r * s) -> (r = n \/ s = n).
Definition composite n := exists r s, r > 0 /\ s > 0 /\ n = r * s /\ 1 < r < n /\ 1 < s < n.

Theorem two_prime : prime 2.
Proof.
  unfold prime. (* This unfolds a definition in the goal. *)
  split.
  - omega.
  - intro r.
    intro s.
    intro Hyp.
    destruct Hyp.
    destruct H0.
    destruct r. (* either r is 0 or greater than 0. *)
    + omega.
    + destruct s.
      * omega.
      * destruct r.
        -- destruct s.
           ++ omega.
           ++ destruct s.
              ** omega.
              ** omega.
        -- destruct s.
           ++ omega.
           ++ simpl in H1.
              rewrite <- plus_n_Sm in H1.
              inversion H1.
Qed.
(* That proof got a little ugly, because we had to look at all possibilities for r and s
   below two. *)

Theorem six_composite : composite 6.
Proof.
  unfold composite.
  exists 2.
  exists 3.
  split.
  - omega.
  - split.
    + omega.
    + split.
      * omega.
      * split.
        -- omega.
        -- omega.
Qed.

(* Coq can do induction! *)
Theorem even_or_odd : forall n, even n \/ odd n.

Theorem not_odd__even : forall n, ~ (odd n) <-> even n.
Proof.
  intro n.
  split.
  * intro not_odd.
    pose proof (even_or_odd n).
    destruct H.
    - assumption.
    - contradiction.
  * intro pf_even.
    intro pf_odd.
    destruct pf_even.
    destruct pf_odd.
    subst. (* This performs all substitutions Coq can find. *)
    omega.
Qed.

Theorem problem_4_1_28 : forall n, odd n -> odd (n * n).
Proof.
  intro n. intro Hodd.
  unfold odd in *. (* unfold everywhere *)
  destruct Hodd.
  (* (2x+1)(2x+1) = 4x^2 + 4x + 1 = 2(2*x^2 + 2*x) + 1 *)
  exists (2 * x * x + 2 * x).
  subst.
  ring. (* like omega, but works better with multiplication *)
Qed.

Theorem problem_4_1_27 : forall n m, (odd m /\ odd n) -> odd (m + n).
Admitted.

Theorem problem_4_1_30 : forall m, even m -> odd (3 * m + 5).
Admitted.

Inductive ltpair : (nat * nat) -> (nat * nat) -> Prop :=
| lt_left : forall a b c d, a < c -> ltpair (a,b) (c,d)
| lt_right : forall a b d, b < d -> ltpair (a,b) (a,d).

Program Fixpoint Ack m n { measure (m,n) (ltpair) } :=
  match m with
  | 0 => n + 1
  | S m' => match n with
            | 0 => Ack m' 1
            | S n' => Ack m' (Ack m n')
            end
  end.
Next Obligation.
  apply lt_left.
  omega.
Qed.
Next Obligation.
  apply lt_right.
  omega.
Qed.
Next Obligation.
  apply lt_left.
  omega.
Qed.
Next Obligation.
Admitted. (* Not enough time to figure this one out. *)
