Require Import Arith Nat Omega.
Require Import SetoidClass.
Set Implicit Arguments.

Lemma sub_sub_add : forall x y z, z <= y -> (x - (y - z)) = x + z - y.
Proof.
  intros.
  omega.
Qed.

Ltac destruct_divmod x y Hypos d m :=
  let Hmlt := fresh "H" m "lt" in
  rewrite (@Nat.div_mod x y Hypos) in *;
  set (x / y) as d;
  set (x mod y) as m;
  assert (m < y) as Hmlt;
  [ unfold m; apply (@Nat.mod_upper_bound x y Hypos) |
    clearbody d; clearbody m].
Ltac destruct_add_mod y H :=
  match goal with
  | |- ?x =>
    multimatch x with
    | context a [(?a + ?b) mod y] =>
      progress (rewrite (Nat.add_mod a b y H);
                repeat rewrite (Nat.mod_mod _ _ H))
    end
  end.

Lemma mod_mul_r : forall x y, y <> 0 -> (x * y) mod y = 0.
Proof.
  intros.
  now apply Nat.mod_mul.
Qed.

Lemma mod_mul_l : forall x y, y <> 0 -> (y * x) mod y = 0.
Proof.
  intros.
  rewrite Nat.mul_comm.
  now apply mod_mul_r.
Qed.



Ltac simpl_mod y Hy :=
  repeat destruct_add_mod y Hy;
  repeat rewrite (@mod_mul_l _ _ Hy);
  repeat (rewrite Nat.add_0_l || rewrite Nat.add_0_r ||
          rewrite (@Nat.mod_mod _ y Hy) ||
          rewrite <- (@Nat.add_mod _ _ y Hy)).

Lemma mod_eq_add_equal : forall x y z, z <> 0 ->
                   x mod z = y mod z -> exists a b, z * a + x = z * b + y.
Proof.
  intros x y z.
  intros Hz.
  destruct_divmod x z Hz x' p.
  destruct_divmod y z Hz y' q.
  clear x y.
  simpl_mod z Hz.
  rewrite (Nat.mod_small p z Hplt).
  rewrite (Nat.mod_small q z Hqlt).
  intro; subst.
  exists (y' - x'), (x' - y').
  repeat rewrite Nat.add_assoc.
  repeat rewrite <- Nat.mul_add_distr_l.
  rewrite Nat.add_cancel_r.
  rewrite Nat.mul_cancel_l; auto.
  omega.
Qed.


Inductive mod_eq : nat -> nat -> nat -> Prop :=
| mod_eq_intro : forall z x y, x mod z = y mod z -> mod_eq z x y.
Lemma mod_eq_iff : forall z x y,
    mod_eq z x y <-> x mod z = y mod z.
Proof.
  intros.
  split.
  - inversion 1. subst. auto.
  - now constructor.
Qed.

Definition mod_eq_dec : forall z x y, {mod_eq z x y} + {~mod_eq z x y}.
Proof.
  intros.
  destruct (Nat.eq_dec (x mod z) (y mod z)); [left | right]; now rewrite mod_eq_iff.
Qed.

Instance mod_eq_equiv z : Equivalence (mod_eq z).
Proof.
  constructor; autounfold; intros; rewrite mod_eq_iff in *; auto.
  congruence.
Qed.

Notation "[ x ~= y ] / z" := (@mod_eq z x y) (at level 100, no associativity).
Instance add_proper_mod z : Proper (mod_eq z ==> mod_eq z ==> mod_eq z) Nat.add.
Proof.
  intros x x' Hx y y' Hy.
  rewrite mod_eq_iff in *.
  destruct z; try reflexivity.
  rewrite (Nat.add_mod x y); auto.
  rewrite (Nat.add_mod x' y'); auto.
Qed.

Lemma mul_modeq_0_r : forall x k, mod_eq k (x * k) 0.
Proof.
  intros.
  constructor.
  destruct k; auto.
  intros.
  rewrite Nat.mod_mul; auto.
  simpl.
  omega.
Qed.
Lemma mul_modeq_0_l : forall x k, mod_eq k (k * x) 0.
Proof.
  intros.
  rewrite Nat.mul_comm.
  apply mul_modeq_0_r.
Qed.

Lemma modeq_same_0 : forall k, mod_eq k k 0.
Proof.
  intro.
  rewrite <- (Nat.mul_1_r k) at 2.
  apply mul_modeq_0_l.
Qed.

Instance add_proper_mul z : Proper (mod_eq z ==> mod_eq z ==> mod_eq z) Nat.mul.
Proof.
  intros x x' Hx y y' Hy.
  rewrite mod_eq_iff in *.
  destruct z; try reflexivity.
  rewrite (Nat.mul_mod x y); auto.
  rewrite (Nat.mul_mod x' y'); auto.
Qed.

Lemma sub_mod_modeq_0 : forall x k, mod_eq k (x - x mod k) 0.
Proof.
  constructor.
  destruct k; auto.
  assert (S k <> 0) as Hnz; auto.
  destruct_divmod x (S k) Hnz m p.
  simpl_mod (S k) Hnz.
  rewrite (Nat.mod_small p); auto.
  rewrite Nat.add_sub.
  simpl_mod (S k) Hnz.
  simpl.
  omega.
Qed.

  
Lemma mod_sub_exact : forall x y, y <= x ->  (x - y) mod y = x mod y.
Proof.
  intros.
  destruct y; auto.
  set (S y) as Sy in *.
  assert (Sy <> 0) as HSy; try now unfold Sy.
  clearbody Sy.
  revert H.
  destruct_divmod x Sy HSy m p.
  destruct m; simpl.
  - rewrite Nat.mul_0_r.
    simpl.
    intuition.
  - intro H.
    rewrite Nat.add_sub_swap.
    + rewrite <- (Nat.mul_1_r Sy) at 2.
      rewrite <- Nat.mul_sub_distr_l.
      simpl.
      rewrite Nat.sub_0_r.
      simpl_mod Sy HSy.
      reflexivity.
    + rewrite Nat.mul_succ_r.
      apply le_plus_r.
Qed.

Lemma mod_add_inj : forall z x y y', mod_eq z (x + y) (x + y') -> mod_eq z y y'.
Proof.
  intro z.
  destruct z; auto. {
    intros.
    rewrite mod_eq_iff.
    reflexivity.
  }
  set (S z) as Sz in *.
  assert (Sz <> 0) as HSz; try now unfold Sz.
  clearbody Sz.

  cut (forall x y y', y < y' -> mod_eq Sz (x + y) (x + y') -> mod_eq Sz y y').
  - intro Hr.
    intros.
    decompose sum (Nat.lt_total y y').
    + apply Hr with (x := x); auto.
    + subst.
      reflexivity.
    + symmetry.
      apply Hr with (x := x); auto.
      symmetry.
      assumption.
  - intros until y'.
    intros Hlt Heqm.
    set (y' - y) as w.
    replace y' with (y + w) in *; try omega.
    rewrite mod_eq_iff in *.
    revert Heqm.
    rewrite Nat.add_assoc.
    destruct_divmod w Sz HSz m p.
    simpl_mod Sz HSz.
    intro H.
    replace p with 0; auto.
    revert H.
    destruct_divmod (x + y) Sz HSz n q.
    simpl_mod Sz HSz.
    destruct (le_gt_dec Sz (q + p)).
    + intro Heq.
      rewrite <- (@mod_sub_exact (q + p)) in Heq; auto.
      rewrite (Nat.mod_small q) in Heq; auto.
      rewrite Nat.mod_small in Heq; omega.
    + repeat rewrite Nat.mod_small; auto.
      intuition.
Qed.

Lemma mod_sub : forall x y k,
    k <> 0 ->
    y <= x ->
    mod_eq k (x - y) (x + (k - y mod k)).
Proof.
  intros x y k Hk.
  set (x - y) as w.
  intro H.
  replace x with (y + w); try omega.
  destruct_divmod w k Hk m p.
  rewrite mul_modeq_0_l.
  simpl.
  replace (y + p + (k - y mod k)) with (p + k + (y - y mod k)).
  - rewrite modeq_same_0 at 2.
    rewrite sub_mod_modeq_0.
    repeat rewrite Nat.add_0_r.
    reflexivity.
  - repeat rewrite Nat.add_sub_assoc; try omega.
    + set (Nat.mod_upper_bound y k Hk).
      omega.
    + now apply Nat.mod_le.
Qed.

Lemma mod_sub_inj : forall x y y' k,
    k <> 0 ->
    y <= x -> y' <= x ->
    mod_eq k (x - y) (x - y') -> mod_eq k y y'.
Proof.
  intros until k.
  intros Hk Hy Hy'.
  rewrite (@mod_sub x y k); auto.
  rewrite (@mod_sub x y' k); auto.
  intro H.
  apply mod_add_inj in H.
  rewrite mod_eq_iff in *.
  destruct (Nat.eq_dec (y mod k) 0) as [Heq | Hneq].
  - rewrite Heq in *.
    rewrite Nat.sub_0_r, Nat.mod_same in H; auto.
    destruct (Nat.eq_dec (y' mod k) 0); auto.
    rewrite Nat.mod_small in H; try omega.
    cut (k <= y' mod k); try omega. 
    cut (y' mod k < k); try omega.
    now apply Nat.mod_upper_bound.
  - destruct (Nat.eq_dec (y' mod k) 0) as [Heq' | Hneq'].
    ++ rewrite Heq' in *.
       rewrite Nat.sub_0_r, Nat.mod_same in H; auto.
       rewrite Nat.mod_small in H; try omega.
       cut (k <= y mod k); try omega.
       cut (y mod k < k); try omega.
       now apply Nat.mod_upper_bound.
    ++ rewrite (Nat.mod_small (k - y mod k)) in H; try omega.
       rewrite (Nat.mod_small (k - y' mod k)) in H; try omega.
       assert (y mod k < k); eauto using Nat.mod_upper_bound.
       assert (y' mod k < k); eauto using Nat.mod_upper_bound.
       omega.
Qed.

