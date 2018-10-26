Require Import Arith Nat Omega.
Require Import SetoidClass.
Set Implicit Arguments.


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

Notation  "[ z ; x ~= y ]" := (@mod_eq z x y) (at level 10, no associativity).

Instance add_proper_mod z : Proper (mod_eq z ==> mod_eq z ==> mod_eq z) Nat.add.
Proof.
  intros x x' Hx y y' Hy.
  rewrite mod_eq_iff in *.
  destruct z; try reflexivity.
  rewrite (Nat.add_mod x y); auto.
  rewrite (Nat.add_mod x' y'); auto.
Qed.

Lemma mul_mod_0_r : forall k x, mod_eq k (x * k) 0.
Proof.
  intros.
  constructor.
  destruct k; auto.
  intros.
  rewrite Nat.mod_mul; auto.
  simpl.
  omega.
Qed.

Lemma mul_mod_0_l : forall k x, mod_eq k (k * x) 0.
Proof.
  intros.
  rewrite Nat.mul_comm.
  apply mul_mod_0_r.
Qed.

Lemma mod_same_0 : forall k, mod_eq k k 0.
Proof.
  intro.
  rewrite <- (Nat.mul_1_r k) at 2.
  apply mul_mod_0_l.
Qed.

Instance add_proper_mul z : Proper (mod_eq z ==> mod_eq z ==> mod_eq z) Nat.mul.
Proof.
  intros x x' Hx y y' Hy.
  rewrite mod_eq_iff in *.
  destruct z; try reflexivity.
  rewrite (Nat.mul_mod x y); auto.
  rewrite (Nat.mul_mod x' y'); auto.
Qed.

Lemma mod_add_self : forall x k, k <> 0 -> mod_eq k x (x + k).
Proof.
  intros x k Hk.
  rewrite mod_same_0 at 2.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma mod_sub_self : forall x k, k <> 0 -> k <= x -> mod_eq k x (x - k).
Proof.
  intros x k Hk.
  destruct_divmod x k Hk m p.
  intro Hle.
  destruct m; try omega.
  replace (k * S m + p - k) with (k * m + p).
  - repeat rewrite mul_mod_0_l.
    reflexivity.
  - clear.
    rewrite Nat.mul_succ_r.
    set (k * m) as x.
    omega.
Qed.

Lemma mod_add_unit_unique : forall k a b,
    k <> 0 ->
    mod_eq k (a + b) a -> mod_eq k b 0.
Proof.
  intros k a b Hk.
  destruct_divmod a k Hk n p.
  destruct_divmod b k Hk m q.
  rewrite mul_mod_0_l.
  rewrite mul_mod_0_l.
  simpl.
  simpl.
  destruct (le_gt_dec k (p + q)) as [Hle | Hgt].
  - rewrite (mod_sub_self Hk Hle).
    repeat rewrite mod_eq_iff.
    rewrite (Nat.mod_small p); auto.
    rewrite (Nat.mod_small q); auto.
    rewrite (Nat.mod_small (p + q - k)); omega.
  - repeat rewrite mod_eq_iff.
    rewrite (Nat.mod_small p); auto.
    rewrite (Nat.mod_small q); auto.
    rewrite (Nat.mod_small 0); try omega.
    rewrite (Nat.mod_small (p + q)); omega.
Qed.

Lemma mod_sub_unit_unique : forall k a b,
    k <> 0 ->
    b <= a ->
    mod_eq k (a - b) a -> mod_eq k b 0.
Proof.
  intros k a b Hk.
  destruct_divmod b k Hk m q.
  rewrite <- (Nat.add_0_l (a - _)) at 1.
  rewrite <- (mul_mod_0_l k (S m)).
  intro Hle.
  replace (k * (S m) + (a - (k * m + q))) with (a + (k - q)).
  - intro H.
    apply mod_add_unit_unique in H; auto.
    repeat rewrite (mul_mod_0_l); auto.
    simpl.
    rewrite mod_eq_iff in *.
    rewrite (Nat.mod_small q); auto.
    rewrite (Nat.mod_small 0) in *; try omega.
    destruct q; auto.
    rewrite Nat.mod_small in H; omega.
  - rewrite Nat.add_sub_assoc; try omega.
    rewrite Nat.add_sub_assoc; try omega.
    rewrite Nat.mul_succ_r.
    omega.
Qed.

Lemma mod_add_inj : forall k x y y',
    k <> 0 ->
    mod_eq k (x + y) (x + y') -> mod_eq k y y'.
Proof.
  assert (forall k x y y',
             k <> 0 -> y <= y' ->
             mod_eq k (x + y) (x + y') -> mod_eq k y y') as Hhelper. {
    intros until y'.
    intros Hk Hle.
    set (y' - y) as w.
    replace y' with (y + w) in *; try omega.
    rewrite Nat.add_assoc.
    intro H.
    symmetry in H.
    apply mod_add_unit_unique in H; auto.
    rewrite H.
    rewrite Nat.add_0_r.
    reflexivity.
  }

  intros k x y y' Hk.
  destruct (Nat.le_ge_cases y y') as [Hle | Hle]; eauto.
  specialize (Hhelper k x y' y Hk Hle).
  intro H.
  symmetry.
  apply Hhelper.
  now symmetry.
Qed.

Lemma mod_sub_inj : forall k x y y',
    k <> 0 ->
    y <= x -> y' <= x ->
    mod_eq k (x - y) (x - y') -> mod_eq k y y'.
Proof.
    assert (forall k x y y',
               k <> 0 ->
               y' <= x ->
               y <= y' ->
             mod_eq k (x - y) (x - y') -> mod_eq k y y') as Hhelper. {
    intros until y'.
    intros Hk Hlex Hley.
    set (y' - y) as w.
    replace y' with (y + w) in *; try omega.
    rewrite Nat.sub_add_distr.
    intro H.
    symmetry in H.
    apply mod_sub_unit_unique in H; try omega.
    rewrite H.
    rewrite Nat.add_0_r.
    reflexivity.
  }

    intros until y'.
    intros Hk Hley Hley'.
    destruct (Nat.le_ge_cases y y') as [Hle | Hle]; eauto.
    specialize (Hhelper k x y' y Hk Hley Hle).
    intro H.
    symmetry.
    apply Hhelper.
    now symmetry.
Qed.
