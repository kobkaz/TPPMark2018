Require Import List.
Require Import Arith Omega.
Require Import SetoidClass.
Require Import Wf_nat.

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

Class Decidable A :=
  {
    eq_dec : forall (x y : A), {x = y} + {x <> y}
  }.

Instance nat_Decidable : Decidable nat.
constructor.
decide equality.
Defined.

Section ListUtil.
  Variable A B : Type.
  Context `{DA : Decidable A}.

  Definition In_dec : forall (x : A) (xs : list A), {In x xs} + {~In x xs}.
    intro x.
    induction xs as [| a xs]; simpl; auto.
    destruct IHxs; auto.
    destruct (eq_dec a x); tauto.
  Defined.
             
  Definition NoDup_dec : forall xs : list A, {NoDup xs} + {~NoDup xs}.
  induction xs as [| x xs].
  - left. apply NoDup_nil.
  - destruct IHxs.
    + destruct (In_dec x xs).
      * right.
        now inversion 1.
      * left.
        now constructor.
    + right.
      now inversion 1.
  Defined.

  Fixpoint map_index_rec
             (f : nat -> A -> B) (xs : list A) (i : nat) : list B :=
    match xs with
    | nil => nil
    | x :: xs' => f i x :: map_index_rec f xs' (S i)
    end.
  
  Definition map_index (f : nat -> A -> B) (xs : list A) : list B :=
    map_index_rec f xs 0.


  Lemma map_index_equation : forall f xs,
      map_index f xs =
      match xs with
      | nil => nil
      | x :: xs' => f 0 x :: map_index (fun i => f (S i)) xs'
      end.
  Proof.
    intros f xs.
    unfold map_index.
    generalize 0 as n.
    induction xs as [| x xs].
    - auto.
    - intro n.
      simpl.
      f_equal.
      rewrite (IHxs (S n)).
      destruct xs as [| y xs].
      + auto.
      + simpl.
        reflexivity.
  Qed.
      
  Lemma map_index_length : forall f xs, length (map_index f xs) = length xs.
  Proof.
    intros f xs.
    revert f.
    induction xs.
    - auto.
    - intro f.
      rewrite map_index_equation.
      simpl.
      rewrite IHxs.
      reflexivity.
  Qed.
  
  Lemma map_index_nth : forall f xs n db da,
      n < length xs -> nth n (map_index f xs) db = f n (nth n xs da).
  Proof.
    intros until da.
    revert f n.
    induction xs as [| x xs].
    - intros f n Hlt.
      inversion Hlt.
    - destruct n as [| n].
      + reflexivity.
      + intro Hlt.
        rewrite map_index_equation.
        simpl.
        rewrite IHxs; auto.
        simpl in Hlt.
        omega.
  Qed.

End ListUtil.

Section NthMod.
  Variable A : Type.
  Definition nth_mod (n: nat) (xs: list A) (d : A) : A :=
    nth (n mod length xs) xs d.

  Lemma nth_mod_indep : forall n xs d d',
      xs <> nil ->
      nth_mod n xs d = nth_mod n xs d'.
  Proof.
    intros until d'. intro H.
    unfold nth_mod.
    apply nth_indep.
    apply Nat.mod_upper_bound.
    destruct xs; auto.
    discriminate.
  Qed.
End NthMod.

Definition Valid xs : Prop :=
  xs <> nil /\
    (forall m n, m + nth_mod m xs 0 = n + nth_mod n xs 0 -> m = n).


Definition Valid' xs : Prop :=
  xs <> nil /\ NoDup (map_index (fun i x => (i + x) mod length xs) xs).

Ltac cut_hyp H :=
  refine ((fun p pq => pq (H p)) _ _); clear H; [| intro H].


Lemma Valid_iff: forall xs, Valid xs <-> Valid' xs.
Proof.
  destruct xs as [| x xs]. {
    split; inversion 1; tauto.
  }
  unfold Valid, Valid'.
  assert (forall P Q R, Q <-> R -> P/\Q <-> P/\R) as help; [intuition |].
  apply help. clear help.
  unfold nth_mod.
  remember (length (x :: xs)) as len.
  assert (len <> 0) as Hlen. {
    subst.
    simpl.
    auto.
  }
  
  rewrite NoDup_nth with (d:=x) .
  rewrite map_index_length, <- Heqlen.

  split; intro H.
  - intros p q Hplt Hqlt.
    repeat (rewrite map_index_nth with (da := 0); try omega).
    intro Heq.
    apply mod_eq_add_equal in Heq; auto.
    destruct Heq as (a & b & Heq).
    specialize (H (len * a + p) (len * b + q)).
    cut_hyp H.
    + simpl_mod len Hlen.
      repeat (rewrite Nat.mod_small; [| assumption]).
      omega.
    + apply f_equal with (f := (fun x => x mod len)) in H.
      revert H.
      simpl_mod len Hlen.
      repeat (rewrite Nat.mod_small; [| assumption]).      
      auto.
  - intros m n.
    destruct_divmod m len Hlen s p. clear m.
    destruct_divmod n len Hlen t q. clear n.
    
    simpl_mod len Hlen.
    
    rewrite (Nat.mod_small _ _ Hplt).
    rewrite (Nat.mod_small _ _ Hqlt).
    specialize (H p q Hplt Hqlt).
    repeat (rewrite map_index_nth with (da := x) in H; [| omega]).
    intro Heq.
    cut_hyp H.
    + apply f_equal with (f := fun x => x mod len) in Heq.
      revert Heq.
      simpl_mod len Hlen.
      repeat (rewrite nth_indep with (d := 0) (d' := x); try omega).
      auto.
    + subst.
      replace t with s; auto.
      rewrite Nat.add_cancel_r in Heq.
      rewrite Nat.add_cancel_r in Heq.
      rewrite Nat.mul_cancel_l in Heq; auto.
Qed.


Definition is_valid' xs : {Valid' xs} + {~Valid' xs}.
  destruct xs as [| x xs].
  right.
  - unfold Valid'.
    tauto.
  - unfold Valid'.
    destruct
      (NoDup_dec 
         (map_index (fun i x => (i + x) mod length (x :: xs)) (x :: xs))).
    + left.
      split; auto.
      discriminate.
    + right.
      tauto.
Defined.


Section NDL.
  Variable A : Type.
  Context `{DA : Decidable A}.

  Record NDL :=
    {
      elems :> list A;
      nodup : NoDup elems
    }.
  Hint Resolve nodup.

  Definition nd_In x (xs: NDL) := In x (elems xs).
  Lemma nd_In_In : forall x xs, nd_In x xs <-> In x xs.
  Proof.
    intros.
    reflexivity.
  Qed.
  
  Definition same_set (xs ys : NDL) : Prop := forall x,
      nd_In x xs <-> nd_In x ys.


  Global Program Instance NDL_Setoid : Setoid NDL := {| equiv := same_set |}.
  Next Obligation.
    constructor; autounfold; unfold same_set.
    - reflexivity.
    - intros xs ys H.
      intro x.
      now symmetry.
    - intros xs ys zs.
      intros Hxy Hyz.
      intro x.
      now rewrite Hxy.
  Qed.


  Global Instance nd_in_proper :
    Proper (eq ==> equiv  ==> equiv) nd_In.
  Proof.
    simpl.
    intros x x' Heqx xs xs' Heqxs'.
    unfold same_set in *.
    subst.
    unfold nd_In in *.
    rewrite Heqxs'.
    reflexivity.
  Qed.
  
  Definition nd_included (xs ys : NDL) : Prop :=
    forall x, nd_In x xs -> nd_In x ys.

  Global Instance nd_included_proper :
    Proper (equiv ==> equiv ==> equiv) nd_included.
  Proof.
    simpl.
    intros xs xs' Heqxs ys ys' Heqys.
    unfold nd_included.
    intuition.
    - specialize (H x).
      rewrite Heqxs, Heqys in H.
      auto.
    - specialize (H x).
      rewrite <- Heqxs, <- Heqys in H.
      auto.
  Qed.
  
  Definition NDL_iff (P : A -> Prop) (xs : NDL) := forall x, nd_In x xs <-> P x.

  Definition count (xs : NDL) : nat := length (elems xs).
  Lemma nd_count_length : forall xs, count xs = length xs.
  Proof.
    reflexivity.
  Qed.

  Global Instance count_proper : Proper (equiv ==> eq) count.
  Proof.
    simpl.
    intros [xs NDxs] [ys NDys].
    unfold count.
    unfold same_set.
    unfold nd_In.
    simpl.
    revert ys NDys.
    induction NDxs.
    - intros.
      destruct ys; auto.
      specialize (H a).
      simpl in H.
      tauto.
    - intros ys Hys HIn.
      simpl in *.
      assert (In x ys) as HInx. {
        rewrite <- HIn.
        auto.
      }
      apply in_split in HInx.
      destruct HInx as (yl & yr & Heqys). subst.
      simpl.
      specialize (IHNDxs (yl ++ yr)).
      rewrite app_length in *.
      simpl.
      rewrite IHNDxs; auto.
      + apply NoDup_remove in Hys.
        tauto.
      + intro y.
        specialize (HIn y).
        split; intro HIny.
        * intuition; subst; try tauto.
          rewrite in_app_iff in *.
          simpl in *.
          intuition.
          now subst.
        * assert (x <> y) as HNe. {
            intro.
            subst.
            now apply NoDup_remove in Hys.
          }
          rewrite in_app_iff in *.
          simpl in *.
          tauto.
  Qed.

  Program Definition nd_add (x : A) (xs : NDL) : NDL :=
    if In_dec x xs
    then xs
    else {| elems := cons x xs |}.
  Next Obligation.
    now constructor.
  Qed.

  Lemma nodup_app :
    forall (xs ys : list A),
      NoDup xs -> NoDup ys -> (forall x, In x xs -> ~In x ys) ->
      NoDup (xs ++ ys).
  Proof.
      intros xs ys Hxs Hys Hnin.
      induction xs.
      - now simpl.
      - simpl.
        constructor.
        + rewrite in_app_iff.
          intros [HInx | HIny].
          * now inversion Hxs.
          * apply (Hnin a); simpl; auto.
        + apply IHxs.
          * now inversion Hxs.
          * intros x HInx.
            apply Hnin.
            simpl. auto.
  Qed.
  Hint Resolve nodup_app.

  Lemma nd_add_in : forall x xs a, nd_In a (nd_add x xs) <-> x = a \/ nd_In a xs.
  Proof.
    intros.
    unfold nd_add.
    destruct In_dec.
    - intuition. subst. auto.
    - simpl.
      reflexivity.
  Qed.

  Global Instance nd_add_proper : Proper (eq ==> equiv ==> equiv) nd_add.
  Proof.
    simpl.
    intros x y Hxy xs ys Heqv.
    subst.
    unfold same_set in *.
    intro z.
    repeat rewrite nd_add_in.
    rewrite Heqv.
    reflexivity.
  Qed.
    
  Lemma nodup_filter : forall f (xs : list A), NoDup xs -> NoDup (filter f xs).
  Proof.
    intros f xs H.
    induction xs; simpl; auto.
    inversion H. subst. intuition.
    destruct (f a); simpl; auto.
    constructor; auto.
    rewrite filter_In.
    tauto.
  Qed.
  Hint Resolve nodup_filter.

  Lemma filter_length : forall f (xs : list A), length (filter f xs) <= length xs.
  Proof.
    intros.
    induction xs; simpl; auto.
    destruct (f a); simpl; auto.
    omega.
  Qed.

  Program Definition nd_filter (f : A -> bool) (xs : NDL) : NDL :=
    {| elems := filter f xs |}.
  Lemma nd_filter_in : forall f xs x,
      nd_In x (nd_filter f xs) <-> nd_In x xs /\ f x = true.
  Proof.
    intros.
    unfold nd_In, nd_filter.
    simpl.
    apply filter_In.
  Qed.

  Global Instance nd_filter_propre : Proper (eq ==> equiv ==> equiv) nd_filter.
  Proof.
    simpl.
    intros f f' Heqf xs xs' Heqxs.
    subst.
    intro x.
    repeat rewrite nd_filter_in.
    rewrite Heqxs.
    reflexivity.
  Qed.

  Program Definition nd_intersection (xs ys : NDL) : NDL :=
    nd_filter (fun x => if In_dec x ys then true else false) xs.

  Lemma nd_intersection_in : forall xs ys a, nd_In a (nd_intersection xs ys) <->
                                             nd_In a xs /\ nd_In a ys.
  Proof.
    intros.
    cbn.
    rewrite filter_In.
    destruct In_dec; try tauto.
    intuition.
  Qed.

  Global Instance nd_intersection_proper :
    Proper (equiv ==> equiv ==> equiv) nd_intersection.
  Proof.
    simpl.
    intros xs xs' Heqx ys ys' Heqy.
    intro x.
    repeat rewrite nd_intersection_in.
    rewrite Heqx, Heqy.
    reflexivity.
  Qed.

  Lemma nd_intersection_comm :
    forall xs ys, nd_intersection xs ys == nd_intersection ys xs.
  Proof.
    intros.
    intro x.
    repeat rewrite nd_intersection_in.
    tauto.
  Qed.

  Lemma nd_intersection_included :
    forall xs ys, nd_included xs ys ->
                  nd_intersection xs ys == xs.
  Proof.
    intros.
    intro x.
    rewrite nd_intersection_in.
    specialize (H x).
    intuition.
  Qed.
  
  Program Definition nd_diff (xs ys : NDL) : NDL :=
    nd_filter (fun x => if In_dec x ys then false else true) xs.

  Lemma nd_diff_in : forall xs ys a, nd_In a (nd_diff xs ys) <->
                                             nd_In a xs /\ ~nd_In a ys.
  Proof.
    intros.
    cbn.
    rewrite filter_In.
    destruct In_dec; try tauto.
    intuition.
  Qed.

  Global Instance nd_diff_proper :
    Proper (equiv ==> equiv ==> equiv) nd_diff.
  Proof.
    simpl.
    intros xs xs' Heqx ys ys' Heqy.
    intro x.
    repeat rewrite nd_diff_in.
    rewrite Heqx, Heqy.
    reflexivity.
  Qed.

  Lemma nd_diff_count : forall xs ys,
      count (nd_diff xs ys) = count xs - count (nd_intersection xs ys).
  Proof.
    intros.
    unfold count.
    destruct xs as [xs xs_prf].
    cbn.
    clear xs_prf.
    induction xs as [| x xs]; auto.
    simpl filter.
    destruct In_dec; auto.
    simpl length.
    rewrite IHxs.
    rewrite Nat.sub_succ_l; auto.
    apply filter_length.
  Qed.
  
  
  Program Definition nd_union (xs ys : NDL) : NDL :=
    {| elems :=
         nd_diff xs ys ++ ys
    |}.
  Next Obligation.
    apply nodup_app; auto.
    intro x.
    rewrite filter_In.
    destruct In_dec; try tauto.
    now destruct 1. 
  Qed.

  Lemma nd_union_in : forall xs ys a, nd_In a (nd_union xs ys) <-> nd_In a xs \/ nd_In a ys.
  Proof.
    intros.
    unfold nd_union.
    simpl.
    unfold nd_In. simpl.
    rewrite in_app_iff, filter_In.
    intuition.
    destruct In_dec; tauto.
  Qed.
  
  Global Instance nd_union_proper :
    Proper (equiv ==> equiv ==> equiv) nd_union.
  Proof.
    simpl.
    intros xs xs' Heqx ys ys' Heqy.
    intro x.
    repeat rewrite nd_union_in.
    rewrite Heqx, Heqy.
    reflexivity.
  Qed.

  Lemma nd_union_count: forall xs ys,
      count (nd_union xs ys) =
      count xs + count ys - count (nd_intersection xs ys).
  Proof.
    intros.
    replace (count (nd_union xs ys)) with (count (nd_diff xs ys) + count ys).
    - rewrite nd_diff_count.
      rewrite Nat.add_sub_swap; auto.
      apply filter_length.
    - unfold nd_union, count.
      simpl.
      rewrite app_length.
      reflexivity.
  Qed.

  Program Definition empty : NDL := {| elems := nil |}.
  Next Obligation.
    constructor.
  Qed.
  
  Lemma empty_in : forall x, ~In x empty.
  Proof.
    intros.
    now simpl.
  Qed.

  Lemma count_0_empty : forall xs, count xs = 0 <-> xs == empty.
  Proof.
    intros.
    split; intro H.
    - destruct xs as [xs Hnd].
      unfold count in *.
      destruct xs as [| x xs]; simpl in *; try discriminate.
      unfold same_set, nd_In. simpl.
      tauto.
    - rewrite H.
      reflexivity.
  Qed.

  Fixpoint nd_union_many (xss : list NDL) : NDL :=
    match xss with
    | nil => empty
    | xs :: xss' => nd_union xs (nd_union_many xss')
    end.

  Lemma nd_union_many_in :
    forall xss a, nd_In a (nd_union_many xss) <-> (exists xs, In xs xss /\ nd_In a xs).
  Proof.
    induction xss as [| xs xss].
    - simpl.
      intros.
      intuition.
      now destruct H.
    - intro a.
      simpl.
      rewrite nd_union_in.
      rewrite IHxss.
      split.
      + intros [HIn | [xs' Hxs']].
        * exists xs.
          tauto.
        * exists xs'.
          tauto.
      + intros [xs' Hxs'].
        destruct Hxs' as [[Heq | HIn] HIna].
        * subst.
          auto.
        * eauto.
  Qed.

  

End NDL.
Arguments empty {A}.

Fixpoint upto_list (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => n' :: upto_list n'
  end.

Lemma upto_list_length n : length (upto_list n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma upto_list_nth : forall m n d,
    n < m ->
    nth n (upto_list m) d = m - (S n).
Proof.
  intros m n d Hlt.
  revert n Hlt.
  induction m; intros n Hlt.
  - inversion Hlt.
  - destruct n as [| n]; simpl; try omega.
    rewrite IHm; omega.
Qed.
Lemma upto_list_iff n : forall x, In x (upto_list n) <-> x < n.
Proof.
  intro x.
  induction n as [| n]; simpl.
  - intuition.
  - rewrite IHn.
    omega.
Qed.

Lemma upto_list_nodup : forall n, NoDup(upto_list n).
Proof.
  induction n; simpl.
  - constructor.
  - constructor; auto.
    rewrite upto_list_iff.
    omega.
Qed.

Program Definition upto (n : nat) : NDL nat :=
  {| elems := upto_list n |}.
Next Obligation.
Proof.
  apply upto_list_nodup.
Qed.

Lemma upto_iff : forall n, NDL_iff (fun x => x < n) (upto n).
Proof.
  intros.
  unfold NDL_iff.
  intro x.
  unfold upto, nd_In.
  simpl.
  now rewrite upto_list_iff.
Qed.

Lemma upto_count : forall n, count (upto n) = n.
Proof.
  intros.
  unfold count, upto.
  simpl.
  induction n; simpl; auto.
Qed.


Definition Across xs n m :=  m <= n < m + nth_mod m xs 0.
Program Definition Across_ndl (xs : list nat) (n : nat) : NDL nat :=
  nd_filter (fun m => n <? m + nth_mod m xs 0) (upto (S n)).

Lemma Across_ndl_iff :
  forall xs n,
    NDL_iff (Across xs n) (Across_ndl xs n).
Proof.
  intros xs n.
  unfold Across, Across_ndl.
  unfold NDL_iff.
  intro x.
  rewrite nd_filter_in.
  rewrite (upto_iff (S n) x).
  rewrite Nat.ltb_lt.
  intuition.
Qed.

Program Definition Across_ndl_mod
        (xs : list nat) (n : nat) (p : nat) : NDL nat :=
  nd_filter (fun m => m mod (length xs) =? p) (Across_ndl xs n).

Lemma Across_ndl_mod_iff : forall xs n p,
    NDL_iff (fun m =>  Across xs n m /\ m mod (length xs) = p)
            (Across_ndl_mod xs n p).
Proof.
  intros xs n p.
  intro x.
  unfold Across_ndl_mod.
  rewrite nd_filter_in.
  rewrite (Across_ndl_iff xs n x).
  rewrite Nat.eqb_eq.
  reflexivity.
Qed.

Lemma Across_mod_union :
  forall xs n,
    xs <> nil -> 
    same_set
      (nd_union_many (map (Across_ndl_mod xs n) (upto_list (length xs))))
      (Across_ndl xs n).
Proof.
  intros xs n Hnnil.
  intro x.
  rewrite nd_union_many_in.
  split.
  - intro H.
    destruct H as [ys [HInys HInx]].
    rewrite in_map_iff in HInys.
    destruct HInys as [p [Heqys HInp]].
    subst.
    rewrite (Across_ndl_mod_iff xs n p x) in HInx.
    rewrite (Across_ndl_iff xs n x).
    tauto.
  - intro H.
    rewrite (Across_ndl_iff xs n x) in H.
    exists (Across_ndl_mod xs n (x mod length xs)).
    split.
    + rewrite in_map_iff.
      exists (x mod length xs).
      split; auto.
      rewrite upto_list_iff.
      apply Nat.mod_upper_bound.
      destruct xs; simpl; auto.
    + now rewrite (Across_ndl_mod_iff _ _ _ _).
Qed.

Fixpoint nat_sum xs :=
  match xs with
  | nil => 0
  | x :: xs' => x + nat_sum xs'
  end.

Lemma nat_sum_app : forall xs ys, nat_sum (xs ++ ys) = nat_sum xs + nat_sum ys.
Proof.
  intros.
  induction xs; simpl; auto.
  omega.
Qed.


Lemma nat_sum_in : forall xs x ys, nat_sum (xs ++ x :: ys) = x + nat_sum xs + nat_sum ys.
Proof.
  intros.
  rewrite nat_sum_app.
  simpl.
  omega.
Qed.

Lemma nat_sum_rev : forall xs, nat_sum (rev xs) = nat_sum xs.
Proof.
  intros.
  induction xs; simpl; auto.
  rewrite nat_sum_in; simpl.
  omega.
Qed.
Lemma Across_mod_union_count :
  forall xs n,
    xs <> nil ->
    count (Across_ndl xs n) =
    nat_sum
      (map (@count _)
           (map (Across_ndl_mod xs n) (upto_list (length xs)))).
Proof.
  intros xs n Hnnil.
  rewrite <- (Across_mod_union _ Hnnil).
  remember (length xs) as m.
  assert (m <= length xs) as Hle; try omega.
  clear Heqm.
  revert Hle.
  induction m.
  - cbn.
    reflexivity.
  - intro Hle.
    cut_hyp IHm; try omega.
    simpl.
    rewrite <- IHm.
    rewrite nd_union_count.
    replace (count (nd_intersection _ _)) with 0; try omega.
    apply eq_sym.
    rewrite count_0_empty.
    intro x.
    split; intro H.
    + rewrite nd_intersection_in in H.
      destruct H as [Hm Hm'].
      rewrite nd_union_many_in in Hm'.
      destruct Hm' as [ys [HIn Hm']].
      rewrite in_map_iff in HIn.
      destruct HIn as [m' [Heqys HInx]].
      subst.
      rewrite upto_list_iff in HInx.
      rewrite (Across_ndl_mod_iff _ _ _ _) in Hm.
      rewrite (Across_ndl_mod_iff _ _ _ _) in Hm'.
      intuition.
    + contradict H.
Qed.


Lemma Across_ndl_mod_iff' : forall xs n p,
    xs <> nil -> p < length xs -> n >= p + nth p xs 0 ->
    NDL_iff
      (fun m => exists x, m = length xs * x + p /\
         n - p - nth p xs 0 < length xs * x <= n - p)
      (Across_ndl_mod xs n p).
Proof.
  intros until p.
  intros Hnn Hp Hn.
  intro m.
  rewrite (Across_ndl_mod_iff xs n p m).
  unfold Across.
  unfold nth_mod.
  remember (length xs) as k.
  assert (k <> 0) as Hk. {
    destruct xs; auto.
    subst.
    simpl.
    auto.
  }
  clear Heqk.
  destruct_divmod m k Hk x p'.
  simpl_mod k Hk.
  repeat rewrite (Nat.mod_small p' k Hp'lt).
  split; intro H.
  - exists x.
    destruct H; subst.
    omega.
  - destruct H as [x' H].
    destruct H.
    replace p' with p in *.
    + replace x' with x in *.
      * omega.
      * rewrite Nat.add_cancel_r in H.
        now rewrite Nat.mul_cancel_l in H.
    + apply f_equal with (f := fun x => x mod k) in H.
      revert H.
      simpl_mod k Hk.
      rewrite (Nat.mod_small p k); auto.
      rewrite (Nat.mod_small p' k); auto.
Qed.

Definition Across_ndl_mod_divk xs n p : list nat :=
  nd_diff (upto (S ((n - p) / length xs)))
          (upto (S ((n - p - nth p xs 0) / length xs))).

Lemma nodup_inj_map {A B} : forall (f : A -> B) (xs : list A),
    (forall x y, f x = f y -> x = y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros f xs Hinj HND.
  induction HND; simpl.
  - constructor.
  - constructor; auto.
    rewrite in_map_iff.
    intros (x' & Heq & HIn).
    apply Hinj in Heq.
    now subst.
Qed.

Lemma Across_ndl_mod'_prf : forall (xs : list nat) (Hnn : xs <> nil) n p,
    NoDup (map (fun m => length xs * m + p) (Across_ndl_mod_divk xs n p)).
Proof.
  intros.
  apply nodup_inj_map. {
    intros.
    rewrite Nat.add_cancel_r in H; auto.
    rewrite Nat.mul_cancel_l in H; auto.
    now destruct xs; simpl.
  }
  apply nodup_filter.
  apply upto_list_nodup.
Qed.

Definition Across_ndl_mod' (xs : list nat) (Hnn : xs <> nil) (n p : nat) : NDL nat.
  apply Build_NDL
    with (map (fun m => length xs * m + p) (Across_ndl_mod_divk xs n p)).
  now apply Across_ndl_mod'_prf.
Defined.


Lemma Across_ndl_mod_same :
  forall xs n p (Hnn : xs <> nil), 
    p < length xs -> n >= p + nth p xs 0 ->
    Across_ndl_mod xs n p == Across_ndl_mod' Hnn n p.
Proof.
  intros until Hnn.
  intros Hp Hn.
  intro m.
  rewrite (Across_ndl_mod_iff' Hnn Hp Hn m).
  rewrite nd_In_In.
  unfold Across_ndl_mod'.
  simpl.
  rewrite in_map_iff.
  remember (length xs) as k.
  assert (k <> 0) as Hk. {
    destruct xs; simpl in *; auto.
    subst. auto.
  }
  unfold Across_ndl_mod_divk.
  split; intros [x H]; exists x.
  - destruct H as [Heqm [Hlb Hub]].
    rewrite Heqm in *; clear Heqm.
    split; auto.
    rewrite <- nd_In_In.
    rewrite nd_diff_in.
    repeat rewrite (upto_iff _ _).
    split.
    + apply Nat.div_le_lower_bound in Hub; auto.
      subst. omega.
    + rewrite Nat.nlt_succ_r.
      revert Hlb.
      rewrite <- Heqk.
      destruct_divmod (n - p - nth p xs 0) k Hk y q.
      intro H.
      cut (k * y + q < k * x + q); try omega.
      rewrite <- Nat.add_lt_mono_r.
      rewrite <- Nat.mul_lt_mono_pos_l; try omega.
      rewrite Nat.mul_comm.
      rewrite Nat.div_add_l; auto.
      rewrite Nat.div_small; auto.
      omega.
  - destruct H as [Heqm HIn].
    rewrite <- nd_In_In in HIn.
    rewrite nd_diff_in in HIn.
    repeat rewrite (upto_iff _ _) in HIn.
    rewrite Nat.nlt_succ_r in HIn.
    rewrite <- Heqk in *.
    split; auto.
    split.
    + apply proj2 in HIn.
      revert HIn.
      destruct_divmod (n - p - nth p xs 0) k Hk y q.
      rewrite (Nat.mul_comm k y) at 1.
      rewrite Nat.div_add_l; auto.
      rewrite Nat.div_small; auto.
      intro Hlt.
      rewrite Nat.add_0_r in Hlt.
      apply lt_le_trans with (k * y + k); try omega.
      unfold lt in Hlt.
      apply Nat.mul_le_mono_l with (p := k) in Hlt.
      rewrite Nat.mul_succ_r in Hlt.
      assumption.
    + apply proj1 in HIn.
      unfold lt in HIn.
      rewrite  <- Nat.succ_le_mono in HIn.
      revert HIn.
      destruct_divmod (n - p) k Hk y q.
      rewrite (Nat.mul_comm k y) at 1.
      rewrite Nat.div_add_l; auto.
      rewrite Nat.div_small; auto.
      rewrite Nat.add_0_r.
      intro Hle.
      apply le_trans with (k * y); try omega.
      now apply Nat.mul_le_mono_l.
Qed.

Lemma div_mul : forall x y, y <> 0 -> x / y * y = x - x mod y.
Proof.
  intros x y Hy.
  destruct_divmod x y Hy m p.
  simpl_mod y Hy.
  rewrite (Nat.mul_comm y m).
  rewrite Nat.div_add_l; auto.
  rewrite Nat.div_small; auto.
  rewrite Nat.mod_small; auto.
  rewrite Nat.add_0_r.
  rewrite Nat.add_sub.
  reflexivity.
Qed.


Lemma Across_ndl_mod_count :
  forall xs n p,
    xs <> nil -> p < length xs -> n >= p + nth p xs 0 ->
    count (Across_ndl_mod xs n p) * length xs =
    nth p xs 0  +
    (n - p - nth p xs 0) mod (length xs) - (n - p) mod (length xs).
Proof.
  intros xs n p Hxs Hp Hn.
  rewrite (Across_ndl_mod_same Hxs Hp Hn).

  unfold Across_ndl_mod'.
  unfold count. simpl.
  rewrite map_length.
  unfold Across_ndl_mod_divk.
  remember (length xs) as k.
  assert (k <> 0) as Hk. {
    destruct xs; auto.
    subst.
    simpl.
    auto.
  }
 
  rewrite <- nd_count_length.
  rewrite nd_diff_count.
  rewrite nd_intersection_comm.
  rewrite nd_intersection_included.
  - clear Heqk.
    repeat rewrite upto_count.
    rewrite Nat.sub_succ.
    rewrite Nat.mul_sub_distr_r.
    repeat rewrite div_mul; auto.

    remember (n - p ) as x.
    remember (nth p xs 0) as a_p.
    rewrite sub_sub_add; eauto using Nat.mod_le.
    rewrite <- Nat.add_sub_swap; eauto using Nat.mod_le.
    omega.
  - intro x.
    repeat rewrite (upto_iff _ _).
    intro Hlt.
    refine (@lt_le_trans _ _ _ Hlt _).
    rewrite <- Nat.succ_le_mono.
    apply Nat.div_le_mono; try omega.
Qed.

Lemma map_sum_add {A} : forall (f g : A -> nat) xs,
    nat_sum (map (fun x => f x + g x) xs) = nat_sum (map f xs) + nat_sum (map g xs).
Proof.
  intros.
  induction xs; simpl; auto.
  rewrite IHxs.
  omega.
Qed.

Lemma map_sum_sub {A} : forall (f g : A -> nat) xs,
    (forall x, In x xs -> g x <= f x) ->
    nat_sum (map (fun x => f x - g x) xs) = nat_sum (map f xs) - nat_sum (map g xs).
Proof.
  intros f g.
  induction xs; intro Hle; simpl; auto.
  rewrite IHxs.
  - rewrite Nat.sub_add_distr.
    rewrite Nat.add_sub_swap.
    + rewrite Nat.add_sub_assoc; auto.
      cut (forall x,In x xs -> g x <= f x); try solve [intuition].
      clear.
      induction xs; simpl; auto.
      intro H.
      apply le_trans with (f a + nat_sum (map g xs)).
      * apply Nat.add_le_mono_r.
        intuition.
      * apply Nat.add_le_mono_l.
        apply IHxs.
        intuition.
    + apply Hle.
      simpl.
      auto.
  - intros x HIn.
    apply Hle.
    simpl.
    auto.
Qed.

Lemma map_sum_mul_distr {A} : forall (f : A -> nat) xs a,
    nat_sum (map f xs) * a = nat_sum (map (fun x => f x * a) xs).
Proof.
  intros f xs a.
  induction xs as [| x xs]; simpl; auto.
  rewrite <- IHxs.
  ring.
Qed.

Lemma pigeon : forall xs n,
    n < length xs -> (forall x, In x xs -> x < n) -> ~NoDup xs.
Proof.
  intro xs.
  remember (length xs) as len.
  revert xs Heqlen.
  induction len as [| len].
  - intros xs Heq n Hlt Hbound.
    inversion Hlt.
  - intros xs Heq n Hlt Hbound.
    destruct n as [| n].
    + destruct xs; inversion Heq.
      specialize (Hbound n).
      simpl in Hbound.
      intuition.
    + destruct (In_dec n xs) as [HIn | Hnin].
      * apply in_split in HIn.
        destruct HIn as (xl & xr & Hxs).
        subst.
        intro HND.
        apply NoDup_remove in HND.
        destruct HND as [HND Hnin].
        contradict HND.
        apply IHlen with (n := n); try omega.
        -- rewrite app_length in *.
           simpl in *.
           omega.
        -- intros x HIn.
           specialize (Hbound x).
           rewrite in_app_iff in *. simpl in *.
           cut_hyp Hbound; try tauto.
           cut (x <> n); try omega.
           intro.
           now subst.
      * inversion 1 as [|?x ?xs' Hninx HND]; subst; simpl in *; try discriminate.
        contradict HND.
        apply IHlen with (n := n); try omega.
        intros y HIny.
        specialize (Hbound y).
        cut_hyp Hbound; auto.
        cut (y <> n); try omega.
        intro.
        subst.
        tauto.
Qed.
    
Lemma inv_pigeon : forall xs,
    NoDup xs -> (forall x, In x xs -> x < length xs) ->
    forall x, x < length xs -> In x xs.
Proof.
  intro xs.
  remember (length xs) as len.
  revert xs Heqlen.
  induction len.
  - intros.
    omega.
  - intros xs Hlen HND Hbound x Hlt.
    assert (In len xs) as HIn. {
      destruct (In_dec len xs); auto.
      contradict HND.
      apply pigeon with (n := len); try omega.
      intros x' HIn.
      specialize (Hbound x' HIn).
      cut (x' <> len); try omega.
      intro.
      now subst.
    }
    inversion Hlt; subst; auto.
    apply in_split in HIn.
    destruct HIn as (xl & xr & Hxs).
    subst.
    specialize (IHlen (xl ++ xr)).
    rewrite app_length in *.
    simpl in *.
    cut_hyp IHlen; try omega.
    apply NoDup_remove in HND.
    cut_hyp IHlen; try tauto.
    cut_hyp IHlen.
    + intros y HIny.
      specialize (Hbound y).
      rewrite in_app_iff in *.
      simpl in *.
      cut (y <> len).
      * intros.
        cut_hyp Hbound; try tauto.
        omega.
      * intro.
        subst.
        tauto.
    + specialize (IHlen x).
      rewrite in_app_iff in *.
      simpl.
      destruct IHlen; auto.
Qed.

Lemma nodup_sum : forall (xs : list nat),
    NoDup xs -> (forall x, In x xs -> x < length xs) ->
    nat_sum xs = nat_sum (upto_list (length xs)).
Proof.
  intros xs.
  remember (length xs) as len.
  revert xs Heqlen.
  induction len.
  - destruct xs; simpl; intuition.
  - intros xs Hlen HND Hbound.
    assert (In len xs) as HIn. {
      apply inv_pigeon; auto; try omega.
      intros x HInx.
      specialize (Hbound x HInx).
      congruence.
    }
    apply in_split in HIn.
    destruct HIn as (l1 & l2 & Hxs).
    subst.
    apply NoDup_remove in HND.
    rewrite nat_sum_in.
    rewrite <- Nat.add_assoc.
    rewrite <- nat_sum_app.
    rewrite (IHlen (l1 ++ l2)); simpl; try tauto.
    + rewrite app_length in *.
      simpl in *.
      omega.
    + intros x HInx.
      specialize (Hbound x).
      rewrite in_app_iff in *.
      simpl in Hbound.
      cut (x <> len).
      * intuition.
      * intro.
        now subst.
Qed.
                        
Fixpoint maximum (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | x :: xs' => Nat.max x (maximum xs')
  end.

Lemma maximum_spec : forall xs x, In x xs -> x <= maximum xs.
Proof.
  induction xs as [| x xs]; intro y; simpl; try tauto.
  destruct 1.
  - subst.
    apply Nat.le_max_l.
  - apply le_trans with (maximum xs); auto.
    apply Nat.le_max_r.
Qed.

Lemma map_nth' : forall {A B} (f : A -> B) xs n da db,
    n < length xs ->
    nth n (map f xs) da = f (nth n xs db).
Proof.
  intros until db.
  revert xs.
  induction n; intros xs Hlt.
  - destruct xs.
    + inversion Hlt.
    + reflexivity.
  - destruct xs.
    + inversion Hlt.
    + simpl.
      rewrite IHn; auto.
      simpl in Hlt.
      omega.
Qed.

Lemma list_elem_eq {A} : forall xs ys (d : A),
    length xs = length ys ->
    (forall i, i < length xs -> nth i xs d = nth i ys d) ->
    xs = ys.
Proof.
  induction xs.
  - destruct ys; simpl in *; try discriminate.
    reflexivity.
  - intros ys d Hlen Heq.
    destruct ys as [|b ys]; simpl in Hlen; try discriminate.
    specialize (IHxs ys d).
    cut_hyp IHxs; auto.
    replace a with b.
    + rewrite IHxs; auto.
      intros i Hi.
      specialize (Heq (S i)).
      simpl in Heq.
      apply Heq.
      omega.
    + specialize (Heq 0).
      simpl in Heq.
      rewrite Heq; auto.
      omega.
Qed.
              

Theorem Problem_2 : forall xs,
    Valid xs -> exists nmin,
      forall n, nmin <= n ->
                nat_sum xs = count (Across_ndl xs n) * length xs.
Proof.
  intros xs HV.
  remember (maximum (map_index  Nat.add xs)) as nmin.
  assert (forall p, p < length xs -> nmin >= p + nth p xs 0) as nmin_max. {
    intros p Hlen.
    unfold ge.
    subst.
    apply maximum_spec.
    set map_index_nth as Hnth. clearbody Hnth.
    specialize (Hnth  _ _ Nat.add xs p 0 0 Hlen).
    rewrite <- Hnth.
    apply nth_In.
    rewrite map_index_length.
    assumption.
  }

  exists nmin.
  intros n Hn.
  rewrite Valid_iff in HV.
  unfold Valid' in HV.
  destruct HV as [Hxs HND].
  assert (length xs <> 0) as Hposlen. {
    destruct xs; simpl; auto.
  }
  rewrite Across_mod_union_count; auto.
  rewrite map_map, map_sum_mul_distr.

  assert (length xs <= S n) as Hlen_le. {
    apply le_trans with (S nmin); try omega.
    set (inv_pigeon HND) as HIn. clearbody HIn.
    cut_hyp HIn.
    - intro.
      intro HIn.
      apply In_nth with (d := 0) in HIn.
      destruct HIn as [i Hi].
      rewrite map_index_length in *.
      rewrite map_index_nth with (da := 0) in Hi; try tauto.
      destruct Hi. subst.
      apply Nat.mod_upper_bound; auto.
    - specialize (HIn (length xs - 1)).
      rewrite map_index_length in HIn.
      cut_hyp HIn; try omega.
      apply In_nth with (d := 0) in HIn.
      destruct HIn as [i Hi].
      specialize (nmin_max i).
      destruct Hi as [Hilt Hieq].
      rewrite map_index_length in Hilt.
      rewrite map_index_nth with (da := 0) in Hieq; auto.
      specialize (nmin_max Hilt).
      assert (length xs - 1 <= i + nth i xs 0). {
        rewrite <- Hieq.
        now apply Nat.mod_le.
      }
      apply le_trans with (S (i + nth i xs 0)); try omega.
  }


  
  transitivity
    (nat_sum
       (map (fun p =>
               nth p xs 0  +
               (n - p - nth p xs 0) mod (length xs) - (n - p) mod (length xs))
            (upto_list (length xs)))).
  - rewrite map_sum_sub.
    + rewrite map_sum_add.
      replace (map (fun x => nth x xs 0) (upto_list (length xs))) with
          (rev xs).
      * cut (forall x y z, y = z -> x = x + y - z); [| intros; omega].
        intro H.
        rewrite nat_sum_rev.
        apply H. clear H.
        repeat rewrite (@nodup_sum (map _ _)).
        -- now repeat rewrite map_length.
        -- rewrite NoDup_nth with (d := 0).
           rewrite map_length.
           rewrite upto_list_length.
           intros p q Hp Hq.
           repeat rewrite map_nth' with (db := 0);
             try now rewrite upto_list_length.
           repeat rewrite upto_list_nth; auto.
           repeat rewrite sub_sub_add; try omega.
           intro Heq.
           cut (p mod length xs = q mod length xs). {
             repeat rewrite Nat.mod_small; auto.
           }
           repeat rewrite <- Nat.add_succ_comm in Heq.
           repeat (rewrite Nat.add_sub_swap in Heq; auto).
           rewrite <- mod_eq_iff in *.
           now apply mod_add_inj in Heq.
        -- intro x.
           rewrite map_length, upto_list_length.
           rewrite in_map_iff.
           intros (y & Hyeq & HyIn).
           subst.
           now apply Nat.mod_upper_bound.
        -- rewrite NoDup_nth with (d := 0).
           intros p q.
           repeat rewrite map_length, upto_list_length.
           intros Hp Hq.
           repeat rewrite map_nth' with (db := 0);
             try now rewrite upto_list_length.
           repeat rewrite upto_list_nth; auto.
           remember (length xs - S p) as i.
           remember (length xs - S q) as j.
           assert (i < length xs) as Hi; try omega.
           assert (j < length xs) as Hj; try omega.
           intro Heqmod.
           rewrite <- mod_eq_iff in Heqmod.
           repeat rewrite <- Nat.sub_add_distr in Heqmod.
           apply mod_sub_inj in Heqmod; auto.
           ++ rewrite NoDup_nth with (d := 0) in HND.
              repeat rewrite map_index_length in HND.
              specialize (HND i j Hi Hj).
              repeat (rewrite map_index_nth with (da := 0) in HND; auto).
              rewrite <- mod_eq_iff in HND.
              rewrite (HND Heqmod) in *.
              omega.
           ++ apply le_trans with nmin; auto.
              now apply nmin_max.
           ++ apply le_trans with nmin; auto.
              now apply nmin_max.
        -- intro x.
           rewrite map_length, upto_list_length.
           rewrite in_map_iff.
           intros (y & Hyeq & HyIn).
           subst.
           now apply Nat.mod_upper_bound.
      * clear.
        apply list_elem_eq with (d := 0).
        -- now rewrite rev_length, map_length, upto_list_length.
        -- intros i Hlt.
           rewrite rev_length in *.
           rewrite rev_nth; auto.
           rewrite map_nth' with (db := 0).
           ++ rewrite upto_list_nth; auto.
           ++ now rewrite upto_list_length.
    + intros p Hp.
      rewrite upto_list_iff in Hp.
      remember (nth p xs 0) as m.
      assert (length xs <> 0) as Hlen. {
        destruct xs; auto.
      }
      replace (n - p) with (n - p - m + m) at 1.
      * destruct_divmod (n-p-m) (length xs) Hlen x q.
        simpl_mod (length xs) Hlen.
        rewrite (Nat.mod_small q); auto.
        rewrite Nat.add_comm.
        apply Nat.mod_le; auto.
      * rewrite Nat.sub_add; auto.
        specialize (nmin_max p Hp).
        omega.
  - f_equal.
    apply map_ext_in.
    intros p Hp.
    rewrite upto_list_iff in Hp.
    rewrite Across_ndl_mod_count; auto.
    specialize (nmin_max p Hp).
    omega.
Qed.
