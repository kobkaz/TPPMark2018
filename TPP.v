Require Import List.
Require Import Arith Omega.
Require Import SetoidClass.
Require Import Wf_nat.

Require Import Util.
Require Import Mod.
Require Import NDL.

Set Implicit Arguments.

Definition Valid xs : Prop :=
  xs <> nil /\
    (forall m n, m + nth_mod m xs 0 = n + nth_mod n xs 0 -> m = n).


Definition Valid' xs : Prop :=
  xs <> nil /\ NoDup (map_index (fun i x => (i + x) mod length xs) xs).



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
