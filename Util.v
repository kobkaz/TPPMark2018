Require Import List.
Require Import Omega.
Require Import SetoidClass.

Set Implicit Arguments.

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

Ltac cut_hyp H :=
  refine ((fun p pq => pq (H p)) _ _); clear H; [| intro H].


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
