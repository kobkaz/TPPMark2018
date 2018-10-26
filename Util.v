Require Import List.
Require Import Arith Omega.


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
              
Lemma sub_sub_add : forall x y z, z <= y -> (x - (y - z)) = x + z - y.
Proof.
  intros.
  omega.
Qed.
