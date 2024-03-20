From stdpp Require Import list.
From CoqListSolver Require Import definitions.
From CoqListSolver Require Import length_normal_form.

Lemma cons_app {A} (v : A) (l : list A):
  v :: l = [v] ++ l.
Proof. done. Qed.

Ltac cons_app_rewrite_helper x xs :=
  lazymatch xs with
  | nil => fail
  | _ => replace (x::xs) with ([x] ++ xs) by by rewrite cons_app
end.

Ltac cons_app_rewrite :=
  repeat match goal with
  | |- context [?x::?xs] => cons_app_rewrite_helper x xs
  | _ : context [?x::?xs] |- _ => cons_app_rewrite_helper x xs
end.

Tactic Notation "nat_simp" :=
  repeat match goal with
  | |- context [ ?n - ?n ] => replace (n - n) with (0) by lia
  | _ : context [ ?n - ?n ] |- _ => replace (n - n) with (0) by lia
  | |- context [ 0 + ?n ] => replace (0 + n) with (n) by lia
  | _ : context [ 0 + ?n ] |- _ => replace (0 + n) with (n) by lia
  | |- context [ ?n + 0 ] => replace (n + 0) with (n) by lia
  | _ : context [ ?n + 0 ] |- _ => replace (n + 0) with (n) by lia
  | |- context [ 0 - ?n ] => replace (0 - n) with (n) by lia
  | _ : context [ 0 - ?n ] |- _ => replace (0 - n) with (n) by lia
  | |- context [ ?n - 0 ] => replace (n - 0) with (n) by lia
  | _ : context [ ?n - 0 ] |- _ => replace (n - 0) with (n) by lia
  end.

Lemma repeat_Sn {A} (v : A) (n : nat) :
  repeat v (S n) = [v] ++ repeat v n.
Proof. done. Qed.

Lemma map_take {A B} (f : A -> B) (l : list A) (n : nat) :
  map f (take n l) = take n (map f l).
Proof.
  revert n.
  induction l; intros; simpl.
  - repeat rewrite take_nil. reflexivity.
  - destruct n; simpl.
    + repeat rewrite take_0. reflexivity.
    + simpl. rewrite IHl. reflexivity.
Qed.

Lemma map_drop {A B} (f : A -> B) (l : list A) (n : nat) :
  map f (drop n l) = drop n (map f l).
Proof.
  revert n.
  induction l; intros; simpl.
  - repeat rewrite drop_nil. reflexivity.
  - destruct n; simpl.
    + repeat rewrite drop_0. reflexivity.
    + simpl. rewrite IHl. reflexivity.
Qed.

Lemma map_flip_ends {A} {B} (F: A -> B) lo hi (al: list A):
  flip_ends lo hi (map F al) = map F (flip_ends lo hi al).
Proof.
  unfold flip_ends.
  repeat rewrite drop_0.
  repeat rewrite map_app.
  repeat rewrite map_drop.
  repeat rewrite map_take.
  repeat rewrite map_rev.
  rewrite map_length.
  done.
Qed.

Lemma map_nil {A} {B} (f : A -> B) :
  map f [] = [].
Proof. done. Qed.

Lemma map_singleton {A} {B} (f : A -> B) (x : A) :
  map f [x] = [f x].
Proof. done. Qed.

Lemma nth_l_nth_l_0 {A} {d : Inhabitant A} (i : nat) (l : list A) (x : A):
  nth_l 0 ([x]) = x.
Proof. done.
Qed.

Lemma nth_l_nil {A} {d : Inhabitant A} (i : nat):
  nth_l i ([] : list A) = default.
Proof. by destruct i. Qed.

Lemma nth_l_app_case1 {A}{d : Inhabitant A} (i : nat) (l l': list A):
  i < length l ->
  nth_l i (l ++ l') = nth_l i l.
Proof.
  unfold nth_l.
  intros H.
  revert l l' H.
  induction i; intros; destruct l; try (simpl in H; lia); simpl; try reflexivity.
  apply IHi. simpl in H; lia.
Qed.

Lemma nth_l_app_case2 {A}{d : Inhabitant A} (i : nat) (l l': list A):
  length l <= i < length l + length l' ->
  nth_l i (l ++ l') = nth_l (i - length l) l'.
Proof.
  unfold nth_l.
  intros H.
  revert l l' H.
  induction i; intros; destruct l; try done.
  - simpl in H; lia.
  - simpl; apply IHi; simpl in H; lia.
Qed.

Lemma nth_l_app_case3 {A}{d : Inhabitant A} (i : nat) (l l': list A):
  length l + length l' <= i ->
  nth_l i (l ++ l') = d.
Proof.
  unfold nth_l.
  intros H.
  apply nth_overflow.
  length_normal_form.
  lia.
Qed.

Lemma split_nth_l_app {A}{d : Inhabitant A} (i : nat) (l l': list A):
  (i < length l /\ nth_l i (l ++ l') = nth_l i l) \/
  (length l <= i < length l + length l' /\ nth_l i (l ++ l') = nth_l (i - length l) l') \/
  (length l + length l' <= i /\ nth_l i (l ++ l') = d).
Proof.
  assert (i < length l \/ length l <= i < length l + length l' \/ length l + length l' <= i) by lia.
  destruct H as [? | [? | ?]].
  - left. split; [assumption|by apply nth_l_app_case1].
  - right; left; split; [assumption|by apply nth_l_app_case2].
  - right; right; split; [assumption|by apply nth_l_app_case3].
Qed.


Ltac split_nth_l_app_tac_helper i l l' :=
  let H' := fresh "H'" in
  (   (assert (i < length l) as H' by (length_normal_form_goal; lia);
      apply nth_l_app_case1 in H'; try rewrite H' in *; clear H')
  ||  (assert (length l <= i < length l + length l') as H' by (length_normal_form_goal; lia);
      apply nth_l_app_case2 in H'; try rewrite H' in *; clear H')
  ||  (assert (length l + length l' <= i) as H' by (length_normal_form_goal; lia);
      apply nth_l_app_case3 in H'; try rewrite H' in *; clear H')
  ||  (destruct (split_nth_l_app i l l') as [[? H']|[[? H']|[? H']]];
      try rewrite H' in *; clear H')
  ).

Ltac split_nth_l_app_tac :=
  repeat match goal with
  | |- context [ nth_l ?i (?l ++ ?l') ] => split_nth_l_app_tac_helper i l l'
  | _ : context [ nth_l ?i (?l ++ ?l') ] |- _ => split_nth_l_app_tac_helper i l l'
  end.

Lemma nth_l_map_case1 {A} {B} {da : Inhabitant A} {db : Inhabitant B} (f : A -> B) (i : nat) (l : list A):
  i < length l ->
  nth_l i (map f l) = f (nth_l i l).
Proof.
  revert f i.
  induction l; destruct i; intros; simpl in *; try lia.
  - unfold nth_l. reflexivity.
  - unfold nth_l; simpl. apply IHl. lia.
Qed.

Lemma nth_l_map_case2 {A} {B} {da : Inhabitant A} {db : Inhabitant B} (f : A -> B) (i : nat) (l : list A):
  length l <= i ->
  nth_l i (map f l) = default.
Proof.
  intros.
  unfold nth_l.
  apply nth_overflow.
  by length_normal_form.
Qed.

Lemma split_nth_l_map {A} {B} {da : Inhabitant A} {db : Inhabitant B} (f : A -> B) (i : nat) (l : list A):
  (i < length l /\ nth_l i (map f l) = f (nth_l i l))
  \/ (length l <= i /\ nth_l i (map f l) = default).
Proof.
  assert (i < length l \/ length l <= i) as [?|?] by lia.
  - left; split; [done|by eapply nth_l_map_case1].
  - right; split; [done|by eapply nth_l_map_case2].
Qed.

Ltac split_nth_l_map_tac_helper f i l :=
  let H' := fresh "H'" in
  (   (assert (i < length l) as H' by (length_normal_form_goal; lia);
      apply nth_l_map_case1 in H'; try rewrite H' in *; clear H')
  ||  (assert (length l <= i) as H' by (length_normal_form_goal; lia);
      apply nth_l_map_case2 in H'; try rewrite H' in *; clear H')
  ||  (destruct (split_nth_l_map f i l) as [[? H']|[? H']];
      try rewrite H' in *; clear H')
  ).

Ltac split_nth_l_map_tac :=
  repeat match goal with
  | |- context [ nth_l ?i (map ?f ?l) ] => split_nth_l_map_tac_helper f i l
  | _ : context [ nth_l ?i (map ?f ?l) ] |- _ => split_nth_l_map_tac_helper f i l
  end.

Lemma nth_l_rev_helper {A} {d : Inhabitant A} (i : nat) (l : list A):
  i < length l ->
  nth_l (length l - i - 1) (rev l) = nth_l i l.
Proof.
  unfold nth_l.
  revert i.
  induction l; intros.
  - destruct i; simpl; done.
  - destruct i.
    + simpl. rewrite app_nth2; length_normal_form; [ |lia].
      replace (length l - 0 - length l) with 0 by lia.
      reflexivity.
    + simpl. rewrite app_nth1.
      * apply IHl. simpl in H. lia.
      * length_normal_form. simpl in H. lia.
Qed.

Lemma nth_l_rev_case1 {A} {d : Inhabitant A} (i : nat) (l : list A):
  i < length l ->
  nth_l i (rev l) = nth_l (length l - i - 1) l.
Proof.
  intros.
  assert (i < (length (rev l))) by (length_normal_form; lia).
  apply nth_l_rev_helper in H0.
  length_normal_form.
  rewrite <- H0.
  by rewrite rev_involutive.
Qed.

Lemma nth_l_rev_case2 {A} {d : Inhabitant A} (i : nat) (l : list A):
  i >= length l ->
  nth_l i (rev l) = d.
Proof.
  intros H.
  unfold nth_l.
  apply nth_overflow.
  length_normal_form; lia.
Qed.

Lemma split_nth_l_rev {A} {d : Inhabitant A} (i : nat) (l : list A):
  (i < length l /\ nth_l i (rev l) = nth_l (length l - i - 1) l)
  \/ (i >= length l /\ nth_l i (rev l) = d).
Proof.
  assert (i < length l \/ i >= length l) as [?|?] by lia.
  - left; split; [done| by apply nth_l_rev_case1].
  - right; split; [done| by apply nth_l_rev_case2].
Qed.

Ltac split_nth_l_rev_tac_helper i l :=
  let H' := fresh "H'" in
  (   (assert (i < length l) as H' by (length_normal_form_goal; lia);
      apply (nth_l_rev_case1 i l) in H'; try rewrite H' in *; clear H')
  ||  (assert (i >= length l) as H' by (length_normal_form_goal; lia);
      apply (nth_l_rev_case2 i l) in H'; try rewrite H' in *; clear H')
  ||  (destruct (split_nth_l_rev i l) as [[? H']|[? H']];
      try rewrite H' in *; clear H')
  ).

Ltac split_nth_l_rev_tac :=
  repeat match goal with
  | |- context [ nth_l ?i (rev ?l) ] => split_nth_l_rev_tac_helper i l
  | _ : context [ nth_l ?i (rev ?l) ] |- _ => split_nth_l_rev_tac_helper i l
  end.

Lemma nth_l_drop {A} {d : Inhabitant A} (i j : nat) (l : list A):
  nth_l i (drop j l) = nth_l (i + j) l.
Proof.
  destruct (le_lt_dec (length l) j) as [Hlen | Hlen]; unfold nth_l.
  - rewrite drop_ge; [ | done].
    rewrite nth_overflow by (simpl; lia).
    by rewrite nth_overflow by lia.
  - unfold nth_l.
    rewrite <- (take_drop j l).
    rewrite app_nth2 by (length_normal_form; lia).
    rewrite (take_drop j l).
    f_equal.
    length_normal_form.
    lia.
Qed.

Lemma nth_l_take_case1 {A} {d : Inhabitant A} (i j : nat) (l : list A):
  i < j ->
  nth_l i (take j l) = nth_l i l.
Proof.
  intros Hij.
  destruct (le_lt_dec (length l) i).
  - unfold nth_l.
    rewrite nth_overflow by (length_normal_form; lia).
    rewrite nth_overflow by (length_normal_form; lia).
    reflexivity.
  - unfold nth_l.
    rewrite <- (take_drop j l).
    rewrite app_nth1 by (length_normal_form; lia).
    rewrite take_drop.
    reflexivity.
Qed.

Lemma nth_l_take_case2 {A} {d : Inhabitant A} (i j : nat) (l : list A):
  i >= j ->
  nth_l i (take j l) = d.
Proof.
  intros Hij.
  unfold nth_l.
  by rewrite nth_overflow by (length_normal_form; lia).
Qed.

Lemma split_nth_l_take {A} {d : Inhabitant A} (i j : nat) (l : list A):
  (i < j /\ nth_l i (take j l) = nth_l i l)
  \/ (i >= j /\ nth_l i (take j l) = d).
Proof.
  destruct (le_lt_dec j i) as [Hj | Hi].
  - right; split; [done | apply nth_l_take_case2; done].
  - left; split; [done | apply nth_l_take_case1; done].
Qed.


Ltac split_nth_l_take_tac_helper i j l :=
  let H' := fresh "H'" in
  (   (assert (i < j) as H' by (length_normal_form_goal; lia);
      apply (nth_l_take_case1 i j l) in H'; try rewrite H' in *; clear H')
  ||  (assert (i >= j) as H' by (length_normal_form_goal; lia);
      apply (nth_l_take_case2 i j l) in H'; try rewrite H' in *; clear H')
  ||  (destruct (split_nth_l_take i j l) as [[? H']|[? H']];
      try rewrite H' in *; clear H')
  ).

Ltac split_nth_l_take_tac :=
  repeat match goal with
  | |- context [ nth_l ?i (take ?j ?l) ] => split_nth_l_take_tac_helper i j l
  | _ : context [ nth_l ?i (take ?j ?l) ] |- _ => split_nth_l_take_tac_helper i j l
  end.


Lemma nth_l_repeat_case1 {A} {d : Inhabitant A} (i : nat) (v : A) (n : nat):
  i < n ->
  nth_l i (repeat v n) = v.
Proof.
  revert i.
  induction n; [lia|].
  intros.
  unfold nth_l.
  destruct i;
  [done|simpl; apply IHn; lia].
Qed.

Lemma nth_l_repeat_case2 {A} {d : Inhabitant A} (i : nat) (v : A) (n : nat):
  i >= n ->
  nth_l i (repeat v n) = d.
Proof.
  unfold nth_l.
  intros.
  apply nth_overflow.
  length_normal_form.
  lia.
Qed.

Lemma split_nth_l_repeat {A} {d : Inhabitant A} (i : nat) (v : A) (n : nat):
  (i < n /\ nth_l i (repeat v n) = v)
  \/ (i >= n /\ nth_l i (repeat v n) = d).
Proof.
  destruct (le_lt_dec n i) as [Hn|Hn].
  - right; split; [done|by apply nth_l_repeat_case2].
  - left; split; [done|by apply nth_l_repeat_case1].
Qed.

Ltac split_nth_l_repeat_tac_helper i v n :=
  let H' := fresh "H'" in
  (   (assert (i < n) as H' by (length_normal_form_goal; lia);
      apply (nth_l_repeat_case1 i v n) in H'; try rewrite H' in *; clear H')
  ||  (assert (i >= n) as H' by (length_normal_form_goal; lia);
      apply (nth_l_repeat_case2 i v n) in H'; try rewrite H' in *; clear H')
  ||  (destruct (split_nth_l_repeat i v n) as [[? H']|[? H']];
      try rewrite H' in *; clear H')
  ).

Ltac split_nth_l_repeat_tac :=
  repeat match goal with
  | |- context [ nth_l ?i (repeat ?v ?n) ] => split_nth_l_repeat_tac_helper i v n
  | _ : context [ nth_l ?i (repeat ?v ?n) ] |- _ => split_nth_l_repeat_tac_helper i v n
  end.

Lemma nth_l_elem {A} {d : Inhabitant A} (i : nat) (l : list A):
  [nth_l i l] = take 1 (drop i l ++ [d]).
Proof.
  unfold nth_l.
  revert i.
  induction l; intros.
  - rewrite nth_overflow, drop_ge; [simpl; done|simpl; lia|simpl; lia].
  - destruct i; simpl; [by rewrite take_0|apply IHl].
Qed.

Lemma repeat_take {A} (v : A) (n m : nat):
  take n (repeat v m) = repeat v (n `min` m).
Proof.
  revert m.
  induction n; intros; simpl; [by rewrite take_0|].
  destruct m; [done|simpl; by f_equal].
Qed.

Lemma repeat_drop {A} (v : A) (n m : nat):
  drop n (repeat v m) = repeat v (m - n).
Proof.
  revert m.
  induction n; intros; simpl; [by rewrite drop_0, Nat.sub_0_r|].
  destruct m; [done|simpl; done].
Qed.

Lemma repeat_map {A} {B} (f : A -> B) (v : A) (n : nat):
  map f (repeat v n) = repeat (f v) n.
Proof.
  induction n; intros; simpl; [done|by f_equal].
Qed.


Ltac take_0_nil_by_lia :=
  match goal with
    | |- context [ take ?n ?l ] => assert (n = 0) as -> by lia; rewrite take_0; try rewrite take_0 in *
    | _ : context [ take ?n ?l ] |- _ => assert (n = 0) as -> by lia; rewrite take_0 in *
  end.

Ltac remove_take_ge_by_lia := 
  let H := fresh "H" in
  match goal with
    | |- context [ take ?n ?l ] => assert (length l <= n) as H by (length_normal_form_goal; lia); apply take_ge in H; rewrite H; try rewrite H in *; clear H
    | _ : context [ take ?n ?l ] |- _ => assert (length l <= n) as H by (length_normal_form_goal; lia); apply take_ge in H; rewrite H in *; clear H
  end.

Ltac drop_ge_nil_by_lia :=
  let H := fresh "H" in
  match goal with
    | |- context [ drop ?n ?l ] => assert (length l <= n) as H by (length_normal_form_goal; lia); apply drop_ge in H; rewrite H; try rewrite H in *; clear H
    | _ : context [ drop ?n ?l ] |- _ => assert (length l <= n) as H by (length_normal_form_goal; lia); apply drop_ge in H; rewrite H in *; clear H
  end.

Ltac remove_drop_0_by_lia :=
  let H := fresh "H" in
  match goal with
    | |- context [ drop ?n ?l ] => assert (n = 0) as H by lia; try rewrite H in *; clear H; rewrite drop_0; try rewrite drop_0 in *
    | _ : context [ drop ?n ?l ] |- _ => assert (n = 0) as H by lia; try rewrite H in *; clear H; rewrite drop_0 in *
  end.

Lemma update_app_case1 {A} `{Inhabitant A} (i : nat) (l1 l2 : list A) (v : A):
  i < length l1 ->
  update i (l1 ++ l2) v = (update i l1 v) ++ l2.
Proof.
  intros.
  unfold update.
  repeat (rewrite firstn_app).
  repeat (match goal with
  | |- context [ take ?n ?l ] => rewrite (take_ge l n); [|try rewrite take_length; try rewrite app_length; lia]
  end; repeat (rewrite app_assoc_reverse)).
  f_equal.
  replace (i - length l1) with 0 by lia.
  rewrite take_0.
  rewrite app_nil_l.
  f_equal.
  + rewrite take_ge.
    * rewrite take_ge; [done|].
      simpl.
       rewrite take_length. simpl. lia.
    * simpl. repeat rewrite app_length. rewrite take_length. simpl. lia.
  + rewrite skipn_app. replace (i + 1 - length l1) with 0 by lia.
    rewrite drop_0. rewrite firstn_app. f_equal.
    * rewrite take_ge; [rewrite take_ge; [done|]|];
      repeat (rewrite app_length); rewrite drop_length;
      rewrite take_length;
      simpl; lia.
    * rewrite take_ge; [done|].
      repeat (rewrite app_length); rewrite drop_length;
      rewrite take_length;
      simpl; lia.
Qed.

Lemma update_app_case2 {A} `{Inhabitant A} (i : nat) (l1 l2: list A) (v : A) :
  i >= length l1 ->
  update i (l1 ++ l2) v = l1 ++ (update (i - length l1) l2 v).
Proof.
  intros.
  unfold update.
  repeat (rewrite firstn_app || rewrite skipn_app || rewrite app_assoc_reverse).
  f_equal.
  1:{ rewrite take_ge; [by rewrite take_ge|]; rewrite app_length; rewrite take_length; lia. }
  f_equal.
  1:{ (repeat rewrite take_take); rewrite take_length; f_equal; rewrite app_length; lia. }
  f_equal.
  1:{ f_equal; repeat (rewrite app_length||rewrite take_length||rewrite nth_l_length); try lia. }
  rewrite drop_ge; [|lia].
  rewrite take_nil.
  rewrite app_nil_l.
  rewrite take_ge.
  2:{ repeat (rewrite app_length||rewrite take_length||rewrite nth_l_length||rewrite drop_length); simpl; try lia. }
  rewrite take_ge.
  2:{ repeat (rewrite app_length||rewrite take_length||rewrite nth_l_length||rewrite drop_length); simpl; try lia. }
  f_equal; lia.
Qed.

Lemma split_update_app {A} `{Inhabitant A} (i : nat) (l1 l2 : list A) (v : A) :
  (i < length l1 /\ update i (l1 ++ l2) v = (update i l1 v) ++ l2 )
  \/ (i >= length l1 /\ update i (l1 ++ l2) v = l1 ++ (update (i - length l1) l2 v)).
Proof.
  assert (i < length l1 \/ i >= length l1) as [?|?] by lia; [left|right];
  (split; [done|]).
  - by apply update_app_case1.
  - by apply update_app_case2.
Qed.

Ltac split_update_app_tac_helper i l1 l2 v :=
  let H' := fresh "H'" in
  (   (assert (i < length l1) as H' by (length_normal_form_goal; lia);
      apply (update_app_case1 i l1 l2 v) in H'; try rewrite H' in *; clear H')
  ||  (assert (i >= length l1) as H' by (length_normal_form_goal; lia);
      apply (update_app_case2 i l1 l2 v) in H'; try rewrite H' in *; clear H')
  ||  (destruct (split_update_app i l1 l2 v) as [[? H']|[? H']];
      try rewrite H' in *; clear H')
  ).

Ltac split_update_app_tac :=
  repeat match goal with
  | |- context [ update ?i (?l1 ++ ?l2) ?v ] => split_update_app_tac_helper i l1 l2 v
  | _ : context [ update ?i (?l1 ++ ?l2) ?v ] |- _ => split_update_app_tac_helper i l1 l2 v
  end.


Lemma take_take_case1 {A} (n m : nat) (l : list A):
  n <= m ->
  take n (take m l) = take n l.
Proof.
  intros.
  rewrite take_take; f_equal; lia.
Qed.

Lemma take_take_case2 {A} (n m : nat) (l : list A):
  m <= n ->
  take n (take m l) = take m l.
Proof.
  intros.
  rewrite take_take; f_equal; lia.
Qed.

Lemma split_take_take {A} (n m : nat) (l : list A):
  (n <= m /\ take n (take m l) = take n l)
  \/ (n > m /\ take n (take m l) = take m l).
Proof.
  intros.
  assert (n <= m \/ n > m) as [?|?] by lia; [left|right];
  (split; [done|rewrite take_take; f_equal; lia]).
Qed.

Ltac split_take_take_tac_helper n m l :=
  let H' := fresh "H'" in
  (   (assert (n <= m) as H' by lia;
      apply (take_take_case1 n m l) in H'; try rewrite H' in *; clear H')
  ||  (assert (m <= n) as H' by lia;
      apply (take_take_case2 n m l) in H'; try rewrite H' in *; clear H')
  ||  (destruct (split_take_take n m l) as [[? H']|[? H']];
      try rewrite H' in *; clear H')
  ).

Ltac split_take_take_tac :=
  repeat match goal with
  | |- context [take ?n (take ?m ?l)] => split_take_take_tac_helper n m l
  | _ : context [take ?n (take ?m ?l)] |- _ => split_take_take_tac_helper n m l
  end.


Lemma drop_take_rev_case1 {A} (n m : nat) (l : list A):
  m <= n ->
  drop n (take m (rev l)) = ([] : list A).
Proof.
  intros.
  rewrite drop_ge; [done|].
  rewrite firstn_length. lia.
Qed.

Lemma drop_take_rev_case2 {A} (n m : nat) (l : list A):
  length l <= n ->
  drop n (take m (rev l)) = [].
Proof.
  intros.
  rewrite drop_ge; [done|].
  rewrite firstn_length.
  rewrite rev_length.
  lia.
Qed.

Lemma drop_take_rev_case3 {A} (n m : nat) (l : list A):
  length l <= m ->
  drop n (take m (rev l)) = rev (take ((length l) - n) l).
Proof.
  intros.
  rewrite take_ge; [rewrite skipn_rev; by subst|rewrite rev_length; lia].
Qed.

Lemma drop_take_rev_case4 {A} (n m : nat) (l : list A):
  (n <= length l /\ m <= length l /\ n <= m) ->
  drop n (take m (rev l)) = rev (drop ((length l) - m) (take ((length l) - n) l)).
Proof.
  intros (? & ? & ?).
  rewrite firstn_rev; rewrite skipn_rev.
  rewrite take_drop_commute.
  repeat f_equal. rewrite skipn_length. lia.
Qed.

Lemma split_drop_take_rev {A} (n m : nat) (l : list A):
  ( m <= n /\ drop n (take m (rev l)) = [])
  \/ ((length l) <= n /\ drop n (take m (rev l)) = [])
  \/ ( (length l) <= m /\ drop n (take m (rev l)) = rev (take ((length l) - n) l))
  \/ ( n < (length l) /\ m < (length l) /\ n < m /\ drop n (take m (rev l)) = rev (drop ((length l) - m) (take ((length l) - n) l))).
Proof.
  intros.
  assert (m <= n \/ n >= (length l) \/ m >= (length l) \/ ( n < (length l) /\ m < (length l) /\ n < m )) as [?|[?|[?|?]]] by lia.
  - left. split; [done|by eapply drop_take_rev_case1].
  - right; left. split; [done|erewrite drop_take_rev_case2; by subst].
  - right; right; left. split; [done|by erewrite drop_take_rev_case3].
  - right; right; right.
    destruct H as [? [? ?]]. repeat split; try done.
    rewrite firstn_rev; rewrite skipn_rev.
    rewrite take_drop_commute.
    repeat f_equal. rewrite skipn_length. lia.
Qed.

Ltac split_drop_take_rev_tac_helper n m l :=
  let H' := fresh "H'" in
  let H'' := fresh "H''" in
  (   (assert (m <= n) as H' by lia;
      apply (drop_take_rev_case1 n m l) in H'; try rewrite H' in *; clear H')
  ||  (assert (length l <= n) as H' by (length_normal_form_goal; lia);
      apply (drop_take_rev_case2 n m l) in H'; try rewrite H' in *; clear H')
  ||  (assert (length l <= m) as H' by (length_normal_form_goal; lia);
      apply (drop_take_rev_case3 n m l) in H'; try rewrite H' in *; clear H')
  ||  (assert (n <= length l /\ m <= length l /\ n <= m) as H' by (length_normal_form_goal; lia);
      apply (drop_take_rev_case4 n m l) in H'; try rewrite H' in *; clear H')
  ||  (eassert (length l = _) as H' by (length_normal_form_goal; reflexivity);
      destruct (split_drop_take_rev n m (length l)) as [[? H'']|[[? H''|[[? H'']|[? ? ? H'']]]]];
      try rewrite H' in *; try rewrite H'' in *;
      clear H'; clear H'')
  ).

Ltac split_drop_take_rev_tac :=
  repeat match goal with
  | |- context [ drop ?n (take ?m (rev ?l)) ] => split_drop_take_rev_tac_helper n m l
  | _ : context [ drop ?n (take ?m (rev ?l)) ] |- _ => split_drop_take_rev_tac_helper n m l
  end.

Lemma e_take_rev {A} (n lenl' : nat) (l l' : list A):
  length l = lenl' ->
  take n (rev l) = rev (drop (lenl' - n) l).
Proof. intros; subst; by rewrite firstn_rev. Qed.

Lemma e_drop_rev {A} (n lenl' : nat) (l l' : list A):
  length l = lenl' ->
  drop n (rev l) = rev (take (lenl' - n) l).
Proof. intros; subst; by rewrite skipn_rev. Qed.

Lemma take_app_case1 {A} (n : nat) (l1 l2 : list A):
  n <= length l1 ->
  take n (l1 ++ l2) = take n l1.
Proof.
  intros.
  rewrite firstn_app.
  replace (n - length l1) with 0 by lia.
  rewrite take_0.
  by rewrite app_nil_r.
Qed.

Lemma take_app_case2 {A} (n : nat) (l1 l2 : list A):
  length l1 < n < length l1 + length l2 ->
  take n (l1 ++ l2) = l1 ++ take (n - length l1) l2.
Proof.
  intros.
  rewrite firstn_app.
  by rewrite take_ge by lia.
Qed.

Lemma take_app_case3 {A} (n : nat) (l1 l2 : list A):
  length l1 + length l2 <= n ->
  take n (l1 ++ l2) = l1 ++ l2.
Proof.
  intros.
  by rewrite take_ge by (rewrite app_length;lia).
Qed.

Lemma split_take_app {A} (n : nat) (l1 l2 : list A):
  (n <= length l1 /\ take n (l1 ++ l2) = take n l1)
  \/ (length l1 < n < length l1 + length l2 /\ take n (l1 ++ l2) = l1 ++ take (n - length l1) l2)
  \/ (length l1 + length l2 <= n /\ take n (l1 ++ l2) = l1 ++ l2).
Proof.
  assert (n <= length l1 \/ length l1 < n < length l1 + length l2 \/ length l1 + length l2 <= n) as [?|[?|?]]by lia.
  - left. split; [done|by eapply take_app_case1].
  - right; left. split; [done|by eapply take_app_case2].
  - right; right. split; [done|by eapply take_app_case3].
Qed.

Ltac split_take_app_tac_helper n l1 l2 :=
  let H' := fresh "H'" in
  (   (assert (n <= length l1) as H' by (length_normal_form_goal; lia);
      apply (take_app_case1 n l1 l2) in H'; try rewrite H' in *; clear H')
  ||  (assert (length l1 < n < length l1 + length l2) as H' by (length_normal_form_goal; lia);
      apply (take_app_case2 n l1 l2) in H'; try rewrite H' in *; clear H')
  ||  (assert (length l1 + length l2 <= n) as H' by (length_normal_form_goal; lia);
      apply (take_app_case3 n l1 l2) in H'; try rewrite H' in *; clear H')
  ||  (pose proof (split_take_app n l1 l2) as [[? H']|[[? H']|[? H']]];
      try rewrite H' in *; clear H')
  ).

Ltac split_take_app_tac :=
  repeat match goal with
  | |- context [ take ?n (?l1 ++ ?l2) ] => split_take_app_tac_helper n l1 l2
  | _ : context [ take ?n (?l1 ++ ?l2) ] |- _ => split_take_app_tac_helper n l1 l2
  end.

Lemma drop_app_case1 {A} (n : nat) (l1 l2 : list A):
  n <= length l1 ->
  drop n (l1 ++ l2) = drop n l1 ++ l2.
Proof.
  intros.
  rewrite skipn_app.
  f_equal.
  replace (n - length l1) with 0 by lia.
  by rewrite drop_0.
Qed.

Lemma drop_app_case2 {A} (n : nat) (l1 l2 : list A):
  length l1 < n < length l1 + length l2 ->
  drop n (l1 ++ l2) = drop (n - length l1) l2.
Proof.
  intros.
  rewrite skipn_app.
  rewrite drop_ge by lia.
  by rewrite app_nil_l.
Qed.

Lemma drop_app_case3 {A} (n : nat) (l1 l2 : list A):
  length l1 + length l2 <= n ->
  drop n (l1 ++ l2) = [].
Proof.
  intros.
  by rewrite drop_ge by (rewrite app_length; lia).
Qed.

Lemma split_drop_app {A} (n : nat) (l1 l2 : list A):
  (n <= length l1 /\ drop n (l1 ++ l2) = drop n l1 ++ l2)
  \/ (length l1 < n < length l1 + length l2 /\ drop n (l1 ++ l2) = drop (n - length l1) l2)
  \/ (length l1 + length l2 <= n /\ drop n (l1 ++ l2) = []).
Proof.
  intros.
  assert (n <= length l1 \/ length l1 < n < length l1 + length l2 \/ length l1 + length l2 <= n) as [?|[?|?]] by lia.
  - left; split; [done|by eapply drop_app_case1].
  - right; left; split; [done|by eapply drop_app_case2].
  - right; right; split; [done|by eapply drop_app_case3].
Qed.


Ltac split_drop_app_tac_helper n l1 l2 :=
  let H' := fresh "H'" in
  (   (assert (n <= length l1) as H' by (length_normal_form_goal; lia);
      apply (drop_app_case1 n l1 l2) in H'; try rewrite H' in *; clear H')
  ||  (assert (length l1 < n < length l1 + length l2) as H' by (length_normal_form_goal; lia);
      apply (drop_app_case2 n l1 l2) in H'; try rewrite H' in *; clear H')
  ||  (assert (length l1 + length l2 <= n) as H' by (length_normal_form_goal; lia);
      apply (drop_app_case3 n l1 l2) in H'; try rewrite H' in *; clear H')
  || (pose proof (split_drop_app n l1 l2) as [[? H']|[[? H']|[? H']]];
      try rewrite H' in *; clear H')
  ).

Ltac split_drop_app_tac :=
  repeat match goal with
  | |- context [ drop ?n (?l1 ++ ?l2) ] => split_drop_app_tac_helper n l1 l2
  | _ : context [ drop ?n (?l1 ++ ?l2) ] |- _ => split_drop_app_tac_helper n l1 l2
  end.

Lemma map_update {A} {B} {da : Inhabitant A} {db : Inhabitant B} (i : nat) (f : A -> B) (l : list A) (v : A):
  update i (map f l) (f v) = map f (update i l v).
Proof.
  intros.
  unfold update.
  rewrite map_length.
  repeat (rewrite map_take||rewrite map_drop||rewrite map_app).
  repeat f_equal.
Qed.

Lemma repeat_take_minimum {A} (v : A) (n m : nat):
  take n (repeat v m) = repeat v (minimum n m).
Proof.
  rewrite min_minimum.
  by rewrite repeat_take.
Qed.

Lemma repeat_take_case1 {A} (v : A) (n m : nat):
  n <= m ->
  take n (repeat v m) = repeat v n.
Proof.
  intros.
  rewrite repeat_take.
  repeat f_equal.
  lia.
Qed.

Lemma repeat_take_case2 {A} (v : A) (n m : nat):
  m <= n ->
  take n (repeat v m) = repeat v m.
Proof.
  intros.
  rewrite repeat_take.
  repeat f_equal.
  lia.
Qed.

Lemma repeat_take_cases {A} (v : A) (n m : nat):
  (n <= m /\ take n (repeat v m) = repeat v n)
  \/ (m <= n /\ take n (repeat v m) = repeat v m).
Proof.
  assert (n <= m \/ m <= n) as [H | H] by lia.
  - left; split; [done|eapply repeat_take_case1; done].
  - right; split; [done|eapply repeat_take_case2; done].
Qed.

Ltac repeat_take_rewrite_helper v n m :=
  let H' := fresh "H'" in
  (   (assert (n <= m) as H' by lia;
      apply (repeat_take_case1 v n m) in H';
      rewrite H' in *; clear H')
  ||  (assert (m <= n) as H' by lia;
      apply (repeat_take_case2 v n m) in H';
      rewrite H' in *; clear H')
  ||  (destruct (repeat_take_cases v n m) as [[? H']|[? ?H']];
      rewrite H' in *; clear H')
  ).

Ltac repeat_take_rewrite :=
  repeat match goal with
  | |- context [ take ?n (repeat ?v ?m) ] => repeat_take_rewrite_helper v n m
  | _ : context [ take ?n (repeat ?v ?m) ] |- _ => repeat_take_rewrite_helper v n m
  end.

Lemma help_rev_repeat {A} (n : nat) (v : A):
  repeat v (S n) = (repeat v n) ++ [v].
Proof.
  induction n; [done|].
  replace (repeat v (S n)) with (v :: repeat v n) by done.
  replace (repeat v (S (S n))) with (v :: repeat v (S n)) by done.
  by rewrite IHn.
Qed.

Lemma rev_repeat {A} (n : nat) (v : A):
  rev (repeat v n) = repeat v n.
Proof.
  induction n; [done|].
  replace (rev (repeat v (S n))) with (rev (repeat v n) ++ [v]) by done.
  rewrite help_rev_repeat.
  by rewrite IHn.
Qed.

Lemma nth_repeat_case1 {A} {d : Inhabitant A} (i n : nat) (v : A):
  i < n ->
  nth_l i (repeat v n) = v.
Proof.
  revert n.
  induction i; destruct n; [lia|done|lia| ]; intros.
  assert (i < n) by lia.
  apply IHi in H0.
  by unfold nth_l in *.
Qed.

Lemma nth_repeat_case2 {A} {d : Inhabitant A} (i n : nat) (v : A):
  i >= n ->
  nth_l i (repeat v n) = d.
Proof.
  unfold nth_l.
  intros.
  apply nth_overflow.
  length_normal_form.
  lia.
Qed.

Lemma nth_repeat_cases {A} {d : Inhabitant A} (i n : nat) (v : A):
  (i < n /\ nth_l i (repeat v n) = v)
  \/ (i >= n /\ nth_l i (repeat v n) = d).
Proof.
  assert (i <n \/ i >= n) as [?|?] by lia.
  - left; split; [done| by apply nth_repeat_case1].
  - right; split; [done| by apply nth_repeat_case2].
Qed.

Ltac nth_repeat_rewrite_helper i n v :=
  let H' := fresh "H'" in
  (   (assert (i < n) as H' by lia;
      apply (nth_repeat_case1 i n v) in H';
      rewrite H' in *; clear H')
  ||  (assert (i >= n ) as H' by lia;
      apply (nth_repeat_case2 i n v) in H';
      rewrite H' in *; clear H')
  ||  (destruct (nth_repeat_cases i n v) as [[? H']|[? ?H']];
      rewrite H' in *; clear H')
  ).

Ltac nth_repeat_rewrite :=
  repeat match goal with
  | |- context [ nth ?i (repeat ?v ?n) ] => nth_repeat_rewrite_helper i n v
  | _ : context [ nth ?i (repeat ?v ?n) ] |- _ => nth_repeat_rewrite_helper i n v
  end.

Lemma repeat_singleton {A} (v : A):
  repeat v 1 = [v].
Proof. done. Qed.

Ltac repeat_singleton_rewrite :=
  repeat (
  match goal with
    | _ : context [ repeat ?v ?n ] |- _ => ( replace n with 1 by lia; replace (repeat v 1) with [v] by (by rewrite repeat_singleton))
    | |- context [ repeat ?v ?n ] => replace n with 1 by lia; replace (repeat v 1) with [v] by (by rewrite repeat_singleton)
  end).

Ltac take_0_in_goal :=
  match goal with
    | |- context [ take ?n ?l ] => assert (n = 0) as -> by lia; rewrite take_0
  end.

Ltac take_ge_in_goal :=
  let H' := fresh "H'" in
  match goal with
    | |- context [ take ?n ?l ] => assert (length l <= n) as H' by (length_normal_form;lia); apply take_ge in H'; rewrite H'
  end.

Lemma nth_l_overflow {A} {d : Inhabitant A} (n : nat) (l : list A):
  length l <= n ->
  nth_l n l = d.
Proof.
  intros;
  unfold nth_l;
  apply nth_overflow;
  lia.
Qed.

Ltac nth_l_overflow_tac :=
  let H' := fresh "H'" in 
  match goal with
    | |- context [ nth_l ?n ?l ] => assert (length l <= n) as H' by lia; apply nth_l_overflow in H'; rewrite H' in *; clear H'
    | _ : context [ nth_l ?n ?l ] |- _ => assert (length l <= n) as H' by lia; apply nth_l_overflow in H'; rewrite H' in *; clear H'
  end.

Lemma e_firstn_app {A} (n : nat) (l1 l2 l1' l2' : list A):
  l1' = take n l1 ->
  l2' = take (n - length l1) l2 ->
  take n (l1 ++ l2) = l1' ++ l2'.
Proof. intros. subst. by rewrite firstn_app. Qed.

Lemma take_app_minimum {A} (n : nat) (l1 l2 : list A):
  take n (l1 ++ l2) = take (minimum n (length l1)) l1 ++ take (minimum (length l2) (n - (minimum n (length l1)))) l2.
Proof.
  repeat(
  match goal with
    | _ : context [ minimum ?n ?m ] |- _ => minimum_destruct_helper n m
    | |- context [ minimum ?n ?m ] => minimum_destruct_helper n m
  end); rewrite firstn_app.
  - repeat take_0_nil_by_lia. done.
  - by repeat (rewrite take_ge; try (done||lia)).
  - rewrite take_ge; try (done||lia).
    f_equal.
    rewrite take_ge; try (done||lia).
Qed.



Lemma drop_app_minimum {A} (n : nat) (l1 l2 : list A):
  drop n (l1 ++ l2) = drop (minimum n (length l1)) l1 ++ drop (minimum (length l2) (n - (minimum n (length l1)))) l2.
Proof.
  repeat(
  match goal with
    | _ : context [ minimum ?n ?m ] |- _ => minimum_destruct_helper n m
    | |- context [ minimum ?n ?m ] => minimum_destruct_helper n m
  end); rewrite skipn_app.
  - by repeat remove_drop_0_by_lia.
  - by repeat drop_ge_nil_by_lia.
  - by repeat drop_ge_nil_by_lia.
Qed.

Lemma take_take_minimum {A} (n m : nat) (l : list A):
  take n (take m l) = take (minimum n m) l.
Proof.
  rewrite take_take; repeat(
  match goal with
    | _ : context [ minimum ?n ?m ] |- _ => minimum_destruct_helper n m
    | |- context [ minimum ?n ?m ] => minimum_destruct_helper n m
  end); try rewrite <- min_minimum in *;
  try rewrite <- max_maximum in *;repeat(
  match goal with
    | _ : context [ minimum ?n ?m ] |- _ => minimum_destruct_helper n m
    | |- context [ minimum ?n ?m ] => minimum_destruct_helper n m
  end); try (lia || done).
Qed.

Ltac list_normal_form :=
  repeat (repeat  (  nat_simp
          || cons_app_rewrite
          || rewrite app_nil_l in * (* [] ++ l -> l *)
          || rewrite app_nil_r in * (* l ++ [] -> l *)
          || rewrite <- app_assoc in * (* (l1 ++ l2) ++ l3 -> l1 ++ (l2 ++ l3) *)
          || rewrite rev_app_distr in * (* rev (l1 ++ l2) -> (rev l2) ++ (rev l1) *)
          || rewrite rev_involutive in * (* rev (rev l) -> l *)
          || rewrite firstn_skipn_comm in * (* take m (drop n l) -> drop n (take (n + m) l) *)
          || rewrite firstn_all in * (* take (length l) l = l *)
          || rewrite map_flip_ends in * (* flip_ends lo hi (map f l) -> map f (flip_ends lo hi l) *)
          || rewrite <- map_rev in * (* rev (map f l) -> map f (rev l) *)
          || rewrite map_app in * (* map f (l ++ l') -> map f l ++ map f l' *)
          || rewrite map_nil in * (* map f [] -> [] *)
          || rewrite <- map_take in * (* take n (map f l) -> map f (take n l) *)
          || rewrite <- map_drop in * (* drop n (map f l) -> map f (drop n l) *)
          || rewrite drop_drop in * (* drop n (drop m l) -> drop (m + n) l *)
(*          || rewrite nth_l_nth_l_0 in * (* nth_l 0 (nth_l i l) -> nth_l i l *)*)
          || rewrite repeat_drop in * (* drop n (repeat v m) -> repeat v (m - n) *)
          || rewrite repeat_map in * (* map f (repeat v n) -> repeat (f v) n *)
          || rewrite map_update in * (* update i (map f l) (f v) -> map f (update i l v) *)
          || rewrite nth_l_nil in * (* nth_l i [] -> default *)
          || rewrite nth_l_drop in * (* nth_l i drop j l -> nth_l (i + j) l *)
          || rewrite rev_repeat in * (* rev (repeat v n) -> repeat v n *)
          || rewrite firstn_rev in * (* take n (rev l) = rev (drop (length l - n) l) *)
          || rewrite skipn_rev in * (* drop n (rev l) = rev (take (length l - n) l) *)
          || (repeat rewrite repeat_take_minimum in *; minimum_destruct)
          )
(*          || repeat_take_rewrite *)
          || (length_normal_form; try lia) (* Optimization *)
          || take_0_nil_by_lia
          || drop_ge_nil_by_lia
          || remove_take_ge_by_lia
          || remove_drop_0_by_lia
          || split_update_app_tac
(*          || split_take_take_tac*)
          || (rewrite take_take_minimum in *; minimum_destruct)
(*          || (rewrite take_app_minimum in *; minimum_destruct; repeat take_0_nil_by_lia; repeat remove_take_ge_by_lia)*)
          || split_take_app_tac
(*          || (rewrite drop_app_minimum in *; minimum_destruct; repeat drop_ge_nil_by_lia; repeat remove_drop_0_by_lia)*)
          || split_drop_app_tac
          || split_nth_l_app_tac
          || split_nth_l_map_tac
          || split_nth_l_rev_tac
          || split_nth_l_take_tac
          || split_nth_l_repeat_tac
          || rewrite nth_l_elem
          || repeat_singleton_rewrite
(*          || nth_repeat_rewrite*)
          ).