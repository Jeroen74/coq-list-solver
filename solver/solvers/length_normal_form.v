From stdpp Require Import list.
From CoqListSolver Require Import definitions.


Lemma take_length_minimum {A} (l : list A) (n : nat):
  length (take n l) = minimum n (length l).
Proof.
  rewrite min_minimum.
  apply take_length.
Qed.

Lemma minimum_case1 n m :
  m <= n -> minimum n m = m.
Proof. rewrite min_minimum; lia. Qed.

Lemma minimum_case2 n m :
  n <= m -> minimum n m = n.
Proof. rewrite min_minimum; lia. Qed.

Lemma minimum_split n m :
  (n <= m /\ minimum n m = n)
  \/ (m < n /\ minimum n m = m).
Proof.
  assert (n <= m \/ m < n) as [?|?] by lia.
  - left; split; [lia|by apply minimum_case2;lia].
  - right; split; [lia|by apply minimum_case1;lia].
Qed.

Ltac minimum_destruct_helper n m :=
  let H' := fresh "H'" in
  (assert (m <= n) as H' by lia; apply minimum_case1 in H'; try rewrite H' in *; clear H')
  || (assert (n <= m ) as H' by lia; apply minimum_case2 in H'; try rewrite H' in *; clear H')
  || (destruct (minimum_split n m) as [[? H']|[? H']]; try rewrite H' in *; clear H').

Ltac minimum_destruct :=
  repeat(
  match goal with
    | _ : context [ minimum ?n ?m ] |- _ => minimum_destruct_helper n m
    | |- context [ minimum ?n ?m ] => minimum_destruct_helper n m
  end).

Lemma maximum_case1 n m :
  m <= n -> maximum n m = n.
Proof. rewrite max_maximum; lia. Qed.

Lemma maximum_case2 n m :
  n <= m -> maximum n m = m.
Proof. rewrite max_maximum; lia. Qed.

Lemma maximum_split n m :
  (n <= m /\ maximum n m = m)
  \/ (m < n /\ maximum n m = n).
Proof.
  assert (n <= m \/ m < n) as [?|?] by lia; rewrite max_maximum.
  - left; split; [done|lia].
  - right; split; [done|lia].
Qed.

Ltac maximum_destruct_helper m n :=
  let H' := fresh "H'" in
  let H'' := fresh "H''" in
  (assert (n <= m) as H' by lia; apply maximum_case1 in H'; try rewrite H' in *; clear H')
  || (assert (m <= n) as H' by lia; apply maximum_case2 in H'; try rewrite H' in *; clear H')
  || (destruct (maximum_split n m) as [[? H']|[? H']]; try rewrite H' in *; clear H').

Ltac maximum_destruct :=
  repeat(
  match goal with
  | _ : context [ maximum ?n ?m ] |- _ => maximum_destruct_helper n m
  | |- context [maximum ?n ?m ] => maximum_destruct_helper n m
  end).

Ltac min_max_destruct :=
  try rewrite <- min_minimum in *;
  try rewrite <- max_maximum in *;
  minimum_destruct;
  maximum_destruct.

Lemma update_length {A} `{Inhabitant A} (i : nat) (l : list A) (v : A) :
  length (update i l v) = length l.
Proof.
  revert l i v.
  induction l; intros; [done|].
  destruct i.
  - simpl. f_equal. unfold update. simpl. 
    rewrite take_length. rewrite drop_length.
    lia.
  - unfold update in *. simpl. simpl in *. by rewrite IHl.
Qed.

Lemma flip_ends_length {A} lo hi (l : list A) :
  length (flip_ends lo hi l) = length l + (length (take lo l) - hi).
Proof.
  intros.
  unfold flip_ends.
  repeat (rewrite app_length).
  repeat (rewrite drop_length).
  repeat (rewrite take_length).
  repeat (rewrite rev_length).
  lia.
Qed.

Lemma singleton_length {A} (x : A):
  length [x] = 1.
Proof. by simpl. Qed.

Tactic Notation "length_normal_form_goal_helper" :=
  repeat  (  rewrite nil_length (* length [] -> 0 *)
          || rewrite rev_length (* length (rev l) -> length l *)
          || rewrite app_length (* length (l1 ++ l2) -> length l1 + length l2 *)
          || rewrite drop_length (* length (drop n l) -> length l - n *)
          || rewrite update_length (* length (update i l v) -> length l *)
          || rewrite repeat_length (* length (repeat v n) -> n *)
          || rewrite map_length (* length (map f l) -> length l *)
          || rewrite flip_ends_length (* length (flip_ends lo hi l) -> length l + length (take lo l) - hi *)
          || rewrite singleton_length (* length [x] -> 1 *)
          ).

Lemma take_length_case1 {A} (n : nat) (l : list A):
  length l <= n ->
  length (take n l) = length l.
Proof.
  intros.
  rewrite firstn_length.
  lia.
Qed.

Lemma take_length_case2 {A} (n : nat) (l : list A):
  n <= length l ->
  length (take n l) = n.
Proof.
  intros.
  rewrite firstn_length.
  lia.
Qed.

Lemma split_take_length {A} (n len' : nat) (l : list A):
  (n < (length l) /\ length (take n l) = n)
  \/ ((length l) <= n /\ length (take n l) = (length l)).
Proof.
  intros.
  assert (n < (length l) \/ (length l) <= n) as [?|?] by lia; [left|right];
  (split; [done|rewrite firstn_length; lia]).
Qed.

Ltac split_take_length_tac :=
  let H' := fresh "H'" in
  let Hl := fresh "Hl" in
  let Hr := fresh "Hr" in
  match goal with
  | |- context [ length (take ?n ?l) ] => 
        (   (assert (length l <= n) as H' by (length_normal_form_goal_helper; lia);
            apply take_length_case1 in H'; try rewrite H' in *; clear H')
        ||  (assert (n <= length l) as H' by (length_normal_form_goal_helper; lia);
            apply take_length_case2 in H'; try rewrite H' in *; clear H')
        ||  (destruct (split_take_length n (length l) l) as [[? Hl]|[? Hr]];
            [try rewrite Hl in *; clear Hl|try rewrite Hr in *; clear Hr])
        )
  end.

Tactic Notation "length_normal_form_goal" :=
  repeat (length_normal_form_goal_helper
          || split_take_length_tac ).

Tactic Notation "length_normal_form_simpl" :=
  repeat (rewrite nil_length in * (* length [] -> 0 *)
        || rewrite rev_length in * (* length (rev l) -> length l *)
        || rewrite app_length in * (* length (l1 ++ l2) -> length l1 + length l2 *)
        || rewrite drop_length in * (* length (drop n l) -> length l - n *)
        || rewrite update_length in * (* length (update i l v) -> length l *)
        || rewrite repeat_length in * (* length (repeat v n) -> n *)
        || rewrite map_length in * (* length (map f l) -> length l *)
        || rewrite singleton_length in * (* length [x] -> 1 *)
        || rewrite flip_ends_length in * ). (* length (flip_ends lo hi l) -> length l + length (take lo l) - hi *)

Ltac split_take_length_tac_in_all_helper n l :=
  let H' := fresh "H'" in
  let Hl := fresh "Hl" in
  let Hr := fresh "Hr" in
  (   (assert (length l <= n) as H' by lia;
      apply take_length_case1 in H'; try rewrite H' in *; clear H')
  ||  (assert (n <= length l) as H' by lia;
      apply take_length_case2 in H'; try rewrite H' in *; clear H')
  ||  (destruct (split_take_length n (length l) l) as [[? Hl]|[? Hr]];
      [try rewrite Hl in *; clear Hl| try rewrite Hr in *; clear Hr])
  ).

Ltac split_take_length_tac_in_all :=
  let H' := fresh "H'" in
  let Hl := fresh "Hl" in
  let Hr := fresh "Hr" in
  repeat match goal with
  | _ : context [ length (take ?n ?l) ] |- _ => split_take_length_tac_in_all_helper n l
  | |- context [ length (take ?n ?l) ] => split_take_length_tac_in_all_helper n l
  end.

Ltac length_normal_form :=
  repeat (rewrite nil_length in * (* length [] -> 0 *)
        || rewrite rev_length in * (* length (rev l) -> length l *)
        || rewrite app_length in * (* length (l1 ++ l2) -> length l1 + length l2 *)
        || rewrite drop_length in * (* length (drop n l) -> length l - n *)
        || rewrite update_length in * (* length (update i l v) -> length l *)
        || rewrite repeat_length in * (* length (repeat v n) -> n *)
        || rewrite map_length in * (* length (map f l) -> length l *)
        || rewrite singleton_length in * (* length [x] -> 1 *)
        || rewrite flip_ends_length in * (* length (flip_ends lo hi l) -> length l + length (take lo l) - hi *)
        || (rewrite take_length_minimum in *; minimum_destruct)
        ).
