From stdpp Require Import list.

Class Inhabitant (A: Type) := default : A.

Definition nth_l {A} `{Inhabitant A} (i : nat) (l : list A) :=
  nth i l default.
(*  take 1 ( (drop i l) ++ [default] ).*)

Definition update {A} `{Inhabitant A} (i : nat) (l : list A) (v : A) :=
  take (length l) (take i l ++ [v] ++ drop (i + 1) l).

Definition flip_ends {A} lo hi (contents: list A) :=
  drop 0 (take lo (rev (contents)))
  ++ drop lo (take hi contents)
  ++ drop hi (take (length contents) (rev contents)).

Definition minimum (n m : nat) : nat :=
  match (le_dec n m) with
    | left _ => n
    | right _ => m
  end.

Lemma min_minimum (n m : nat):
  (minimum n m) = n `min` m.
Proof.
  unfold minimum.
  destruct (le_dec n m); lia.
Qed.

Definition maximum (n m : nat) : nat := 
  match (ge_dec n m) with
    | left _ => n
    | right _ => m
  end.


Lemma max_maximum (n m : nat):
  (maximum n m) = n `max` m.
Proof.
  unfold maximum.
  destruct (ge_dec n m); lia.
Qed.