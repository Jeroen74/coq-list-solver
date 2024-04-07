From CoqListSolver Require Export list_solver.

Definition sublist {A} {_ : Inhabitant A} (n m : nat) (l : list A) :=
  drop n (take m l).

Ltac list_solver_preprocess_expand ::=
  unfold sublist.

(* Start of lemmas that are self invented *)
 
Lemma update_update {A} {_ : Inhabitant A} (i : nat) (x y : A) (l : list A) :
  update i (update i l x) y = update i l y.
Proof.
  idtac "update_update";
  time list_solver.
Qed.

Lemma sublist_lem {A} {_ : Inhabitant A} (n m p : nat) (l : list A):
  sublist n m (sublist 0 p l ++ sublist p (length l) l)
  = sublist n (m `min` p) l ++ sublist (n `max` p) m l.
Proof.
  idtac "sublist_lem";
  time list_solver.
Qed.

Lemma nth_l_app_eq {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : nat) (l l': list A):
  i < length l ->
  (nth_l i l = nth_l i (l ++ l')).
Proof.
  idtac "nth_l_app_eq".
  time list_solver.
Qed.

Lemma concat_fix_tail {A} {_ : Inhabitant A} (la lb l1 l2 l3 l3' : list A):
  la ++ lb ++ l3 = l1 ++ l2 ++ l3' ->
  length la + length lb = length l1 + length l2 ->
  l3 = l3'.
Proof.
  idtac "concat_fix_tail";
  time list_solver.
Qed.

Lemma double_rev_id {A} {_ : Inhabitant A} (l : list A) : 
  rev (rev l) = l.
Proof.
  idtac "double_rev_id";
  time list_solver.
Qed.

Lemma rev_cons_append {A} {_ : Inhabitant A} (a : A) (l1 : list A):
  rev ( a :: l1) = (rev l1) ++ [a].
Proof.
  idtac "rev_cons_append";
  time list_solver. 
Qed.

Lemma rev_app_commute {A} {_ : Inhabitant A} (l1 l2 : list A):
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  idtac "rev_app_commute";
  time list_solver. 
Qed.

Lemma app_eq_tail_cancel {A} {_ : Inhabitant A} (l1 l2 l3 l4 : list A):
  l1 ++ l4 = l2 ++ l4  -> l1 ++ l3 = l2 ++ l3.
Proof.
  idtac "app_eq_tail_cancel";
  time list_solver.
Qed.

Lemma concat_assoc {A} {_ : Inhabitant A} (l1 l2 l3 : list A): 
  ((l1 ++ l2) ++ l3) = (l1 ++ (l2 ++ l3)).
Proof.
  idtac "concat_assoc";
  time list_solver.
Qed.

Lemma rev_preserves_eq {A} {_ : Inhabitant A} (l1 l2 : list A):
  l1 = l2 -> rev l1 = rev l2.
Proof.
  idtac "reverse preserves_eq";
  time list_solver.
Qed.

Lemma rev_injective {A} {_ : Inhabitant A} (l1 l2 : list A):
  rev l1 = rev l2 -> l1 = l2.
Proof.
  idtac "rev_injective";
  time list_solver.
Qed.

Lemma left_app_cancel {A} {_ : Inhabitant A} (l1 l2 l3 : list A):
  l1 ++ l2 = l1 ++ l3 -> l2 = l3.
Proof.
  idtac "left_app_cancel";
  time list_solver. Qed.

Lemma right_app_cancel {A} {_ : Inhabitant A} (l1 l2 l3 : list A):
  l1 ++ l3 = l2 ++ l3 -> l1 = l2.
Proof.
  idtac "rigth_app_cancel";
  time list_solver.
Qed.

Lemma ex_suff_of_take {A} {_ : Inhabitant A} (l l' : list A) (n : nat):
  l = sublist 0 n l' ->
  exists x, l ++ x = l'.
Proof.
  intros.
  eexists.
  Fail [list_solver]:{
Admitted.

Lemma own_test_1 {A} {_ : Inhabitant A} (a : A) (l1 l2 : list A):
  rev ( a :: (l1 ++ (rev l2))) = l2 ++ (rev l1) ++ [a].
Proof.
  idtac "own_test_1";
  time list_solver.
Qed.

Lemma own_test_2 (a : nat) (l1 l2 : list nat):
  rev  (a + 2 :: (l1 ++ (rev l2))) = l2 ++ (rev l1) ++ [2 + a].
Proof.
  idtac "own_test_2";
  time list_solver.
Qed.

Lemma own_test_3 {A} {_ : Inhabitant A} (a b c : A) (l1 l2 l3 l4 l5 l6 l7: list A):
  l4 = (rev (l5 ++ l6)) ->
  l3 ++ l1 = l7 ->
  a = b ->
  c = b ->
  rev (((rev l1) ++ (rev l3)) ++ (rev [a]) ++ (rev l4)) 
    = (rev l6) ++ (rev l5) ++ (c :: l7).
Proof.
  idtac "own_test_3";
  time list_solver.
Qed.

Lemma own_test_4 {A} {_ : Inhabitant A} (k l m n o : list A):
  length k = length l + length m ->
  k ++ n = l ++ ( m ++ n) ->
  k = l ++ m.
Proof.
  idtac "own_test_4";
  time list_solver.
Qed.

Lemma own_test_5 {A} {_ : Inhabitant A} (l12 l1 l2 l23 l3 l3' : list A):
  l12 = l1 ++ l2 ->
  l23 = l2 ++ l3' ->
  l12 ++ l3 = l1 ++ l23 ->
  l3 = l3'.
Proof.
  idtac "own_test_5";
  time list_solver.
Qed.

Lemma own_test_6 {A} {_ : Inhabitant A} (l1 l2 l3 l4 l5 l6 : list A):
  l1 ++ l2 = l3 ++ l4 ->
  l3 ++ l4 = l5 ++ l6 ->
  l1 ++ l2 = l5 ++ l6.
Proof.
  idtac "own_test_6";
  time list_solver.
Qed.

Lemma own_test_7 {A} {_ : Inhabitant A} (la lb lc ld le lf l1 l2 l3 l4 l12 l23 la' lb' lc' ld' le' lf' l1' l2' l3' l4' l12' l23' : list A):
  l12 = la ++ lb ->
  l23 = lc ++ ld ->
  l12 = l1 ++ l2 ->
  lc ++ ld = le ++ lf ->
  le ++ lf = l2 ++ l4 ->
  l12 ++ l3 = l1 ++ l23 ->
  l12' = la' ++ lb' ->
  l23' = lc' ++ ld' ->
  l12' = l1' ++ l2' ->
  lc' ++ ld' = le' ++ lf' ->
  le' ++ lf' = l2' ++ l4' ->
  l12' ++ l3' = l1' ++ l23' ->
  l3' = l4'.
Proof.
  idtac "own_test_7".
  time list_solver.
Qed.

Lemma own_test_8 {A} {_ : Inhabitant A} (la lb lc ld l1 l1' l2 l3 l12 l23: list A):
  l12 = la ++ lb ->
  l23 = lc ++ ld ->
  l12 = l1' ++ l2 ->
  l23 = l2 ++ l3 ->
  l12 ++ l3 = l1 ++ l23 ->
  l1 = l1'.
Proof.
  idtac "own_test_8";
  intros.
  time list_solver.
Qed.

Lemma own_test_9 {A} {_ : Inhabitant A} (la lb lc ld l1 l2 l3 l4 l5 l5' : list A):
  la ++ lb = lc ++ ld ->
  la ++ l1 ++ l2 = lc ++ l3 ++ l4 ->
  l1 ++ l2 = lb ++ l5 ->
  l3 ++ l4 = ld ++ l5' ->
  l5 = l5'.
Proof.
  idtac "own_test_9";
  time list_solver.
Qed.

(* End of lemmas of lemmas that are self invented *)

(* Begin of lemmas the Coq and std++ library *)

Lemma app_eq_nil {A} {_ : Inhabitant A}  {_ : Inhabitant A} (l l':list A) : l ++ l' = [] -> l = [] /\ l' = [].
Proof.
  idtac "app_eq_nil";
  time list_solver.
Qed.

Lemma rev_app_distr {A} {_ : Inhabitant A} (x y : list A): rev (x ++ y) = rev y ++ rev x.
Proof.
  list_solver.
Qed.

Lemma rev_unit {A} {_ : Inhabitant A} (l : list A) (a : A): rev (l ++ [a]) = a :: rev l.
Proof.
  idtac "rev_unit";
  time list_solver.
Qed.

Lemma rev_eq_app {A} {_ : Inhabitant A} (l l1 l2 : list A):
  rev l = l1 ++ l2 → l = rev l2 ++ rev l1.
Proof.
  idtac "rev_eq_app";
  time list_solver.
Qed.

Lemma suffix_snoc_inv_1
  {A} {_ : Inhabitant A} (x y : A) (l1 l2 : list A):
    l1 ++ [x] `suffix_of` l2 ++ [y] → x = y.
Proof.
  unfold suffix in *;
  intros. destruct H as [k H].
  idtac "suffix_snoc_inv_1 with destruct";
  time list_solver.
Qed.

Lemma app_cons_not_nil {A} (a : A) (x y : list A):
  [] ≠ x ++ a :: y.
Proof.
  idtac "app_cons_not_nil".
  time list_solver.
Qed.

Lemma app_singleton:
  ∀ {A : Type} (l1 l2 : list A) (x : A),
    l1 = [] ∧ l2 = [x] ∨ l1 = [x] ∧ l2 = [] -> l1 ++ l2 = [x].
Proof.
  idtac "app_singleton";
  time list_solver.
Qed.

Lemma rev_involutive
   {A} {_ : Inhabitant A} (l : list A):
    rev (rev l) = l.
Proof.
  idtac "rev_involutive";
  time list_solver.
Qed.

Lemma rev_length
  {A} {_ : Inhabitant A} (l : list A):
    length (rev l) = length l.
Proof.
  idtac "rev_length";
  time list_solver.
Qed.

Lemma sublist_rev {A} {_ : Inhabitant A} (i : nat) (l : list A):
  sublist 0 i (rev l) = rev (sublist (length l - i) (length l) l).
Proof.
  idtac "sublist_rev";
  time list_solver.
Qed.

Lemma rev_nth {A} {_ : Inhabitant A} (l : list A) (n : nat):
    n < length l
    → nth_l n (rev l) =
      nth_l (length l - (n + 1)) l.
Proof.
  idtac "rev_nth";
  time list_solver.
Qed.

(* End of lemmas the Coq and std++ library *)

(* Begin From VST_make_experiment *)

Lemma VST_experiment_1 {A} {_ : Inhabitant A} (a : A) (xs : list A):
  sublist 0 (length (a :: xs)) (a :: xs) = (a :: xs).
Proof.
  idtac "VST experiment 1".
  time list_solver.
Qed.

Lemma VST_experiment_2 {A} {_ : Inhabitant A} (a : A) (xs : list A):
  sublist 1 (length (a :: xs)) (a :: xs) = xs.
Proof.
  idtac "VST experiment 2".
  time list_solver.
Qed.

Lemma VST_experiment_3 {A} {_ : Inhabitant A} (j size : nat) (l : list A):
  length l = size ->
  0 <= j ->
  size - j - 1 <= j ->
  j <= size - j ->
  (sublist (length l - length l) (length l - (size - j)) l ++ sublist j (size - j) l) ++ sublist (length l - j) (length l - 0) l = l.
Proof.
  idtac "VST experiment 3".
  time list_solver.
Qed.

Lemma VST_experiment_4 {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : nat) (al : list A):
  i >= j ->
  (i - j < size - j - (size - j - 1)) ->
  size = length al ->
  (nth_l (i - j + (size - j - 1)) al = nth_l (length al - i - 1) al).
Proof.
  idtac "VST experiment 4".
  time list_solver.
Qed.

Lemma VST_experiment_5 {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : nat) (al : list A) :
  size = length al ->
  (i - j - (size - j - (size - j - 1)) + (j + 1) >= size - j - 1) ->
  (i - j - (size - j - (size - j - 1)) + (j + 1) - (size - j - 1) < j + 1 - j) ->
  (nth_l (i - j - (size - j - (size - j - 1)) + (j + 1) - (size - j - 1) + j - j + j) al 
  = nth_l (length al - (i - (j + 1) - (size - (j + 1) - (j + 1)) + (size - (j + 1))) - 1) al).
Proof.
  idtac "VST experiment 5".
  time list_solver.
Qed.

Lemma VST_experiment_6 {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : nat) (al : list A):
  (length al = size) ->
  (j < size - j - 1) ->
  (0 <= j) ->
  (length (rev al) = length al) ->
  (nth_l (size - j - 1) al = nth_l (size - j - 1)
                            (sublist 0 j (rev al) ++
                             sublist j (size - j) al ++
                             sublist (size - j) (length al) (rev al))).
Proof.
  idtac "VST experiment 6".
  time list_solver.
Qed.

Lemma VST_experiment_7 {A} {_ : Inhabitant A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (Vint : A -> B) (j : nat) (contents : list A):
  (j < length (map Vint contents) - j - 1) ->
  (0 <= j) ->
  (j <= length (map Vint contents) - j) ->
  (length (flip_ends j (length (map Vint contents) - j) (map Vint contents)) = 
   length (map Vint contents)) ->
(update j
   (update (length (map Vint contents) - j - 1)
      (flip_ends j (length (map Vint contents) - j) (map Vint contents))
      (nth_l j
         (flip_ends j (length (map Vint contents) - j) (map Vint contents))))
   ( Vint (nth_l (length (map Vint contents) - j - 1) contents)) = 
 sublist 0 j
   (flip_ends j (length (map Vint contents) - j) (map Vint contents)) ++
 sublist (length (map Vint contents) - j - 1)
   (length (map Vint contents) - j) (map Vint contents) ++
 sublist (j + 1) (length (map Vint contents))
   (sublist 0 (length (map Vint contents) - j - 1)
      (flip_ends j (length (map Vint contents) - j) (map Vint contents)) ++
    sublist j (j + 1)
      (flip_ends j (length (map Vint contents) - j) (map Vint contents)) ++
    sublist (length (map Vint contents) - j) (length (map Vint contents))
      (flip_ends j (length (map Vint contents) - j) (map Vint contents)))).
Proof.
  idtac "VST experiment 7".
  time list_solver.
Qed.

Lemma VST_experiment_8 {A} {_ : Inhabitant A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (Vint : A -> B) (contents : list A):
  (map Vint contents) = (flip_ends 0 (length contents) (map Vint contents)).
Proof.
  idtac "VST experiment 8".
  time list_solver.
Qed.

Lemma VST_experiment_9 {A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (j : nat) (Vint : A -> B) (contents : list A):
  j >= 0 ->
  j < length contents - j - 1 ->
   (update j
      (update (length contents - j - 1)
         (flip_ends j (length contents - j) (map Vint contents))
         (nth_l j (flip_ends j (length contents - j) (map Vint contents))))
      (nth_l (length contents - j - 1)
         (flip_ends j (length contents - j) (map Vint contents))))
  = (flip_ends (j + 1) (length contents - (j + 1)) (map Vint contents)).
Proof.
  idtac "VST experiment 9".
  time list_solver.
Qed.

Lemma VST_experiment_10 {A} {_ : Inhabitant A} {B} {_ : Inhabitant B} (contents : list A) (Vint : A -> B) (j : nat):
  (length contents >= 0) ->
  (j >= length contents - j - 1) ->
  (0 <= j) ->
  (j <= length contents - j) ->
  (flip_ends j (length contents - j) (map Vint contents)) = (map Vint (rev contents)).
Proof.
  idtac "VST experiment 10".
  time list_solver.
Qed.

Lemma VST_experiment_11 {A} {B} {C} {_ : Inhabitant A} {_ : Inhabitant B} {_ : Inhabitant C} (repr : A -> B) (Vint : B -> C) (al : list A) (i : nat):
(map Vint (map repr al) = update i (map Vint (map repr al))
                                (Vint (repr (nth_l i al)))).
Proof.
  idtac "VST experiment 11".
  time list_solver.
Qed.

Lemma VST_experiment_12 {A} {_ : Inhabitant A} {B} {_ : Inhabitant B}{Vbyte : A -> B} (zero : A) (n : nat) (Vundef : B) (ls ld : list A):
(length
   (map Vbyte (ld ++ [zero]) ++
    repeat Vundef ( (n - (length ld + 1)))) = 
 Nat.max 0 n) ->
(length ld + length ls < n) ->
(length (map Vbyte (ls ++ [zero])) = Nat.max 0 (length ls + 1)) ->
(n = length
       (map Vbyte ld ++
        map Vbyte [zero] ++
        repeat Vundef ( (n - (length ld + 1))))).
Proof.
  idtac "VST experiment 12".
  time list_solver.
Qed.

Lemma VST_experiment_13 {A} {_ : Inhabitant A} {B} {_ : Inhabitant B} (n : nat) (zero : A) (Vundef: B) (Vbyte : A -> B) (ls ld : list A):
(length ld + length ls < n) ->
(length
   (map Vbyte (ld ++ [zero]) ++
    repeat Vundef ( (n - (length ld + 1)))) = 
 Nat.max 0 n) ->
 (length (map Vbyte (ls ++ [zero])) = Nat.max 0 (length ls + 1)) ->
(n = length (map Vbyte ld ++ repeat Vundef ((n - length ld)))).
Proof.
  idtac "VST experiment 13".
  time list_solver.
Qed.

Lemma VST_experiment_14 {A} {_ : Inhabitant A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (zero : A) (Vundef: B) (Vbyte : A -> B) (ld ls : list A) (n : nat):
length ld + length ls < n ->
(map Vbyte (ld ++ ls) ++
    update 0 (repeat Vundef (n - (length ld + length ls)))
      (Vbyte zero)) = (map Vbyte ((ld ++ ls) ++ [zero]) ++
        repeat Vundef (n - (length ld + length ls + 1))).
Proof.
  idtac "VST experiment 14";
  time list_solver.
Qed.

(* Eind From VST_make_experiment *)

(* Begin from verif_revarray.v *)

Lemma flip_fact_1: forall A {d: Inhabitant A} (size : nat) (contents: list A) j,
  length contents = size ->
  0 <= j ->
  size - j - 1 <= j <= size - j ->
  flip_ends j (size - j) contents = rev contents.
Proof.
  idtac "flip_fact_1";
  time list_solver.
Qed.

Lemma flip_fact_3:
 forall A {d: Inhabitant A} (al: list A) j size,
  size = length al ->
  0 <= j ->
  j < size - j - 1 ->
sublist 0 j (flip_ends j (size - j) al) ++
sublist (size - j - 1) (size - j) al ++
sublist (j + 1) size
  (sublist 0 (size - j - 1) (flip_ends j (size - j) al) ++
   sublist j (j + 1) (flip_ends j (size - j) al) ++
   sublist (size - j) size (flip_ends j (size - j) al)) =
flip_ends (j + 1) (size - (j + 1)) al.
Proof.
  idtac "test flip_fact_3".
  time list_solver.
Qed.

Lemma flip_ends_map
  {A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (F: A -> B) lo hi (al: list A):
  flip_ends lo hi (map F al) = map F (flip_ends lo hi al).
Proof.
  idtac "flip_ends_map".
  time list_solver.
Qed.

Lemma flip_fact_2:
  forall {A} {_ : Inhabitant A}{d: Inhabitant A} (al: list A) size j,
 length al = size ->
  j < size - j - 1 ->
   0 <= j ->
  nth_l (size - j - 1) al =
  nth_l (size - j - 1) (flip_ends j (size - j) al).
Proof.
  idtac "flip_fact_2".
  time list_solver.
Qed.

(* Eind from verif_revarray.v *)
