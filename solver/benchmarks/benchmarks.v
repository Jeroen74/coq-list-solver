Require Import Running_benchmarks_own_solver.

(* By default our solver is tested.
  To test the solver from VST apply the following steps:
    1. Make sure you have installed it correcly
    2. Comment the first line of the document
    3. Replace everywhere in the document ': nat' with ': Z'
    4. Replace everywhere in the document 'Nat.' with 'Nat.'
    5. Replace everywhere in the document 'list nat' with 'list Z'
    6. Uncomment the line below *) 

(*Require Import Running_benchmarks_VST_solver.*)

(* Start of lemmas that are self invented *)
 
Lemma Update_Update {A} {_ : Inhabitant A} (i : nat) (x y : A) (l : list A) :
  Update i (Update i l x) y = Update i l y.
Proof.
  idtac "update_update";
  time list_solver.
Qed.

Lemma sublist_lem {A} {_ : Inhabitant A} (n m p : nat) (l : list A):
  sublist n m (sublist 0 p l ++ sublist p (Length l) l)
  = sublist n (m `min` p) l ++ sublist (n `max` p) m l.
Proof.
  idtac "sublist_lem";
  time list_solver.
Qed.

Lemma nth_l_app_eq {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : nat) (l l': list A):
  i < Length l ->
  (Nth i l = Nth i (l ++ l')).
Proof.
  idtac "nth_l_app_eq".
  time list_solver.
Qed.

Lemma concat_fix_tail {A} {_ : Inhabitant A} (la lb l1 l2 l3 l3' : list A):
  la ++ lb ++ l3 = l1 ++ l2 ++ l3' ->
  Length la + Length lb = Length l1 + Length l2 ->
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
  Length k = Length l + Length m ->
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
    Length (rev l) = Length l.
Proof.
  idtac "rev_length";
  time list_solver.
Qed.

Lemma sublist_rev {A} {_ : Inhabitant A} (i : nat) (l : list A):
  sublist 0 i (rev l) = rev (sublist (Length l - i) (Length l) l).
Proof.
  idtac "sublist_rev";
  time list_solver.
Qed.

Lemma rev_nth {A} {_ : Inhabitant A} (l : list A) (n : nat):
    n < Length l
    → Nth n (rev l) =
      Nth (Length l - (n + 1)) l.
Proof.
  idtac "rev_nth";
  time list_solver.
Qed.

(* End of lemmas the Coq and std++ library *)

(* Begin From VST_make_experiment *)

Lemma VST_experiment_1 {A} {_ : Inhabitant A} (a : A) (xs : list A):
  sublist 0 (Length (a :: xs)) (a :: xs) = (a :: xs).
Proof.
  idtac "VST experiment 1".
  time list_solver.
Qed.

Lemma VST_experiment_2 {A} {_ : Inhabitant A} (a : A) (xs : list A):
  sublist 1 (Length (a :: xs)) (a :: xs) = xs.
Proof.
  idtac "VST experiment 2".
  time list_solver.
Qed.

Lemma VST_experiment_3 {A} {_ : Inhabitant A} (j size : nat) (l : list A):
  Length l = size ->
  0 <= j ->
  size - j - 1 <= j ->
  j <= size - j ->
  (sublist (Length l - Length l) (Length l - (size - j)) l ++ sublist j (size - j) l) ++ sublist (Length l - j) (Length l - 0) l = l.
Proof.
  idtac "VST experiment 3".
  time list_solver.
Qed.

Lemma VST_experiment_4 {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : nat) (al : list A):
  i >= j ->
  (i - j < size - j - (size - j - 1)) ->
  size = Length al ->
  (Nth (i - j + (size - j - 1)) al = Nth (Length al - i - 1) al).
Proof.
  idtac "VST experiment 4".
  time list_solver.
Qed.

Lemma VST_experiment_5 {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : nat) (al : list A) :
  size = Length al ->
  (i - j - (size - j - (size - j - 1)) + (j + 1) >= size - j - 1) ->
  (i - j - (size - j - (size - j - 1)) + (j + 1) - (size - j - 1) < j + 1 - j) ->
  (Nth (i - j - (size - j - (size - j - 1)) + (j + 1) - (size - j - 1) + j - j + j) al 
  = Nth (Length al - (i - (j + 1) - (size - (j + 1) - (j + 1)) + (size - (j + 1))) - 1) al).
Proof.
  idtac "VST experiment 5".
  time list_solver.
Qed.

Lemma VST_experiment_6 {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : nat) (al : list A):
  (Length al = size) ->
  (j < size - j - 1) ->
  (0 <= j) ->
  (Length (rev al) = Length al) ->
  (Nth (size - j - 1) al = Nth (size - j - 1)
                            (sublist 0 j (rev al) ++
                             sublist j (size - j) al ++
                             sublist (size - j) (Length al) (rev al))).
Proof.
  idtac "VST experiment 6".
  time list_solver.
Qed.

Lemma VST_experiment_7 {A} {_ : Inhabitant A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (Vint : A -> B) (j : nat) (contents : list A):
  (j < Length (map Vint contents) - j - 1) ->
  (0 <= j) ->
  (j <= Length (map Vint contents) - j) ->
  (Length (Flip_ends j (Length (map Vint contents) - j) (map Vint contents)) = 
   Length (map Vint contents)) ->
(Update j
   (Update (Length (map Vint contents) - j - 1)
      (Flip_ends j (Length (map Vint contents) - j) (map Vint contents))
      (Nth j
         (Flip_ends j (Length (map Vint contents) - j) (map Vint contents))))
   ( Vint (Nth (Length (map Vint contents) - j - 1) contents)) = 
 sublist 0 j
   (Flip_ends j (Length (map Vint contents) - j) (map Vint contents)) ++
 sublist (Length (map Vint contents) - j - 1)
   (Length (map Vint contents) - j) (map Vint contents) ++
 sublist (j + 1) (Length (map Vint contents))
   (sublist 0 (Length (map Vint contents) - j - 1)
      (Flip_ends j (Length (map Vint contents) - j) (map Vint contents)) ++
    sublist j (j + 1)
      (Flip_ends j (Length (map Vint contents) - j) (map Vint contents)) ++
    sublist (Length (map Vint contents) - j) (Length (map Vint contents))
      (Flip_ends j (Length (map Vint contents) - j) (map Vint contents)))).
Proof.
  idtac "VST experiment 7".
  time list_solver.
Qed.

Lemma VST_experiment_8 {A} {_ : Inhabitant A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (Vint : A -> B) (contents : list A):
  (map Vint contents) = (Flip_ends 0 (Length contents) (map Vint contents)).
Proof.
  idtac "VST experiment 8".
  time list_solver.
Qed.

Lemma VST_experiment_9 {A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (j : nat) (Vint : A -> B) (contents : list A):
  j >= 0 ->
  j < Length contents - j - 1 ->
   (Update j
      (Update (Length contents - j - 1)
         (Flip_ends j (Length contents - j) (map Vint contents))
         (Nth j (Flip_ends j (Length contents - j) (map Vint contents))))
      (Nth (Length contents - j - 1)
         (Flip_ends j (Length contents - j) (map Vint contents))))
  = (Flip_ends (j + 1) (Length contents - (j + 1)) (map Vint contents)).
Proof.
  idtac "VST experiment 9".
  time list_solver.
Qed.

Lemma VST_experiment_10 {A} {_ : Inhabitant A} {B} {_ : Inhabitant B} (contents : list A) (Vint : A -> B) (j : nat):
  (Length contents >= 0) ->
  (j >= Length contents - j - 1) ->
  (0 <= j) ->
  (j <= Length contents - j) ->
  (Flip_ends j (Length contents - j) (map Vint contents)) = (map Vint (rev contents)).
Proof.
  idtac "VST experiment 10".
  time list_solver.
Qed.

Lemma VST_experiment_11 {A} {B} {C} {_ : Inhabitant A} {_ : Inhabitant B} {_ : Inhabitant C} (repr : A -> B) (Vint : B -> C) (al : list A) (i : nat):
(map Vint (map repr al) = Update i (map Vint (map repr al))
                                (Vint (repr (Nth i al)))).
Proof.
  idtac "VST experiment 11".
  time list_solver.
Qed.

Lemma VST_experiment_12 {A} {_ : Inhabitant A} {B} {_ : Inhabitant B}{Vbyte : A -> B} (zero : A) (n : nat) (Vundef : B) (ls ld : list A):
(Length
   (map Vbyte (ld ++ [zero]) ++
    Repeat Vundef ( (n - (Length ld + 1)))) = 
 Nat.max 0 n) ->
(Length ld + Length ls < n) ->
(Length (map Vbyte (ls ++ [zero])) = Nat.max 0 (Length ls + 1)) ->
(n = Length
       (map Vbyte ld ++
        map Vbyte [zero] ++
        Repeat Vundef ( (n - (Length ld + 1))))).
Proof.
  idtac "VST experiment 12".
  time list_solver.
Qed.

Lemma VST_experiment_13 {A} {_ : Inhabitant A} {B} {_ : Inhabitant B} (n : nat) (zero : A) (Vundef: B) (Vbyte : A -> B) (ls ld : list A):
(Length ld + Length ls < n) ->
(Length
   (map Vbyte (ld ++ [zero]) ++
    Repeat Vundef ( (n - (Length ld + 1)))) = 
 Nat.max 0 n) ->
 (Length (map Vbyte (ls ++ [zero])) = Nat.max 0 (Length ls + 1)) ->
(n = Length (map Vbyte ld ++ Repeat Vundef ((n - Length ld)))).
Proof.
  idtac "VST experiment 13".
  time list_solver.
Qed.

Lemma VST_experiment_14 {A} {_ : Inhabitant A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (zero : A) (Vundef: B) (Vbyte : A -> B) (ld ls : list A) (n : nat):
Length ld + Length ls < n ->
(map Vbyte (ld ++ ls) ++
    Update 0 (Repeat Vundef (n - (Length ld + Length ls)))
      (Vbyte zero)) = (map Vbyte ((ld ++ ls) ++ [zero]) ++
        Repeat Vundef (n - (Length ld + Length ls + 1))).
Proof.
  idtac "VST experiment 14";
  time list_solver.
Qed.

(* Eind From VST_make_experiment *)

(* Begin from verif_revarray.v *)

Lemma flip_fact_1: forall A {d: Inhabitant A} (size : nat) (contents: list A) j,
  Length contents = size ->
  0 <= j ->
  size - j - 1 <= j <= size - j ->
  Flip_ends j (size - j) contents = rev contents.
Proof.
  idtac "flip_fact_1";
  time list_solver.
Qed.

Lemma flip_fact_3:
 forall A {d: Inhabitant A} (al: list A) j size,
  size = Length al ->
  0 <= j ->
  j < size - j - 1 ->
sublist 0 j (Flip_ends j (size - j) al) ++
sublist (size - j - 1) (size - j) al ++
sublist (j + 1) size
  (sublist 0 (size - j - 1) (Flip_ends j (size - j) al) ++
   sublist j (j + 1) (Flip_ends j (size - j) al) ++
   sublist (size - j) size (Flip_ends j (size - j) al)) =
Flip_ends (j + 1) (size - (j + 1)) al.
Proof.
  idtac "test flip_fact_3".
  time list_solver.
Qed.

Lemma Flip_ends_map
  {A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (F: A -> B) lo hi (al: list A):
  Flip_ends lo hi (map F al) = map F (Flip_ends lo hi al).
Proof.
  idtac "flip_ends_map".
  time list_solver.
Qed.

Lemma flip_fact_2:
  forall {A} {_ : Inhabitant A}{d: Inhabitant A} (al: list A) size j,
 Length al = size ->
  j < size - j - 1 ->
   0 <= j ->
  Nth (size - j - 1) al =
  Nth (size - j - 1) (Flip_ends j (size - j) al).
Proof.
  idtac "flip_fact_2".
  time list_solver.
Qed.

(* Eind from verif_revarray.v *)