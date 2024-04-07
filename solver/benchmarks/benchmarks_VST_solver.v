Require Export stdpp.tactics.
Require Export stdpp.list.
Require Export VST.zlist.list_solver.

Open Scope Z_scope.

Global Hint Rewrite @Zlength_rev : Zlength.
Global Hint Rewrite @Znth_rev  using Zlength_solve : Znth.

Definition flip_ends {A} {_ : Inhabitant A} lo hi (contents: list A) :=
  sublist 0 lo (rev contents)
  ++ sublist lo hi contents
  ++ sublist hi (Zlength contents) (rev contents).

Ltac preprocess :=
  unfold flip_ends.

Ltac list_solver :=
  list_solve.

(* Start of lemmas that are self invented *)
 
Lemma upd_Znth_upd_Znth {A} {_ : Inhabitant A} (i : Z) (x y : A) (l : list A) :
  upd_Znth i (upd_Znth i l x) y = upd_Znth i l y.
Proof.
  idtac "upd_Znth_upd_Znth";
  time list_solver.
Qed.

Lemma sublist_lem {A} {_ : Inhabitant A} (n m p : Z) (l : list A):
  sublist n m (sublist 0 p l ++ sublist p (Zlength l) l)
  = sublist n (m `min` p) l ++ sublist (n `max` p) m l.
Proof.
  idtac "sublist_lem";
  time list_solver.
Qed.

Lemma nth_l_app_eq {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : Z) (l l': list A):
  i < Zlength l ->
  (Znth i l = Znth i (l ++ l')).
Proof.
  idtac "nth_l_app_eq".
  time list_solver.
Qed.

Lemma concat_fix_tail {A} {_ : Inhabitant A} (la lb l1 l2 l3 l3' : list A):
  la ++ lb ++ l3 = l1 ++ l2 ++ l3' ->
  Zlength la + Zlength lb = Zlength l1 + Zlength l2 ->
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

Lemma ex_suff_of_take {A} {_ : Inhabitant A} (l l' : list A) (n : Z):
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

Lemma own_test_2 (a : Z) (l1 l2 : list Z):
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
  Zlength k = Zlength l + Zlength m ->
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

Lemma rev_Zlength
  {A} {_ : Inhabitant A} (l : list A):
    Zlength (rev l) = Zlength l.
Proof.
  idtac "rev_Zlength";
  time list_solver.
Qed.

Lemma sublist_rev {A} {_ : Inhabitant A} (i : Z) (l : list A):
  sublist 0 i (rev l) = rev (sublist (Zlength l - i) (Zlength l) l).
Proof.
  idtac "sublist_rev";
  time list_solver.
Qed.

Lemma rev_nth {A} {_ : Inhabitant A} (l : list A) (n : Z):
    n < Zlength l
    → Znth n (rev l) =
      Znth (Zlength l - (n + 1)) l.
Proof.
  idtac "rev_nth";
  time list_solver.
Qed.

(* End of lemmas the Coq and std++ library *)

(* Begin From VST_make_experiment *)

Lemma VST_experiment_1 {A} {_ : Inhabitant A} (a : A) (xs : list A):
  sublist 0 (Zlength (a :: xs)) (a :: xs) = (a :: xs).
Proof.
  idtac "VST experiment 1".
  time list_solver.
Qed.

Lemma VST_experiment_2 {A} {_ : Inhabitant A} (a : A) (xs : list A):
  sublist 1 (Zlength (a :: xs)) (a :: xs) = xs.
Proof.
  idtac "VST experiment 2".
  time list_solver.
Qed.

Lemma VST_experiment_3 {A} {_ : Inhabitant A} (j size : Z) (l : list A):
  Zlength l = size ->
  0 <= j ->
  size - j - 1 <= j ->
  j <= size - j ->
  (sublist (Zlength l - Zlength l) (Zlength l - (size - j)) l ++ sublist j (size - j) l) ++ sublist (Zlength l - j) (Zlength l - 0) l = l.
Proof.
  idtac "VST experiment 3".
  time list_solver.
Qed.

Lemma VST_experiment_4 {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : Z) (al : list A):
  i >= j ->
  (i - j < size - j - (size - j - 1)) ->
  size = Zlength al ->
  (Znth (i - j + (size - j - 1)) al = Znth (Zlength al - i - 1) al).
Proof.
  idtac "VST experiment 4".
  time list_solver.
Qed.

Lemma VST_experiment_5 {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : Z) (al : list A) :
  size = Zlength al ->
  (i - j - (size - j - (size - j - 1)) + (j + 1) >= size - j - 1) ->
  (i - j - (size - j - (size - j - 1)) + (j + 1) - (size - j - 1) < j + 1 - j) ->
  (Znth (i - j - (size - j - (size - j - 1)) + (j + 1) - (size - j - 1) + j - j + j) al 
  = Znth (Zlength al - (i - (j + 1) - (size - (j + 1) - (j + 1)) + (size - (j + 1))) - 1) al).
Proof.
  idtac "VST experiment 5".
  time list_solver.
Qed.

Lemma VST_experiment_6 {A} {_ : Inhabitant A} {d : Inhabitant A} (i j size : Z) (al : list A):
  (Zlength al = size) ->
  (j < size - j - 1) ->
  (0 <= j) ->
  (Zlength (rev al) = Zlength al) ->
  (Znth (size - j - 1) al = Znth (size - j - 1)
                            (sublist 0 j (rev al) ++
                             sublist j (size - j) al ++
                             sublist (size - j) (Zlength al) (rev al))).
Proof.
  idtac "VST experiment 6".
  time list_solver.
Qed.

Lemma VST_experiment_7 {A} {_ : Inhabitant A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (Vint : A -> B) (j : Z) (contents : list A):
  (j < Zlength (map Vint contents) - j - 1) ->
  (0 <= j) ->
  (j <= Zlength (map Vint contents) - j) ->
  (Zlength (flip_ends j (Zlength (map Vint contents) - j) (map Vint contents)) = 
   Zlength (map Vint contents)) ->
(upd_Znth j
   (upd_Znth (Zlength (map Vint contents) - j - 1)
      (flip_ends j (Zlength (map Vint contents) - j) (map Vint contents))
      (Znth j
         (flip_ends j (Zlength (map Vint contents) - j) (map Vint contents))))
   ( Vint (Znth (Zlength (map Vint contents) - j - 1) contents)) = 
 sublist 0 j
   (flip_ends j (Zlength (map Vint contents) - j) (map Vint contents)) ++
 sublist (Zlength (map Vint contents) - j - 1)
   (Zlength (map Vint contents) - j) (map Vint contents) ++
 sublist (j + 1) (Zlength (map Vint contents))
   (sublist 0 (Zlength (map Vint contents) - j - 1)
      (flip_ends j (Zlength (map Vint contents) - j) (map Vint contents)) ++
    sublist j (j + 1)
      (flip_ends j (Zlength (map Vint contents) - j) (map Vint contents)) ++
    sublist (Zlength (map Vint contents) - j) (Zlength (map Vint contents))
      (flip_ends j (Zlength (map Vint contents) - j) (map Vint contents)))).
Proof.
  idtac "VST experiment 7".
  time list_solver.
Qed.

Lemma VST_experiment_8 {A} {_ : Inhabitant A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (Vint : A -> B) (contents : list A):
  (map Vint contents) = (flip_ends 0 (Zlength contents) (map Vint contents)).
Proof.
  idtac "VST experiment 8".
  time list_solver.
Qed.

Lemma VST_experiment_9 {A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (j : Z) (Vint : A -> B) (contents : list A):
  j >= 0 ->
  j < Zlength contents - j - 1 ->
   (upd_Znth j
      (upd_Znth (Zlength contents - j - 1)
         (flip_ends j (Zlength contents - j) (map Vint contents))
         (Znth j (flip_ends j (Zlength contents - j) (map Vint contents))))
      (Znth (Zlength contents - j - 1)
         (flip_ends j (Zlength contents - j) (map Vint contents))))
  = (flip_ends (j + 1) (Zlength contents - (j + 1)) (map Vint contents)).
Proof.
  idtac "VST experiment 9".
  time list_solver.
Qed.

Lemma VST_experiment_10 {A} {_ : Inhabitant A} {B} {_ : Inhabitant B} (contents : list A) (Vint : A -> B) (j : Z):
  (Zlength contents >= 0) ->
  (j >= Zlength contents - j - 1) ->
  (0 <= j) ->
  (j <= Zlength contents - j) ->
  (flip_ends j (Zlength contents - j) (map Vint contents)) = (map Vint (rev contents)).
Proof.
  idtac "VST experiment 10".
  time list_solver.
Qed.

Lemma VST_experiment_11 {A} {B} {C} {_ : Inhabitant A} {_ : Inhabitant B} {_ : Inhabitant C} (repr : A -> B) (Vint : B -> C) (al : list A) (i : Z):
(map Vint (map repr al) = upd_Znth i (map Vint (map repr al))
                                (Vint (repr (Znth i al)))).
Proof.
  idtac "VST experiment 11".
  time list_solver.
Qed.

Lemma VST_experiment_12 {A} {_ : Inhabitant A} {B} {_ : Inhabitant B}{Vbyte : A -> B} (zero : A) (n : Z) (Vundef : B) (ls ld : list A):
(Zlength
   (map Vbyte (ld ++ [zero]) ++
    Zrepeat Vundef ( (n - (Zlength ld + 1)))) = 
 Z.max 0 n) ->
(Zlength ld + Zlength ls < n) ->
(Zlength (map Vbyte (ls ++ [zero])) = Z.max 0 (Zlength ls + 1)) ->
(n = Zlength
       (map Vbyte ld ++
        map Vbyte [zero] ++
        Zrepeat Vundef ( (n - (Zlength ld + 1))))).
Proof.
  idtac "VST experiment 12".
  time list_solver.
Qed.

Lemma VST_experiment_13 {A} {_ : Inhabitant A} {B} {_ : Inhabitant B} (n : Z) (zero : A) (Vundef: B) (Vbyte : A -> B) (ls ld : list A):
(Zlength ld + Zlength ls < n) ->
(Zlength
   (map Vbyte (ld ++ [zero]) ++
    Zrepeat Vundef ( (n - (Zlength ld + 1)))) = 
 Z.max 0 n) ->
 (Zlength (map Vbyte (ls ++ [zero])) = Z.max 0 (Zlength ls + 1)) ->
(n = Zlength (map Vbyte ld ++ Zrepeat Vundef ((n - Zlength ld)))).
Proof.
  idtac "VST experiment 13".
  time list_solver.
Qed.

Lemma VST_experiment_14 {A} {_ : Inhabitant A} {B} {_ : Inhabitant A} {_ : Inhabitant B} (zero : A) (Vundef: B) (Vbyte : A -> B) (ld ls : list A) (n : Z):
Zlength ld + Zlength ls < n ->
(map Vbyte (ld ++ ls) ++
    upd_Znth 0 (Zrepeat Vundef (n - (Zlength ld + Zlength ls)))
      (Vbyte zero)) = (map Vbyte ((ld ++ ls) ++ [zero]) ++
        Zrepeat Vundef (n - (Zlength ld + Zlength ls + 1))).
Proof.
  idtac "VST experiment 14";
  time list_solver.
Qed.

(* Eind From VST_make_experiment *)

(* Begin from verif_revarray.v *)

Lemma flip_fact_1: forall A {d: Inhabitant A} (size : Z) (contents: list A) j,
  Zlength contents = size ->
  0 <= j ->
  size - j - 1 <= j <= size - j ->
  flip_ends j (size - j) contents = rev contents.
Proof.
  idtac "flip_fact_1";
  time list_solver.
Qed.

Lemma flip_fact_3:
 forall A {d: Inhabitant A} (al: list A) j size,
  size = Zlength al ->
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
 Zlength al = size ->
  j < size - j - 1 ->
   0 <= j ->
  Znth (size - j - 1) al =
  Znth (size - j - 1) (flip_ends j (size - j) al).
Proof.
  idtac "flip_fact_2".
  time list_solver.
Qed.

(* Eind from verif_revarray.v *)
  unfold Zrepeat;
  unfold not;
  intuition.

Ltac list_solver := preprocess; list_solve.
