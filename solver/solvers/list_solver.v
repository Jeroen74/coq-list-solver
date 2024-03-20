From CoqListSolver Require Import Loader.
From stdpp Require Export list.
From CoqListSolver Require Export definitions.
From CoqListSolver Require Export length_normal_form.
From CoqListSolver Require Export list_normal_form.

From Coq Require Export Program.Tactics.

Lemma nth_l_overflow_eq {A} {d : Inhabitant A} (i j : nat) (l l' : list A):
  i >= length l ->
  j >= length l' ->
  nth_l i l = nth_l j l'.
Proof.
  intros;
  unfold nth_l;
  by repeat rewrite nth_overflow by lia.
Qed.

Lemma nth_l_eq {A} {d : Inhabitant A} (i j : nat) (l l' : list A):
  i = j -> l = l' ->
  nth_l i l = nth_l j l'.
Proof. intros; by subst. Qed.

(* Ltac that help in the solver *)

(*==================================================================*)
(*|   Ltac length_lists implements the following inference rule:   |*)
(*|                                                                |*)
(*|            Δ,l_1 = l_2,length l_1 = length l_2 |- G            |*)
(*|           -----------------------------------------            |*)
(*|                     Δ,l_1 = l_2 |- G                           |*)
(*==================================================================*)

Ltac length_lists :=
  repeat match goal with
  | H : ?l1 = ?l2 |- _ =>
        assert (length l1 = length l2) as ?Hl;
        [(by rewrite H) || (by rewrite <- H)|]; revert H;
        length_normal_form;
        revert Hl
  end;
  intros.

(* Ltac take_drop_subst_n is used in take_drop_generalize *)
(*
Require Import ssreflect.

Ltac take_drop_subst_n n l :=
  let H := fresh "tempH" in
  let lt := fresh "lt" in
  let ld := fresh "ld" in
  let H' := fresh "H'" in
  pose (lt := take n l);
  pose (ld := drop n l);
  wlog suff H : /
    length lt = minimum n (length l) ∧
    length ld = length l - n ∧
    lt ++ ld = l;
  [|unfold lt, ld; repeat split; [apply take_length_minimum|apply drop_length|apply take_drop]];
  revert lt ld H;
  generalize (take n l) (drop n l);
  intros lt ld;
  cbn zeta;
  intros (?Hlt & ?Hld & ?H'); rewrite <- H' in *; clear H'.

Unset SsrRewrite.
*)

Lemma take_drop_segment {A} n (l : list A) (P : list A → list A → Prop) :
  (∀ lt ld,
    length lt = n `min` length l →
    length ld = length l - n →
    l = lt ++ ld →
    P lt ld) →
  P (take n l) (drop n l).
Proof.
  intros.
  apply H.
  apply take_length.
  apply drop_length.
  by rewrite take_drop.
Qed.

Ltac take_drop_subst_n n l :=
let H' := fresh "H'" in
let lt := fresh "lt" in
let ld := fresh "ld" in
generalize dependent l;
intros l;
pattern (take n l);
pattern (drop n l);
apply (take_drop_segment n l);
intros lt ld ?Hlt ?Hld H';
intros;
rewrite -> H' in *;
clear H'.

(*===================================================================================================================*)
(*|               Ltac take_drop_generalize implements the following two inferce rules:                             |*)
(*|                                                                                                                 |*)
(*|    Δ, (lt ld : list_α), length lt = n `min` length (lt ++ ld), length ld = length (lt ++ ld) - n |- φ(lt, ld)   |*)
(*|    ----------------------------------------------------------------------------------------------------------   |*)
(*|                                Δ, l : list_α |- φ(take n l, drop n l)                                           |*)
(*|                                                                                                                 |*)
(*|                                             and                                                                 |*)
(*|                                                                                                                 |*)
(*|  Δ, (lt ld : list_α), length lt = n `min` length (lt ++ ld), length ld = length (lt ++ ld) - n, φ(lt, ld) |- G  |*)
(*|  -------------------------------------------------------------------------------------------------------------  |*)
(*|                              Δ, l : list_α, φ(take n l, drop n l) |- G                                          |*)
(*===================================================================================================================*)

Ltac take_drop_generalize :=
  match goal with
    | |- context [ take ?n ?l ] => take_drop_subst_n n l
    | _ : context [ take ?n ?l ] |- _ => take_drop_subst_n n l
    | |- context [ drop ?n ?l ] => take_drop_subst_n n l
    | _ : context [ drop ?n ?l ] |- _ => take_drop_subst_n n l
  end.

(*====================================================================*)
(*|     Ltac zero_length_then_nil implements the inference rule:     |*)
(*|                                                                  |*)
(*|    Δ, l : list_α |- length l = 0     Δ, l : list_α, l = [] |- G  |*)
(*|    ------------------------------------------------------------  |*)
(*|                        Δ, l : list_α |- G                        |*)
(*===================================================================|*)

Ltac repeat_zero_length_then_nil_helper v n :=
  let H' := fresh "H'" in
  assert (length (repeat v n) = 0) as H' by (rewrite repeat_length; lia); 
  apply nil_length_inv in H'; rewrite H' in *; clear H'.

Ltac zero_length_then_nil :=
  repeat (
  let H' := fresh "H'" in
  match goal with
    | l : (list _) |- _ => 
      assert (length l = 0) as H' by lia; apply nil_length_inv in H'; subst
    | |- context [repeat ?v ?n] => 
      repeat_zero_length_then_nil_helper v n
    | _ : context [repeat ?v ?n] |- _ => 
      repeat_zero_length_then_nil_helper v n
  end).

Ltac lia_eq_take_l :=
  let H := fresh "H" in
  multimatch goal with
    | |- context [take ?i ?l] =>
          multimatch goal with
            | |- context [take ?j l] => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (take i l = take j l) as <- by (by rewrite H); clear H
                  end
          end
    | _ : context [take ?i ?l] |- _ =>
          multimatch goal with
            | |- context [take ?j l] => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (take i l = take j l) as <- by (by rewrite H); clear H
                  end
          end
    | |- context [take ?i ?l] =>
          multimatch goal with
            | _ : context [take ?j l] |- _ => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (take i l = take j l) as <- by (by rewrite H); clear H
                  end
          end
    | _ : context [take ?i ?l] |- _ =>
          multimatch goal with
            | _ : context [take ?j l] |- _ => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (take i l = take j l) as <- by (by rewrite H); clear H
                  end
          end
  end.

Ltac lia_eq_drop_l :=
  let H := fresh "H" in
  multimatch goal with
    | |- context [drop ?i ?l] =>
          multimatch goal with
            | |- context [drop ?j l] => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (drop i l = drop j l) as <- by (by rewrite H); clear H
                  end
          end
    | _ : context [drop ?i ?l] |- _ =>
          multimatch goal with
            | |- context [drop ?j l] => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (drop i l = drop j l) as <- by (by rewrite H); clear H
                  end
          end
    | |- context [drop ?i ?l] =>
          multimatch goal with
            | _ : context [drop ?j l] |- _ => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (drop i l = drop j l) as <- by (by rewrite H); clear H
                  end
          end
    | _ : context [drop ?i ?l] |- _ =>
          multimatch goal with
            | _ : context [drop ?j l] |- _ => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (drop i l = drop j l) as <- by (by rewrite H); clear H
                  end
          end
  end.

Ltac lia_eq_drop_take_l :=
  let H := fresh "H" in
  multimatch goal with
    | |- context [take ?i ?l] =>
          multimatch goal with
            | |- context [drop ?j l] => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (drop i l = drop j l) as <- by (by rewrite H); clear H
                  end
          end
    | _ : context [take ?i ?l] |- _ =>
          multimatch goal with
            | |- context [drop ?j l] => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (drop i l = drop j l) as <- by (by rewrite H); clear H
                  end
          end
    | |- context [take ?i ?l] =>
          multimatch goal with
            | _ : context [drop ?j l] |- _ => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (drop i l = drop j l) as <- by (by rewrite H); clear H
                  end
          end
    | _ : context [take ?i ?l] |- _ =>
          multimatch goal with
            | _ : context [drop ?j l] |- _ => assert (i = j) as H by lia;
                  lazymatch goal with
                    | H : (i = i) |- _ => fail
                    | H : _ |- _ => assert (drop i l = drop j l) as <- by (by rewrite H); clear H
                  end
          end
  end.

Ltac lia_eq_take_drop_l :=
  repeat lia_eq_take_l;
  repeat lia_eq_drop_take_l;
  repeat lia_eq_drop_l.

Lemma len_le_2_rev {A} (l : list A) :
  length l < 2 ->
  rev l = l.
Proof.
  intros.
  assert (length l = 0 \/ length l = 1) by lia.
  destruct H0; destruct l; [done|by simpl in H0|by simpl in H0; done|].
  destruct l; [done|by simpl in H0].
Qed.

Ltac len_le_2_rev_tac_helper l :=
  let H' := fresh "H'" in
  assert (length l < 2) as H' by (length_normal_form_goal; lia);
  apply len_le_2_rev in H'; rewrite H' in *; clear H'.

Ltac len_le_2_rev_tac :=
  match goal with
  | |- context [rev ?l] => len_le_2_rev_tac_helper l
  | _ : context [rev ?l] |- _ => len_le_2_rev_tac_helper l 
  end.



(* The Lemma split_list_hyp_length is used in Ltac app_break_up *)

Lemma split_list_hyp_length {A} (l1 l2 l3 l4 : list A):
  l1 ++ l2 = l3 ++ l4 -> length l1 = length l3 -> l1 = l3 /\ l2 = l4.
Proof.
  intros.
  assert (l1 = l3).
  - revert l1 l2 l3 l4 H H0.
    induction l1; intros l2 l3 l4 H H0; destruct l3; [done|simpl in H0;lia|simpl in H0;lia|].
    simpl in H. inversion H. f_equal. apply (IHl1 l2 _ l4); try done.
    simpl in H0. lia.
  - split; [done|].
    length_lists;
    assert (length l2 = length l4) by lia; clear Hl. revert l1 l2 l3 l4 H2 H1 H H0 Hl0.
    induction l1; intros l2 l3 l4 H2 H1 H H0 Hl0; destruct l3; [by simpl in *|simpl in *; lia|simpl in *; lia|].
    inversion H1. apply (IHl1 l2 l3 l4); try done; try lia.
    + subst. simpl in H. by inversion H.
    + length_lists; lia.
    + length_lists; lia.
Qed.

(*===================================================================================*)
(*|            Ltac app_break_up implements the following inference rule:           |*)
(*|                                                                                 |*)
(*|  nf(e1) =_assoc e11 ++ e12     Δ, nf(e1) = nf(e2) |- len_nf(e11) = len_nf(e22)  |*)
(*|  nf(e2) =_assoc e21 ++ e22     Δ, nf(e11) = nf(e21), nf(e12) = nf(e22) |- G     |*)
(*|  -----------------------------------------------------------------------------  |*)
(*|                             Δ, nf(e1) = nf(e2) |- G                             |*)
(*===================================================================================*)

Ltac apply_segmentation_lemma llh llt lrh lrt :=
  assert (length llh = length lrh) as ?H'; 
  [length_normal_form_goal; try done; lia|
  apply (split_list_hyp_length llh llt lrh lrt) in H' as [?H ?]];
  [|by list_normal_form]; list_normal_form; try done.

Ltac recursive_segmentation llh llt lrh lrt :=
  first [(apply_segmentation_lemma llh llt lrh lrt)|
  (match lrt with
    | ?lrh' ++ ?lrt' => recursive_segmentation llh llt (lrh ++ lrh') lrt'
  end) |
  (match llt with 
    | ?llh' ++ ?llt' => recursive_segmentation (llh ++ llh') llt' lrh lrt
  end)].

Ltac spec_break_up_hyp H :=
  match goal with
    | H : ?llh ++ ?llt = ?lrh ++ ?lrt |- _ =>
        recursive_segmentation llh llt lrh lrt; try done; clear H
  end; intuition.


Ltac try_break_up llh llt lrh lrt:=
  let H' := fresh "H" in 
  or_congruence_eq H' (llh ++ llt = lrh ++ lrt); 
  [spec_break_up_hyp H'|congruence].

Lemma cons_break_up_strong {A} (a b : A) (l1 l2 : list A):
  a :: l1 = b :: l2 -> a = b /\ l1 = l2.
Proof. intros H; by inversion H. Qed.

Ltac break_up_hyp :=
  repeat ((*(match goal with
    | H : ?a :: ?l1 = ?b :: ?l2 |- _ =>
      apply cons_break_up_strong in H; intuition
  end) ||*)
  (match goal with
    | H : ?llh ++ ?llt = ?lrh ++ ?lrt |- _ =>
        try_break_up llh llt lrh lrt; (*try done;*) clear H
  end)); intuition.

Definition eq_fold (p : Prop) := p.

Lemma eq_fold_rewrite (p : Prop) :
  eq_fold p <-> p.
Proof. by unfold eq_fold. Qed.

Ltac rev_hyp :=
  repeat (let Hrev := fresh "Hrev" in
  match goal with
    | H : ?l1 = ?l2 |- _ => assert (rev l1 = rev l2) as ?Hrev; [by rewrite H|];
          list_normal_form;
          apply eq_fold_rewrite in H;
          apply eq_fold_rewrite in Hrev
  end); unfold eq_fold in *.

(* The Lemma split_list_app is used in Ltac app_segment_goal *)

Lemma split_list_app {A} (l1 l2 l3 l4 : list A):
  l1 = l3 -> l2 = l4 -> l1 ++ l2 = l3 ++ l4.
Proof. intros; by subst. Qed.

Ltac app_segment_goal llh llt lrh lrt :=
  (apply (split_list_app llh llt lrh lrt); list_normal_form) + (*[congruence|list_normal_form]*)
  (match lrt with 
    | ?lrh' ++ ?lrt' => app_segment_goal llh llt (lrh ++ lrh') lrt'
  end) +
  (match llt with 
    | ?llh' ++ ?llt' => app_segment_goal (llh ++ llh') llt' lrh lrt
  end).

Lemma cons_break_up_strong_inv {A} (a b : A) (l1 l2 : list A):
  a = b -> l1 = l2 -> a :: l1 = b :: l2.
Proof. intros; by subst. Qed.

(*=================================================================*)
(*|  Ltac segment_goal implements the following inference rule:  |*)
(*|                                                               |*)
(*|           e1 =_assoc e11 ++ e12    Δ |- e11 = e12             |*)
(*|           e2 =_assoc e21 ++ e22    Δ |- e21 = e22             |*)
(*|           ---------------------------------------             |*)
(*|                       Δ |- e1 = e2                            |*)
(*=================================================================*)

Ltac segment_goal :=
  idtac +
(*   ((match goal with
    | |- ?a :: ?l1 = ?b :: ?l2 => apply (cons_break_up_strong_inv a b); [first [done|lia|fail]|] (* hier kunnen we tactics toepassen die op de elementen van de lijst werken *)
  end);segment_goal) +*)
  ((match goal with
    | |- ?llh ++ ?llt = ?lrh ++ ?lrt =>
        app_segment_goal llh llt lrh lrt
  end);segment_goal).

Ltac clear_dup :=
  match goal with
    | [ H : ?X |- _ ] =>
      match goal with
        | [ H' : ?Y |- _ ] =>
          match H with
            | H' => fail 2
            | _ => unify X Y ; (clear H' || clear H)
          end
      end
  end.

Ltac clear_refl :=
  match goal with
  | [ H : ?a = ?a |- _ ] =>
      clear H
  end.

Ltac clean_hyps :=
  repeat clear_refl;
  repeat clear_dup.

(* The solver *)

Ltac theorem_printer :=
  intros;
  idtac "Begin of a theorem solved by list_solver";
  show_hyps;
  idtac "-----------------------------";
  show_goal;
  idtac "End of theorem".

Ltac list_solver_unfold :=
  unfold flip_ends in *;
  list_normal_form;
  unfold update in *.

Ltac list_solver_preprocess_expand :=
  idtac.

Ltac list_solver_preprocess :=
  list_solver_preprocess_expand;
  unfold not;
  intros;
  subst;
  length_normal_form;
  list_normal_form;
  min_max_destruct;
  list_normal_form;
  list_solver_unfold;
  length_normal_form; try lia;
  list_normal_form.

Ltac list_solver_finalize :=
  lia_eq_take_drop_l;
(*  repeat (repeat take_0_nil_by_lia; repeat remove_take_ge_by_lia; repeat remove_drop_0_by_lia; repeat drop_ge_nil_by_lia; try take_drop_generalize; try minimum_destruct; list_normal_form);*)
  list_normal_form;
  repeat (try take_drop_generalize; try minimum_destruct; list_normal_form);
  length_normal_form;
  list_normal_form;
  length_lists;
  zero_length_then_nil; 
  clean_hyps;
  assert (∀A , ∀ l1 l2 l3 : list A, l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3) by (intro; apply app_assoc);
  repeat (
    break_up_hyp;
    clean_hyps;
    rev_hyp;
    subst;
    list_normal_form;
    clean_hyps
  );
  list_normal_form;
  repeat len_le_2_rev_tac;
  segment_goal.

Ltac list_solver :=
  list_solver_preprocess;
(*  list_solver_optimize;*)
  list_solver_finalize;
  (congruence ||
  (f_equal; (done|| lia)) || 
  (apply nth_l_overflow_eq; 
  (length_normal_form; lia)) || 
  ((apply nth_l_eq; [lia|list_solver])));
  fail.

