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
