From CoqListSolver Require Export list_solver.
Require Export stdpp.list.


Definition sublist {A} {_ : Inhabitant A} (n m : nat) (l : list A) :=
  drop n (take m l).

Definition Length {A} {_ : Inhabitant A} (l : list A) :=
  length l.

Definition Update {A} {_ : Inhabitant A} (i : nat) (l : list A) (v : A) := 
  update i l v.

Definition Nth {A} {_ : Inhabitant A} (i : nat) (l : list A) :=
  nth_l i l.

Definition Flip_ends {A} {_ : Inhabitant A} (i j : nat) (l : list A) :=
  flip_ends i j l.

Definition Repeat {A} {_ : Inhabitant A} (v : A) (i : nat) :=
  repeat v i.

Ltac list_solver_preprocess_expand ::=
  unfold Length;
  unfold Update;
  unfold Nth;
  unfold Flip_ends;
  unfold Repeat;
  unfold sublist;
  simpl;
  unfold not;
  intuition.