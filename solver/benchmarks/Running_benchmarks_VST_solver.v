 Require Export stdpp.tactics.
Require Export stdpp.list.
Require Export VST.zlist.list_solver.

Open Scope Z_scope.

Global Hint Rewrite @Zlength_rev : Zlength.
Global Hint Rewrite @Znth_rev  using Zlength_solve : Znth.
Definition Length {A} {_ : Inhabitant A} (l : list A) :=
  Zlength l.

Definition Update {A} {_ : Inhabitant A} (i : Z) (l : list A) (v : A) :=
  upd_Znth i l v.

Definition Nth {A} {_ : Inhabitant A} (i : Z) (l : list A) :=
  Znth i l.

Definition Flip_ends {A} {_ : Inhabitant A} lo hi (contents: list A) :=
  sublist 0 lo (rev contents)
  ++ sublist lo hi contents
  ++ sublist hi (Zlength contents) (rev contents).

Definition Repeat {A} {_ : Inhabitant A} (v : A) (i : Z) :=
  Zrepeat v i.

Ltac preprocess :=
  unfold Length;
  unfold Update;
  unfold Nth;
  unfold Flip_ends;
  unfold Repeat;
  unfold not;
  intuition.

Ltac list_solver := preprocess; list_solve.
