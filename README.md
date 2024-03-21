# coq-list-solver

This repository contains the spplementary material of the master thesis with the title "List Theorem Solving" by Jeroen Kool.

The following is contained in this repository:
  * The master thesis (see `Thesis.pdf`);
  * The solver for theorems about lists implemented in Coq (see directory `solver`);
  * The benchmarks that are used to compare the solver with existing work (see directory `solver/benchmarks`);
  * The implementation that is used to verify with the program AProVE that the rewrite system discussed in the thesis is always terminating (see directory `AProVE`).
  
## The abstract of the master thesis

In this master thesis, we present a solver for proving theorems about lists, formulated in the proof assistant Coq. The solver is a new Coq tactic that attempts to automatically prove these theorems. Theorems about lists may include operations such as length, concatenation, reverse, map, take, and drop. For this fragment of theory, little research has been done and, to our knowledge, it has only been (partially) investigated in “A Solver for Arrays with Concatenation” by Qinshi Wang and Andrew W Appel. Our Coq solver leverages on the identity property of the reverse operator (whereby applying reverse twice returns the original list) and implements a segmentation approach based on the length of the lists, utilizing the hypothesis with a congruence closure algorithm. We provide the solver's theoretical framework, practical implementation via new Coq tactics by using Coq's Ltac, and a new OCaml plugin, which is a modification of the existing congruence closure plugin. Evaluation against benchmarks demonstrates our solver's effectiveness, comparing favorably with existing methods, and highlighting its contributions to automated theorem proving in Coq. This work not only presents a significant advancement in list theorem solving but also lays the groundwork for future exploration in automated proof generation for list data structures.
