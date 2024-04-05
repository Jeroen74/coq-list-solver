# coq-list-solver

## Software requirements

This project was built and tested with Coq version 8.16.1 and OCaml version 4.09.0.

## How to build

First create a new `opam switch` by executing

```
opam switch create coq-list-solver 4.09.0
```

Make sure opam can find the required packages

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```

To build the list-solver run
``` opam install coq-list-solver```


This project can be build by executing the following:
```
make .merlin
make
```
  
## How to run

To run this project open the CoqIDE with the correct options, to open for example the benchmarks use:

```coqide cc_theories/benchmarks.v  -I cc_src```

To be able to use te list solver, load the solver with 
```
From CoqListSolver Require Export list_solver.
Require Export stdpp.list.
```

## Accepted operators

Here we provide a list of operators that is accepted by our solver. To check the type, please use the Coq's `Check` command

```
length
++ / app
rev
take
drop
repeat
map
nth_l
update
flip_ends
```

## Provide a Inhabitant

For lemmas that use nth or update, make sure to provide an Inhabitant in the context, for example with lists of type `list A` do this as:

```
Lemma foo {A} {_ : Inhabitant A} :
   [The lemma]
```
