# coq-list-solver

## How to build

This project can be build by executing the following:
```make .merlin
make```
  
## How to run

To run this project open the CoqIDE with the correct options, to open for example the benchmarks use:

```coqide cc_theories/benchmarks.v  -I cc_src -R cc_theories Mycc```

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

```Lemma foo {A} {_ : Inhabitant A} :
   [The lemma]```
