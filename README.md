# constrained.pl

A Prolog library (primary for Scryer Prolog) that aims to generalize common
Prolog predicates using constaints so that they are more flexible and
declarative.

Currently offers `functor_c/3`, `#=../2` and `length_c/2`, which are constraint
versions of `functor/3`, `=../2` and `length/2` respectively. They work in all
directions, including the most general case where all arguments are variables, ensure consistency, and delay the instantiation of their arguments. Reified versions of these predicates are also provided for use with `library(reif)`.
