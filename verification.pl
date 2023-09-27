:- use_module(library(lists)).
:- use_module(library(lambda)).
:- use_module(library(debug)).
:- use_module(library(format)).
:- use_module(library(reif)).
:- use_module(library(clpz)).

default_depth(1).

term_(Term) :-
    default_depth(Depth),
    term_(Term, Depth).

term_(Term, Depth) :-
    (   variable_(Term)
    ;   atomic_non_list_(Term)
    ;   compound_(Term, Depth)
    ).

variable_(Term) :- var(Term).
atomic_(Term) :-
    (   atomic_non_list_(Term)
    ;   Term = []
    ).

atomic_non_list_(Term) :-
    (   number_(Term)
    ;   atom_(Term)
    ).

number_(Term) :-
    (   integer_(Term)
    ;   float_(Term)
    ).

integer_(Term) :-
    Term in -5..5,
    label([Term]).

float_(Term) :-
    T0 in -5..5,
    label([T0]),
    Term is T0 / 3.

atom_(Term) :-
    (   Term = a
    ;   Term = abc
    ;   Term = 'Test'
    ).

compound_(Term) :-
    default_depth(Depth),
    compound_(Term, Depth).

compound_(Term, Depth) :-
    (   non_list_compound_(Term, Depth)
    ;   list_(Term, Depth)
    ).

non_list_compound_(Term, Depth) :-
    0 #=< #Depth,
    if_(
        #Depth = 0,
        atomic_(Term),
        (   atomic_(Functor),
            Arity in 1..3,
            label([Arity]),
            length(Args, Arity),
            #Depth1 = #Depth - 1,
            maplist(
                Depth1+\T^term(T, Depth1),
                Args
            ),
            Term =.. [Functor|Args]
        )
    ).

list_(Term) :-
    default_depth(Depth),
    list_(Term, Depth).

list_(Term, Depth) :-
    0 #=< #Depth,
    if_(
        #Depth #= 0,
        Term = [],
        (   Len in 1..3,
            label([Len]),
            length(Term, Len),
            #Depth1 #= #Depth - 1,
            maplist(Depth1+\T^(term_(T, Depth1)), Term)
        )
    ).
