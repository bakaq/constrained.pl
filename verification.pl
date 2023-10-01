:- use_module(library(lists)).
:- use_module(library(lambda)).
:- use_module(library(debug)).
:- use_module(library(format)).
:- use_module(library(reif)).
:- use_module(library(clpz)).
:- use_module(library(pairs)).
:- use_module(library(charsio)).
:- use_module(library(si)).

:- use_module(constrained).

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
    catch(Term in -2..2, _, false),
    label([Term]).

float_(Term) :-
    T0 in -2..2,
    label([T0]),
    Term is T0 / 3.

atom_(Term) :-
    (   Term = a
    ;   Term = '.'
    ;   Term = '太陽'
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

consistent_equivalent(functor, functor_c, 3).
consistent_equivalent((=..), (#=..), 2).
consistent_equivalent(length, length_c, 2).
consistent_equivalent(atom, atom_c, 1).
consistent_equivalent(integer, integer_c, 1).
consistent_equivalent(float, float_c, 1).
consistent_equivalent(number, number_c, 1).
consistent_equivalent(atomic, atomic_c, 1).
consistent_equivalent(list_si, list_c, 1).

test_predicates(Predicates0) :-
    maplist(consistent_equivalent, Predicates0, PredicatesC0, Arities0),
    maplist(\P^Pc^A^(P-Pc-A)^true, Predicates0, PredicatesC0, Arities0, PPcA0),
    permutation(PPcA0, PPcA),
    maplist(\P^Pc^A^(P-Pc-A)^true, Predicates, PredicatesC, Arities, PPcA),
    maplist(length, Args, Arities),
    append(Args, Vars),
    sum_list(Arities, NVars),
    length(Terms, NVars),
    maplist(term_, Terms),
    maplist(\V^T^(V = T)^true, Vars, Terms, VarTerms),
    maplist(\P^A^F^(F =.. [P|A]), Predicates, Args, Goals0),
    append(VarTerms, Goals0, Goals1),
    reverse(Goals1, Goals),
    Goals = [G|Gs],
    foldl(\A^B^(A,B)^true, Gs, G, Goal),
    copy_term(Goal, GoalCopy),
    copy_term(Args, ArgsCopy),
    copy_term(Terms, TermsCopy),
    once(catch(call(Goal), _, false)),
    portray_clause(GoalCopy),
    test_predicates_c(PredicatesC, ArgsCopy, TermsCopy).

test_predicates_c(PredicatesC, Args, Terms) :-
    append(Args, Vars),
    maplist(\V^T^(V = T)^true, Vars, Terms, VarTerms),
    maplist(\P^A^F^(F =.. [P|A]), PredicatesC, Args, Goals0),
    append(VarTerms, Goals0, Goals1),
    permutation(Goals1, Goals),
    Goals = [G|Gs],
    foldl(\A^B^(A,B)^true, Gs, G, Goal),
    (   catch(call(Goal), _, false) ->
        true
    ;   format("Failed unexpectedly for goal ~q~n", [Goal]),
        get_single_char(_),
        false
    ).

    
