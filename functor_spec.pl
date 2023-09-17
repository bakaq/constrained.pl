/*
  SPDX-License-Identifier: Unlicense
*/

:- module(functor_spec, [
    op(700, xfx, (#=..)),
    functor_spec/3,
    functor_spec/4,
    (#=..)/2,
    functor_spec_t/4,
    functor_spec_t/5,
    (#=..)/3,
    functor_match_t/3
]).

:- use_module(library(atts)).
:- use_module(library(lists)).
:- use_module(library(reif)).
:- use_module(library(debug)).
:- use_module(library(format)).

:- attribute functor_spec/3.

functor_spec(Var, Functor, Arity) :-
    (
        (   var(Var), nonvar(Functor), nonvar(Arity)
        ;   nonvar(Var)
        )
        -> functor(Var, Functor, Arity)
    ;   (   get_atts(Var, +functor_spec(Functor0, Arity0, _)) ->
            Functor0 = Functor,
            Arity0 = Arity,
            (   (nonvar(Functor), nonvar(Arity)) ->
                functor(Var, Functor, Arity)
            ;   true
            )
        ;   (   nonvar(Arity) ->
                length(Args, Arity)
            ;   true
            ),
            put_atts(Var, +functor_spec(Functor, Arity, Args))
        )
    ).

functor_spec(Var, Functor, Arity, Args) :-
    (   (   nonvar(Arity)
        ;   nonvar(Args)
        ) ->
        length(Args, Arity)
    ;   true
    ),
    (
        (   var(Var), nonvar(Functor), nonvar(Args)
        ;   nonvar(Var)
        ) ->
        Var =.. [Functor|Args],
        length(Args, Arity)
    ;   (   get_atts(Var, +functor_spec(Functor0, Arity0, Args0)) ->
            Functor0 = Functor,
            Arity0 = Arity,
            Args0 = Args,
            (   (nonvar(Functor), nonvar(Args)) ->
                Var =.. [Functor|Args]
            ;   true
            )
        ;   put_atts(Var, +functor_spec(Functor, Arity, Args))
        )
    ).

(#=..)(Term, [Functor|Args]) :-
        functor_spec(Term, Functor, _, Args).

functor_spec_t(Var, Functor, Arity, T) :-
    functor_spec(Var, Functor0, Arity0),
    if_(
        (Functor0 = Functor, Arity0 = Arity),
        T = true,
        T = false
    ).

functor_spec_t(Var, Functor, Arity, Args, T) :-
    functor_spec(Var, Functor0, Arity0, Args0),
    if_(
        (Functor0 = Functor, Arity0 = Arity, Args0 = Args),
        T = true,
        T = false
    ).

(#=..)(Term, FunctorArgs, T) :-
    Term #=.. FunctorArgs0,
    =(FunctorArgs0, FunctorArgs, T).

functor_match_t(F1, F2, T) :-
    functor_spec(F1, Functor1, Arity1, Args1),
    portray_clause(Arity1),
    functor_spec(F2, Functor2, Arity2, Args2),
    if_(
        (Functor1 = Functor2, Arity1 = Arity2),
        (T = true, Args1 = Args2),
        (
            T = false
        )
    ).

verify_attributes(Var, Value, Goals) :-
    (   get_atts(Var, +functor_spec(Functor, Arity, Args)) ->

        (   var(Value) ->
            (   get_atts(Value, +functor_spec(Functor0, Arity0, Args0)) ->
                Functor0 = Functor,
                Arity0 = Arity,
                Args0 = Args
            ;   put_atts(Value, +functor_spec(Functor, Arity, Args))
            )
        ;   Value =.. [Functor|Args],
            length(Args, Arity)
        ),
        (   (nonvar(Functor), nonvar(Args)) ->
            Goals = [(Var =.. [Functor|Args])]
        ;   Goals = []
        )
    ).

attribute_goals(Var) -->
    { get_atts(Var, +functor_spec(Functor, Arity, ArgSpec)) },
    [functor_spec:functor_spec(Var, Functor, Arity, ArgSpec)],
    { put_atts(Var, -functor_spec(_, _, _)) }.

