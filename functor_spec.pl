/*
  SPDX-License-Identifier: Unlicense
*/

:- module(functor_spec, [
    op(700, xfx, (#=..)),
    functor_spec/3,
    functor_spec/4,
    (#=..)/2
]).

:- use_module(library(atts)).
:- use_module(library(lists)).
:- use_module(library(debug)).

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
        ) -> Var =.. [Functor|Args]
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

