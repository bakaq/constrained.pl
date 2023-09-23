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
:- use_module(library(lambda)).
:- use_module(library(debug)).
:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).
:- use_module(library(format)).

:- attribute functor_spec/3, functor_spec_constraint/1.

functor_spec(Var, Functor, Arity) :-
    functor_spec(Var, Functor, Arity, _).

functor_spec(Var, Functor, Arity, Args) :-
    enforce_constraints(Var, Functor, Arity, Args),
    (
        (   var(Var), nonvar(Functor), nonvar(Args)
        ;   nonvar(Var)
        ) ->
        Var =.. [Functor|Args],
        length(Args, Arity)
    ;   (   get_atts(Var, +functor_spec(Functor0, Arity0, Args0)) ->
            Functor0 = Functor,
            Arity0 = Arity,
            Args0 = Args
        ;   put_atts(Var, +functor_spec(Functor, Arity, Args)),
            maplist(
                Var+\V^(
                    var(V) ->
                    (   get_atts(V, +functor_spec_constraint(Vars0)) ->
                        sort([Var|Vars0], Vars),
                        put_atts(V, +functor_spec_constraint(Vars))
                    ;   put_atts(V, +functor_spec_constraint([Var]))
                    )
                ;   true
                ),
                [Functor, Arity, Args]
            )
        )
    ).

enforce_constraints(Var, Functor, Arity, Args) :-
    catch(enforce_constraints_(Var, Functor, Arity, Args), _, false).

enforce_constraints_(Var, Functor, Arity, Args) :-
    (   nonvar(Functor) ->
        (   atom(Functor) ->
            true
        ;   Arity = 0
        )
    ;   true
    ),
    (   (Var == Functor; Var == Arity) ->
        Arity = 0
    ;   true
    ),
    (   Functor == Arity ->
        % Functor has to be a number then, and a number is not an atom,
        % so it has to have arity 0
        Functor = 0
    ;   true
    ),
    (   Functor == Arity ->
        Functor = 0
    ;   true
    ),
    (   (nonvar(Arity); nonvar(Args)) ->
        length(Args, Arity)
    ;   true
    ),
    (   nonvar(Functor), nonvar(Arity) ->
        functor(Var, Functor, Arity)
    ;   true
    ).

#=..(Term, [Functor|Args]) :-
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

#=..(Term, FunctorArgs, T) :-
    Term #=.. FunctorArgs0,
    =(FunctorArgs0, FunctorArgs, T).

functor_match_t(F1, F2, T) :-
    functor_spec(F1, Functor1, Arity1, Args1),
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
        Goals = []
    ;   get_atts(Var, +functor_spec_constraint(Vars)) ->
        maplist(
            \V^G^(
                G = (
                    var(V) ->
                    functor_spec:get_atts(V, +functor_spec(Functor, Arity, Args)),
                    functor_spec:enforce_constraints(V, Functor, Arity, Args)
                ;   true
                )
            ),
            Vars,
            Goals
        )
    ;   Goals = []
    ).

attribute_goals(Var) --> 
    {(  get_atts(Var, +functor_spec(Functor, Arity, ArgSpec)) ->
        put_atts(Var, -functor_spec(_, _, _)),
        Goals0 = [functor_spec:functor_spec(Var, Functor, Arity, ArgSpec)|Goals],
        phrase(attribute_goals(Var), Goals)
    ;   get_atts(Var, +functor_spec_constraint(_)) ->
        put_atts(Var, -functor_spec_constraint(_)),
        Goals0 = Goals,
        phrase(attribute_goals(Var), Goals)
    ;   Goals0 = []
    )},
    Goals0.
