/*
  SPDX-License-Identifier: Unlicense
*/

:- module(constrained, [
    op(700, xfx, (#=..)),
    functor_c/3,
    functor_c/4,
    (#=..)/2,
    length_c/2,
    same_length_c/2,
    functor_c_t/4,
    functor_c_t/5,
    (#=..)/3,
    functor_match_t/3
]).

:- use_module(library(atts)).
:- use_module(library(lists)).
:- use_module(library(reif)).
:- use_module(library(clpz)).
:- use_module(library(lambda)).
:- use_module(library(debug)).
:- use_module(library(dcgs)).
:- use_module(library(iso_ext)).
:- use_module(library(format)).

:- attribute functor_spec/3, functor_spec_constraint/1, length_of/1, lengths/1.

functor_c(Var, Functor, Arity) :-
    functor_c(Var, Functor, Arity, _).

functor_c(Var, Functor, Arity, Args) :-
    enforce_functor_constraints(Var, Functor, Arity, Args),
    (
        (   var(Var), nonvar(Functor), nonvar(Args)
        ;   nonvar(Var)
        ) ->
        Var =.. [Functor|Args],
        length(Args, Arity)
    ;   (   get_atts(Var, functor_spec(Functor0, Arity0, Args0)) ->
            Functor0 = Functor,
            Arity0 = Arity,
            Args0 = Args
        ;   put_atts(Var, functor_spec(Functor, Arity, Args)),
            maplist(
                Var+\V^(
                    var(V) ->
                    (   get_atts(V, functor_spec_constraint(Vars0)) ->
                        sort([Var|Vars0], Vars),
                        put_atts(V, functor_spec_constraint(Vars))
                    ;   put_atts(V, functor_spec_constraint([Var]))
                    )
                ;   true
                ),
                [Functor, Arity, Args]
            )
        )
    ).

enforce_functor_constraints(Var, Functor, Arity, Args) :-
    catch(
        catch(
            enforce_functor_constraints_(Var, Functor, Arity, Args),
            error(type_error(_,_),_),
            false
        ),
        error(domain_error(_,_),_),
        false
    ).

enforce_functor_constraints_(Var, Functor, Arity, Args) :-
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


install_length_attributes(Ls, Len) :-
    0 #=< #Len,
    (   get_atts(Ls, lengths(Lens0)) ->
        % Propagate clpz
        maplist(Len+\L^(Len #= L), Lens0),
        sort([Len|Lens0], Lens),
        put_atts(Ls, lengths(Lens))
    ;   put_atts(Ls, lengths([Len]))
    ),
    (   get_atts(Len, length_of(Lists0)) ->
        sort([Ls|Lists0], Lists),
        put_atts(Len, length_of(Lists))
    ;   put_atts(Len, length_of([Ls]))
    ).

length_c(Ls, Len) :-
    (   var(Ls), var(Len) ->
        Ls \== Len, % Can't be a list and a number at the same time
        install_length_attributes(Ls, Len)
    ;   nonvar(Ls), var(Len) ->
        % Check if it's an partial list
        '$skip_max_list'(Len0, _, Ls, LsTail),
        (   var(LsTail) ->
            #LenTail #= #Len - #Len0,
            install_length_attributes(LsTail, LenTail)
        ;   LsTail = [] ->
            length(Ls, Len)
        ;   false
        )
    ;   length(Ls, Len)
    ).

same_length_c(A, B) :-
    length_c(A, Len),
    length_c(B, Len).

lists_length(Ls, Len) :-
    maplist(Len+\L^(length(L, Len)), Ls).

list_lengths(L, Lens) :-
    maplist(L+\Len^(length(L, Len)), Lens).

#=..(Term, [Functor|Args]) :-
        functor_c(Term, Functor, _, Args).

functor_c_t(Var, Functor, Arity, T) :-
    functor_c(Var, Functor0, Arity0),
    if_(
        (Functor0 = Functor, Arity0 = Arity),
        T = true,
        T = false
    ).

functor_c_t(Var, Functor, Arity, Args, T) :-
    functor_c(Var, Functor0, Arity0, Args0),
    if_(
        (Functor0 = Functor, Arity0 = Arity, Args0 = Args),
        T = true,
        T = false
    ).

#=..(Term, FunctorArgs, T) :-
    Term #=.. FunctorArgs0,
    =(FunctorArgs0, FunctorArgs, T).

functor_match_t(F1, F2, T) :-
    functor_c(F1, Functor1, Arity1, Args1),
    functor_c(F2, Functor2, Arity2, Args2),
    if_(
        (Functor1 = Functor2, Arity1 = Arity2),
        (T = true, Args1 = Args2),
        (
            T = false
        )
    ).

verify_attributes(Var, Value, Goals) :-
    (   get_atts(Var, functor_spec(Functor, Arity, Args)) ->
        (   var(Value) ->
            (   get_atts(Value, functor_spec(Functor0, Arity0, Args0)) ->
                Functor0 = Functor,
                Arity0 = Arity,
                Args0 = Args
            ;   put_atts(Value, functor_spec(Functor, Arity, Args))
            )
        ;   Value =.. [Functor|Args],
            length(Args, Arity)
        ),
        Goals = []
    ;   get_atts(Var, functor_spec_constraint(Vars)) ->
        maplist(
            \V^G^(
                G = (
                    var(V) ->
                    constrained:get_atts(V, functor_spec(Functor, Arity, Args)),
                    constrained:enforce_functor_constraints(V, Functor, Arity, Args)
                ;   true
                )
            ),
            Vars,
            Goals
        )
    ;   get_atts(Var, lengths(Lens)) ->
        (   var(Value) ->
            Goals = []
        ;   Goals = [list_lengths(Var, Lens)]
        )
    ;   get_atts(Var, length_of(Lists)) ->
        (   var(Value) ->
            Goals = []
        ;   Goals = [lists_length(Lists, Var)]
        )
    ;   Goals = []
    ).

length_c_attribute_goals([], _) --> [].
length_c_attribute_goals([Len|Lens], Var) -->
    [constrained:length_c(Var, Len)],
    length_c_attribute_goals(Lens, Var).

attribute_goals(Var) --> 
    (   { get_atts(Var, functor_spec(Functor, Arity, ArgSpec)) } ->
        { put_atts(Var, -functor_spec(_, _, _)) },
        [constrained:functor_spec(Var, Functor, Arity, ArgSpec)],
        attribute_goals(Var)
    ;   { get_atts(Var, functor_spec_constraint(_)) } ->
        { put_atts(Var, -functor_spec_constraint(_)) },
        [],
        attribute_goals(Var)
    ;   { get_atts(Var, lengths(Lens)) } ->
        { put_atts(Var, -lengths(_)) },
        length_c_attribute_goals(Lens, Var),
        attribute_goals(Var)
    ;   { get_atts(Var, length_of(_)) } ->
        { put_atts(Var, -length_of(_)) },
        [],
        attribute_goals(Var)
    ;   []
    ).

