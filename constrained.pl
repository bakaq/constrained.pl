/*
  SPDX-License-Identifier: Unlicense
*/

:- module(constrained, [
    op(700, xfx, (#=..)),
    functor_c/3,
    functor_c/4,
    (#=..)/2,
    length_c/2,
    atom_c/1,
    integer_c/1,
    float_c/1,
    number_c/1,
    atomic_c/1,
    list_c/1,
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

:- attribute 
    functor_spec/3,
    functor_spec_constraint/1,
    length_of/1,
    lengths/1,
    type/1.

functor_c(Var, Functor, Arity) :-
    functor_c(Var, Functor, Arity, _).

functor_c(Var, Functor, Arity, Args) :-
    Arity in 0..sup,
    list_c(Args),
    length_c(Args, Arity),
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

enforce_functor_constraints_(Var, Functor, Arity, _) :-
    (   nonvar(Functor) ->
        (   atom(Functor) ->
            true
        ;   #Arity #= 0
        )
    ;   true
    ),
    (   (Var == Functor; Var == Arity) ->
        #Arity #= 0
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
    list_c(Ls),
    integer_c(Len),
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

type_c(Atom, atom) :-
    (   var(Atom) ->
        (   get_atts(Atom, type(Type)) ->
            (   Type = atom ->
                true
            ;   Type = atomic ->
                put_atts(Atom, type(atom))
            )
        ;   put_atts(Atom, type(atom))
        )
    ;   atom(Atom)
    ).

type_c(Int, integer) :-
    (   var(Int) ->
        (   get_atts(Int, type(Type)) ->
            (   Type = integer ->
                true
            ;   (Type = number; Type = atomic) ->
                put_atts(Int, type(integer))
            )
        ;   put_atts(Int, type(integer)),
            Int in inf..sup
        )
    ;   integer(Int)
    ).

type_c(Float, float) :-
    (   var(Float) ->
        (   get_atts(Float, type(Type)) ->
            (   Type = float ->
                true
            ;   (Type = number; Type = atomic) ->
                put_atts(Float, type(float))
            )
        ;   put_atts(Float, type(float))
        )
    ;   float(Float)
    ).

type_c(Number, number) :-
    (   var(Number) ->
        (   get_atts(Number, type(Type)) ->
            (   Type = number ->
                true
            ;   Type = atomic ->
                put_atts(Number, type(number))
            ;   Type = integer ->
                put_atts(Number, type(integer))
            ;   Type = float ->
                put_atts(Number, type(float))
            )
        ;   put_atts(Number, type(number))
        )
    ;   number(Number)
    ).

type_c(Atomic, atomic) :-
    (   var(Atomic) ->
        (   get_atts(Atomic, type(Type)) ->
            (   Type = atomic ->
                true
            ;   Type = atom ->
                put_atts(Atomic, type(atom))
            ;   Type = number ->
                put_atts(Atomic, type(number))
            ;   Type = integer ->
                put_atts(Atomic, type(integer))
            ;   Type = float ->
                put_atts(Atomic, type(float))
            ;   Type = list ->
                Atomic = []
            )
        ;   put_atts(Atomic, type(atomic))
        )
    ;   atomic(Atomic)
    ).

type_c(Ls, list) :-
    (   var(Ls) ->
        var_list_c(Ls)
    ;   '$skip_max_list'(_, _, Ls, LsTail),
        (   var(LsTail) ->
            var_list_c(LsTail)
        ;   LsTail = []
        )
    ).

var_list_c(Ls) :-
    (   get_atts(Ls, type(Type)) ->
        (   Type = list ->
            true
        ;   Type = atomic ->
            Ls = []
        )
    ;   put_atts(Ls, type(list))
    ).

atom_c(Atom) :- type_c(Atom, atom).
integer_c(Int) :- type_c(Int, integer).
float_c(Float) :- type_c(Float, float).
number_c(Number) :- type_c(Number, number).
atomic_c(Atomic) :- type_c(Atomic, atomic).
list_c(Ls) :- type_c(Ls, list).

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
    % TODO: Verify more than one attribute at a time
    (   get_atts(Var, functor_spec(Functor, Arity, Args)) ->
        (   var(Value) ->
            (   get_atts(Value, functor_spec(Functor0, Arity0, Args0)) ->
                Goals0 = [
                    Functor0 = Functor,
                    Arity0 = Arity,
                    Args0 = Args
                ]
            ;   put_atts(Value, functor_spec(Functor, Arity, Args))
            )
        ;   Goals0 = [(
                Value =.. [Functor|Args],
                length(Args, Arity)
            )]
        )
    ;   Goals0 = []
    ),
    (   get_atts(Var, functor_spec_constraint(Vars)) ->
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
            Goals1
        )
    ;   Goals1 = []
    ),
    (   get_atts(Var, lengths(Lens)) ->
        (   var(Value) ->
            Goals2 = []
        ;   Goals2 = [list_lengths(Var, Lens)]
        )
    ;   Goals2 = []
    ),
    (   get_atts(Var, length_of(Lists)) ->
        (   var(Value) ->
            Goals3 = []
        ;   Goals3 = [lists_length(Lists, Var)]
        )
    ;   Goals3 = []
    ),
    (   get_atts(Var, type(Type)) ->
        type_c(Value, Type),
        Goals4 = []
    ;   Goals4 = []
    ),
    append([Goals0, Goals1, Goals2, Goals3, Goals4], Goals).

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
    ;   { get_atts(Var, type(Type)) } ->
        { 
            put_atts(Var, -type(_)),
            (   Type = atom -> TypeGoals = [constrained:atom_c(Var)]
            ;   Type = integer -> TypeGoals = [constrained:integer_c(Var)]
            ;   Type = list -> TypeGoals = [constrained:list_c(Var)]
            ;   TypeGoals = []
            )
        },
        TypeGoals,
        attribute_goals(Var)
    ;   []
    ).

