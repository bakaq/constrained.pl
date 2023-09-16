/**/

:- module(functor_spec, [
    functor_spec/3
]).

:- use_module(library(atts)).

:- attribute functor_spec/2.

functor_spec(Var, Functor, Arity) :-
    (
        (   var(Var), nonvar(Functor), nonvar(Arity)
        ;   nonvar(Var)
        ) -> functor(Var, Functor, Arity)
    ;   (   get_atts(Var, +functor_spec(Functor, Arity)) ->
            (   (nonvar(Functor), nonvar(Arity)) ->
                functor(Var, Functor, Arity)
            ;   true
            )
        ;   put_atts(Var, +functor_spec(Functor, Arity))
        )
    ).

verify_attributes(Var, Value, Goals) :-
    (   get_atts(Var, +functor_spec(Functor, Arity)) ->
        (   var(Value) ->
            (   get_atts(Value, +functor_spec(Functor, Arity)) ->
                true
            ;   put_atts(Value, +functor_spec(Functor, Arity))
            )
        ;   functor(Value, Functor, Arity)
        ),
        (   (nonvar(Functor), nonvar(Arity)) ->
            Goals = [functor(Var, Functor, Arity)]
        ;   Goals = []
        )
    ;   Goals = []
    ).

attribute_goals(Var) -->
    { get_atts(Var, +functor_spec(Functor, Arity)) },
    [functor_spec:functor_spec(Var, Functor, Arity)],
    { put_atts(Var, -functor_spec(_, _)) }.
