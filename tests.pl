/**/

:- use_module(library(format)).
:- use_module(library(clpz)).
:- use_module(library(debug)).

:- use_module(functor_spec).

test("functor_spec: usage as functor/3",(
    functor_spec(A, a, 1),
    phrase(portray_clause_(A), "a(A).\n"),

    functor_spec(a(_,_), Functor, Arity),
    phrase(portray_clause_([Functor, Arity]), "[a,2].\n"),

    functor_spec(asdf(2,3,4), asdf, 3)
)).

test("functor_spec: general query",(
    functor_spec(A, B, C),
    phrase(portray_clause_([A, B, C]), "[A,B,C].\n")
)).

test("functor_spec: specify one of the properties",(
    functor_spec(A, a, _),
    phrase(portray_clause_(A), "A.\n"),

    functor_spec(B, _, 2),
    phrase(portray_clause_(B), "A.\n")
)).

test("functor_spec: complete information later",(
    functor_spec(A, a, _),
    phrase(portray_clause_(A), "A.\n"),
    functor_spec(A, _, 2),
    phrase(portray_clause_(A), "a(A,B).\n")
)).

test("functor_spec: conflicting information later",(
    functor_spec(A, a, _),
    \+ functor_spec(A, b, _)
)).

test("functor_spec: unification with complementary specs",(
    functor_spec(A, a, _),
    functor_spec(B, _, 1),
    A = B,
    phrase(portray_clause_(A), "a(A).\n"),
    phrase(portray_clause_(B), "a(A).\n")
)).

test("functor_spec: unification with conflicting specs",(
    functor_spec(A, a, _),
    functor_spec(B, b, _),
    \+ A = B
)).

main :-
    findall(test(Name, Goal), test(Name, Goal), Tests),
    run_tests(Tests, Failed),
    show_failed(Failed),
    halt.

portray_failed_([]) --> [].
portray_failed_([F|Fs]) -->
    "\"", F, "\"",  "\n", portray_failed(Fs).

portray_failed([]) --> [].
portray_failed([F|Fs]) -->
    "\n", "Failed tests:", "\n", portray_failed_([F|Fs]).

show_failed(Failed) :-
    phrase(portray_failed(Failed), F),
    format("~s", [F]).

run_tests([], []).
run_tests([test(Name, Goal)|Tests], Failed) :-
    format("Running test \"~s\"~n", [Name]),
    (   call(Goal) ->
        Failed = Failed1
    ;   Failed = [Name|Failed1]
    ),
    run_tests(Tests, Failed1).

