/**/

:- use_module(library(format)).
:- use_module(library(clpz)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(debug)).

:- use_module(functor_spec).

test("functor_spec/3: usage as functor/3",(
    functor_spec(A, a, 1),
    assert_p(A, "a(A)"),

    functor_spec(a(_,_), Functor, Arity),
    assert_p([Functor, Arity], "[a,2]"),

    functor_spec(asdf(2,3,4), asdf, 3)
)).

test("functor_spec/3: general query",(
    functor_spec(A, B, C),
    assert_p([A, B, C], "[A,B,C]")
)).

test("functor_spec/3: specify one of the properties",(
    functor_spec(A, a, _),
    assert_p(A, "A"),

    functor_spec(B, _, 2),
    assert_p(B, "A")
)).

test("functor_spec/3: complete information later with functor_spec/3",(
    functor_spec(A, a, _),
    assert_p(A, "A"),

    functor_spec(A, _, 2),
    assert_p(A, "a(A,B)")
)).

test("functor_spec/3: complete information later unifying constraint",(
    functor_spec(A, a, B),
    assert_p(A, "A"),
    B = 1,
    assert_p(A, "a(A)"),

    functor_spec(C, D, 2),
    assert_p(C, "A"),
    D = a,
    assert_p(C, "a(A,B)")
)).

test("functor_spec/3: sharing constraints",(
    functor_spec(A, a, B),
    functor_spec(C, b, B),
    assert_p(A, "A"),
    assert_p(C, "A"),

    B = 1,
    assert_p(A, "a(A)"),
    assert_p(C, "b(A)"),

    functor_spec(D, E, 1),
    functor_spec(F, E, 2),
    assert_p(D, "A"),
    assert_p(F, "A"),

    E = a,
    assert_p(D, "a(A)"),
    assert_p(F, "a(A,B)")
)).

test("functor_spec/3: conflicting information later",(
    functor_spec(A, a, _),
    \+ functor_spec(A, b, _)
)).

test("functor_spec/3: unification with complementary specs",(
    functor_spec(A, a, _),
    functor_spec(B, _, 1),
    A = B,
    assert_p(A, "a(A)"),
    assert_p(B, "a(A)")
)).

test("functor_spec/3: unification with conflicting specs",(
    functor_spec(A, a, _),
    functor_spec(B, b, _),
    \+ A = B
)).


test("functor_spec/4: general query",(
    functor_spec(A, B, C, D),
    assert_p([A, B, C, D], "[A,B,C,D]")
)).

test("functor_spec/4: specify one of the properties",(
    functor_spec(A, a, _, _),
    assert_p(A, "A"),

    functor_spec(B, _, 2, _),
    assert_p(B, "A"),

    functor_spec(C, _, _, [2,1]),
    assert_p(C, "A")
)).

test("functor_spec/4: arity and args consistency",(
    functor_spec(_, _, 2, Aargs),
    assert_p(Aargs, "[A,B]"),

    functor_spec(_, _, Barity, [1,2]),
    assert_p(Barity, "2")
)).

test("functor_spec/4: instantiate arity",(
    functor_spec(a(1,2,3), _, A, _),
    assert_p(A, "3")
)).

test("functor_spec/4: complete information later with functor_spec/4",(
    functor_spec(A, a, _, _),
    assert_p(A, "A"),
    functor_spec(A, _, 2, _),
    assert_p(A, "a(A,B)"),

    functor_spec(B, a, _, _),
    assert_p(B, "A"),
    functor_spec(B, _, _, [1,2]),
    assert_p(B, "a(1,2)")
)).

test("functor_spec/4: complete information later unifying constraint",(
    functor_spec(A, a, B, _),
    assert_p(A, "A"),
    B = 1,
    assert_p(A, "a(A)"),

    functor_spec(C, D, 2, _),
    assert_p(C, "A"),
    D = a,
    assert_p(C, "a(A,B)"),

    functor_spec(E, a, _, F),
    assert_p(E, "A"),
    length(F, 2),
    assert_p(E, "a(A,B)")
)).

test("functor_spec/4: conflicting information later",(
    functor_spec(A, a, _, _),
    \+ functor_spec(A, b, _, _),

    functor_spec(B, _, 2, _),
    \+ functor_spec(B, _, 3, _),

    functor_spec(C, _, 2, _),
    \+ functor_spec(C, _, _, [1,2,3]),

    functor_spec(D, _, _, [_,_]),
    \+ functor_spec(D, _, _, [_,_,_]),

    functor_spec(E, _, _, [_,_]),
    \+ functor_spec(E, _, 3, _)
)).

test("functor_spec/4: unification with complementary specs",(
    functor_spec(A, a, _, _),
    functor_spec(B, _, 1, _),
    A = B,
    assert_p(A, "a(A)"),
    assert_p(B, "a(A)"),

    functor_spec(C, a, _, _),
    functor_spec(D, _, _, [1,2]),
    C = D,
    assert_p(C, "a(1,2)"),
    assert_p(D, "a(1,2)")
)).

test("functor_spec/4: unification with conflicting specs",(
    functor_spec(A, a, _, _),
    functor_spec(B, b, _, _),
    \+ A = B,

    functor_spec(C, _, 2, _),
    functor_spec(D, _, 3, _),
    \+ C = D,

    functor_spec(E, _, 2, _),
    functor_spec(F, _, _, [_,_,_]),
    \+ E = F,

    functor_spec(G, _, _, [_,_]),
    functor_spec(H, _, 3, _),
    \+ G = H
)).

test("(#=..)/2: use as (=..)/2",(
    A #=.. [a, 1, 2],
    assert_p(A, "a(1,2)"),

    a(1,2) #=.. [F|Args],
    assert_p([F, Args], "[a,[1,2]]"),

    a(1,2) #=.. [a, 1, 2]
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

assert_p(A, B) :-
    phrase(portray_clause_(A), Portrayed),
    phrase((B, ".\n"), Portrayed).


