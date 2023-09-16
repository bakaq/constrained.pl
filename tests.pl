/**/

:- use_module(library(format)).
:- use_module(library(clpz)).
:- use_module(library(debug)).

:- use_module(functor_spec).

test("functor_spec/3: usage as functor/3",(
    functor_spec(A, a, 1),
    phrase(portray_clause_(A), "a(A).\n"),

    functor_spec(a(_,_), Functor, Arity),
    phrase(portray_clause_([Functor, Arity]), "[a,2].\n"),

    functor_spec(asdf(2,3,4), asdf, 3)
)).

test("functor_spec/3: general query",(
    functor_spec(A, B, C),
    phrase(portray_clause_([A, B, C]), "[A,B,C].\n")
)).

test("functor_spec/3: specify one of the properties",(
    functor_spec(A, a, _),
    phrase(portray_clause_(A), "A.\n"),

    functor_spec(B, _, 2),
    phrase(portray_clause_(B), "A.\n")
)).

test("functor_spec/3: complete information later",(
    functor_spec(A, a, _),
    phrase(portray_clause_(A), "A.\n"),
    functor_spec(A, _, 2),
    phrase(portray_clause_(A), "a(A,B).\n")
)).

test("functor_spec/3: conflicting information later",(
    functor_spec(A, a, _),
    \+ functor_spec(A, b, _)
)).

test("functor_spec/3: unification with complementary specs",(
    functor_spec(A, a, _),
    functor_spec(B, _, 1),
    A = B,
    phrase(portray_clause_(A), "a(A).\n"),
    phrase(portray_clause_(B), "a(A).\n")
)).

test("functor_spec/3: unification with conflicting specs",(
    functor_spec(A, a, _),
    functor_spec(B, b, _),
    \+ A = B
)).

test("functor_spec/4: general query",(
    functor_spec(A, B, C, D),
    phrase(portray_clause_([A, B, C, D]), "[A,B,C,D].\n")
)).

test("functor_spec/4: specify one of the properties",(
    functor_spec(A, a, _, _),
    phrase(portray_clause_(A), "A.\n"),

    functor_spec(B, _, 2, _),
    phrase(portray_clause_(B), "A.\n"),

    functor_spec(C, _, _, [2,1]),
    phrase(portray_clause_(C), "A.\n")
)).

test("functor_spec/4: arity and args consistency",(
    functor_spec(_, _, 2, Aargs),
    phrase(portray_clause_(Aargs), "[A,B].\n"),

    functor_spec(_, _, Barity, [1,2]),
    phrase(portray_clause_(Barity), "2.\n")
)).

test("functor_spec/4: complete information later",(
    functor_spec(A, a, _, _),
    phrase(portray_clause_(A), "A.\n"),
    functor_spec(A, _, 2, _),
    phrase(portray_clause_(A), "a(A,B).\n"),

    functor_spec(B, a, _, _),
    phrase(portray_clause_(B), "A.\n"),
    functor_spec(B, _, _, [1,2]),
    phrase(portray_clause_(B), "a(1,2).\n")
)).

test("functor_spec/4: conflicting information later",(
    functor_spec(A, a, _, _),
    \+ functor_spec(A, b, _, _),

    functor_spec(A, _, 2, _),
    \+ functor_spec(A, _, 3, _),

    functor_spec(A, _, 2, _),
    \+ functor_spec(A, _, _, [1,2,3]),

    functor_spec(A, _, _, [_,_]),
    \+ functor_spec(A, _, _, [_,_,_]),

    functor_spec(A, _, _, [_,_]),
    \+ functor_spec(A, _, 3, _)
)).

test("functor_spec/4: unification with complementary specs",(
    functor_spec(A, a, _, _),
    functor_spec(B, _, 1, _),
    A = B,
    phrase(portray_clause_(A), "a(A).\n"),
    phrase(portray_clause_(B), "a(A).\n"),

    functor_spec(C, a, _, _),
    functor_spec(D, _, _, [1,2]),
    C = D,
    phrase(portray_clause_(C), "a(1,2).\n"),
    phrase(portray_clause_(D), "a(1,2).\n")
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
    phrase(portray_clause_(A), "a(1,2).\n"),

    a(1,2) #=.. [F|Args],
    phrase(portray_clause_([F, Args]), "[a,[1,2]].\n"),

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

