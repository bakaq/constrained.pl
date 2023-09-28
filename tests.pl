/**/

:- use_module(library(format)).
:- use_module(library(clpz)).
:- use_module(library(dcgs)).
:- use_module(library(lists)).
:- use_module(library(debug)).

:- use_module(constrained).

test("functor_c/3: usage as functor/3",(
    functor_c(A, a, 1),
    assert_p(A, "a(A)"),

    functor_c(a(_,_), Functor, Arity),
    assert_p([Functor, Arity], "[a,2]"),

    functor_c(asdf(2,3,4), asdf, 3)
)).

test("functor_c/3: general query",(
    functor_c(A, B, C),
    assert_p([A, B, C], "[A,B,C]")
)).

test("functor_c/3: specify one of the properties",(
    functor_c(A, a, _),
    assert_p(A, "A"),

    functor_c(B, _, 2),
    assert_p(B, "A")
)).

test("functor_c/3: complete information later with functor_c/3",(
    functor_c(A, a, _),
    assert_p(A, "A"),

    functor_c(A, _, 2),
    assert_p(A, "a(A,B)")
)).

test("functor_c/3: complete information later unifying constraint",(
    functor_c(A, a, B),
    assert_p(A, "A"),
    B = 1,
    assert_p(A, "a(A)"),

    functor_c(C, D, 2),
    assert_p(C, "A"),
    D = a,
    assert_p(C, "a(A,B)")
)).

test("functor_c/3: sharing constraints",(
    functor_c(A, a, B),
    functor_c(C, b, B),
    assert_p(A, "A"),
    assert_p(C, "A"),

    B = 1,
    assert_p(A, "a(A)"),
    assert_p(C, "b(A)"),

    functor_c(D, E, 1),
    functor_c(F, E, 2),
    assert_p(D, "A"),
    assert_p(F, "A"),

    E = a,
    assert_p(D, "a(A)"),
    assert_p(F, "a(A,B)")
)).

test("functor_c/3: conflicting information later",(
    functor_c(A, a, _),
    \+ functor_c(A, b, _)
)).

test("functor_c/3: unification with complementary specs",(
    functor_c(A, a, _),
    functor_c(B, _, 1),
    A = B,
    assert_p(A, "a(A)"),
    assert_p(B, "a(A)")
)).

test("functor_c/3: unification with conflicting specs",(
    functor_c(A, a, _),
    functor_c(B, b, _),
    \+ A = B
)).

test("functor_c/3: non-atom functor",(
    % https://github.com/bakaq/constrained.pl/issues/1
    functor_c(A, A, A),
    assert_p(A, "0"),

    % https://github.com/bakaq/constrained.pl/issues/2
    functor_c(B, C, D),
    B = 1,
    assert_p([B,C,D], "[1,1,0]"),

    % https://github.com/bakaq/constrained.pl/issues/3
    functor_c(E, 1, F),
    assert_p([E,F], "[1,0]"),

    % https://github.com/mthom/scryer-prolog/discussions/2021#discussioncomment-7043362
    functor_c(G, G, H),
    assert_p([G,H], "[A,0]"),

    % https://github.com/bakaq/constrained.pl/issues/4
    functor_c(I, J, I),
    assert_p([I,J], "[0,0]")
)).

/* https://github.com/bakaq/constrained.pl/issues/5#issuecomment-1740115280
test("functor_c/3: fail instead of emitting errors",(
    % https://github.com/bakaq/constrained.pl/issues/5
    catch(
        \+ (functor_c(_, A, B), A = a, B = 1*1),
        _,
        false
    ),

    catch(
        \+ (functor_c(_, C, D), D = 1*1, C = a),
        _,
        false
    )
)).
*/

test("functor_c/3: unify term with negative after",(
    % https://github.com/bakaq/constrained.pl/issues/13
    functor_c(T, F, N, A), T = -1,
    T == -1,
    F == -1,
    N == 0,
    A == []
)).

test("functor_c/4: general query",(
    functor_c(A, B, C, D),
    assert_p([A, B, C, D], "[A,B,C,D]")
)).

test("functor_c/4: specify one of the properties",(
    functor_c(A, a, _, _),
    assert_p(A, "A"),

    functor_c(B, _, 2, _),
    assert_p(B, "A"),

    functor_c(C, _, _, [2,1]),
    assert_p(C, "A")
)).

test("functor_c/4: arity and args consistency",(
    functor_c(_, _, 2, Aargs),
    assert_p(Aargs, "[A,B]"),

    functor_c(_, _, Barity, [1,2]),
    assert_p(Barity, "2")
)).

test("functor_c/4: instantiate arity",(
    functor_c(a(1,2,3), _, A, _),
    assert_p(A, "3")
)).

test("functor_c/4: complete information later with functor_c/4",(
    functor_c(A, a, _, _),
    assert_p(A, "A"),
    functor_c(A, _, 2, _),
    assert_p(A, "a(A,B)"),

    functor_c(B, a, _, _),
    assert_p(B, "A"),
    functor_c(B, _, _, [1,2]),
    assert_p(B, "a(1,2)")
)).

test("functor_c/4: complete information later unifying constraint",(
    functor_c(A, a, B, _),
    assert_p(A, "A"),
    B = 1,
    assert_p(A, "a(A)"),

    functor_c(C, D, 2, _),
    assert_p(C, "A"),
    D = a,
    assert_p(C, "a(A,B)"),

    functor_c(E, a, _, F),
    assert_p(E, "A"),
    length(F, 2),
    assert_p(E, "a(A,B)")
)).

test("functor_c/4: conflicting information later",(
    functor_c(A, a, _, _),
    \+ functor_c(A, b, _, _),

    functor_c(B, _, 2, _),
    \+ functor_c(B, _, 3, _),

    functor_c(C, _, 2, _),
    \+ functor_c(C, _, _, [1,2,3]),

    functor_c(D, _, _, [_,_]),
    \+ functor_c(D, _, _, [_,_,_]),

    functor_c(E, _, _, [_,_]),
    \+ functor_c(E, _, 3, _)
)).

test("functor_c/4: unification with complementary specs",(
    functor_c(A, a, _, _),
    functor_c(B, _, 1, _),
    A = B,
    assert_p(A, "a(A)"),
    assert_p(B, "a(A)"),

    functor_c(C, a, _, _),
    functor_c(D, _, _, [1,2]),
    C = D,
    assert_p(C, "a(1,2)"),
    assert_p(D, "a(1,2)")
)).

test("functor_c/4: unification with conflicting specs",(
    functor_c(A, a, _, _),
    functor_c(B, b, _, _),
    \+ A = B,

    functor_c(C, _, 2, _),
    functor_c(D, _, 3, _),
    \+ C = D,

    functor_c(E, _, 2, _),
    functor_c(F, _, _, [_,_,_]),
    \+ E = F,

    functor_c(G, _, _, [_,_]),
    functor_c(H, _, 3, _),
    \+ G = H
)).

test("(#=..)/2: use as (=..)/2",(
    A #=.. [a, 1, 2],
    assert_p(A, "a(1,2)"),

    a(1,2) #=.. [F|Args],
    assert_p([F, Args], "[a,[1,2]]"),

    a(1,2) #=.. [a, 1, 2]
)).

test("(#=..)/2: unify term with negative after",(
    A #=.. B, A = -1,
    A == -1,
    B == [-1]
)).

test("length_c/2: basic functionality",(
    length_c(Ls0, Len0),
    assert_p(Ls0, "A"),
    assert_p(Len0, "A"),
    Ls0 = [1,2,3],
    Len0 == 3,

    length_c(Ls1, Len1),
    assert_p(Ls1, "A"),
    assert_p(Len1, "A"),
    Len1 = 3,
    assert_p(Ls1, "[A,B,C]")
)).

test("length_c/2: multiple lenghts on same list, unify list",(
    length_c(Ls, Len0),
    length_c(Ls, Len1),
    assert_p(Ls, "A"),
    assert_p(Len0, "A"),
    assert_p(Len1, "A"),
    Ls = [1,2,3],
    Len0 == 3,
    Len1 == 3
)).

test("length_c/2: multiple lenghts on same list, unify length",(
    length_c(Ls, Len0),
    length_c(Ls, Len1),

    assert_p(Ls, "A"),
    assert_p(Len0, "A"),
    assert_p(Len1, "A"),

    Len0 = 3,
    Len1 == 3,
    assert_p(Ls, "[A,B,C]")
)).

test("length_c/2: multiple lists with same length, unify length",(
    length_c(Ls0, Len),
    length_c(Ls1, Len),

    assert_p(Ls0, "A"),
    assert_p(Ls1, "A"),
    assert_p(Len, "A"),

    Len = 3,
    assert_p(Ls0, "[A,B,C]"),
    assert_p(Ls1, "[A,B,C]")
)).

test("length_c/2: multiple lists with same length, unify list",(
    length_c(Ls0, Len),
    length_c(Ls1, Len),

    assert_p(Ls0, "A"),
    assert_p(Ls1, "A"),
    assert_p(Len, "A"),

    Ls0 = [1,2,3],
    Len == 3,
    assert_p(Ls1, "[A,B,C]")
)).

% https://github.com/bakaq/constrained.pl/issues/14
test("length_c/2: type inconsistency",(
    \+ length_c(A, A),

    length_c(Ls, Len),
    \+ Ls = Len
)).

% https://github.com/bakaq/constrained.pl/issues/14
test("length_c/2: partial lists",(
    Ls = [_|_],
    length_c(Ls, N),
    assert_p(Ls, "[A|B]"),
    assert_p(N, "A")
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


