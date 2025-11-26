% mm_bridge.pl - Bridge layer that converts Prolog structures to MeTTa Cons lists
% Based on Gemini's recommendation
:- module(mm_bridge, [parse_to_metta/2]).
:- use_module(mm_primitives).

%% Main entry: Parse file, then DEEP CONVERT to MeTTa Cons structures
parse_to_metta(Filename, MettaStructure) :-
    parse_mm_file(Filename, PrologStatements),
    prolog_to_metta(PrologStatements, MettaStructure).

%% Convert Lists to Cons(H, T) or Empty (using capitalized atoms, not quoted!)
%% This way MeTTa will see them as proper constructors, not Prolog compounds
prolog_to_metta([], 'Empty') :- !.
prolog_to_metta([H|T], 'Cons'(MH, MT)) :-
    !,
    prolog_to_metta(H, MH),
    prolog_to_metta(T, MT).

%% Convert Compound terms (recurse into their arguments)
prolog_to_metta(c(L), c(ML)) :-
    !,
    prolog_to_metta(L, ML).

prolog_to_metta(v(L), v(ML)) :-
    !,
    prolog_to_metta(L, ML).

prolog_to_metta(d(L), d(ML)) :-
    !,
    prolog_to_metta(L, ML).

prolog_to_metta(f(L,T,V), f(L, T, V)) :-
    !. % Atoms inside are fine as-is

prolog_to_metta(e(L,T,M), e(L, T, MM)) :-
    !,
    prolog_to_metta(M, MM).

prolog_to_metta(a(L,T,M), a(L, T, MM)) :-
    !,
    prolog_to_metta(M, MM).

prolog_to_metta(p(L,T,M,P), p(L, T, MM, MP)) :-
    !,
    prolog_to_metta(M, MM),
    prolog_to_metta(P, MP).

prolog_to_metta(open_frame, open_frame) :- !.
prolog_to_metta(close_frame, close_frame) :- !.

%% Atoms/Numbers pass through unchanged
prolog_to_metta(X, X).
