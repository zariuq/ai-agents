% test_prolog_bridge.pl - Test cases for PeTTa's Prolog bridge
:- module(test_prolog_bridge, [
    return_atom/1,
    return_number/1,
    return_string/1,
    return_empty_list/1,
    return_atom_list/1,
    return_number_list/1,
    return_nested_list/1,
    return_compound/1,
    return_compound_with_list/1,
    return_cons_term/1,
    return_explicit_cons/1
]).

%% Test 1: Simple atom
return_atom(hello).

%% Test 2: Number
return_number(42).

%% Test 3: String (if different from atom)
return_string("hello").

%% Test 4: Empty list
return_empty_list([]).

%% Test 5: List of atoms
return_atom_list([a, b, c]).

%% Test 6: List of numbers
return_number_list([1, 2, 3]).

%% Test 7: Nested list
return_nested_list([[a, b], [c, d]]).

%% Test 8: Simple compound term
return_compound(foo(bar, baz)).

%% Test 9: Compound with list inside
return_compound_with_list(foo([a, b, c])).

%% Test 10: Try using Prolog's list notation [H|T]
return_cons_term([H|T]) :-
    H = first,
    T = [second, third].

%% Test 11: Explicit 'Cons' functor (Gemini's approach)
return_explicit_cons('Cons'(a, 'Cons'(b, 'Cons'(c, 'Empty')))).
