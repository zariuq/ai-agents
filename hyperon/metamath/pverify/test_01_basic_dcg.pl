%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%% Test 1: Basic DCG Parsing
%%%%
%%%% Purpose: Verify DCG works in SWI-Prolog (PeTTa's backend)
%%%% Run: swipl -s test_01_basic_dcg.pl -g "run_all_tests" -t halt
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(readutil)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Simple DCG rules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Parse a word (sequence of alphabetic characters)
word([C|Cs]) --> [C], { code_type(C, alpha) }, word(Cs).
word([]) --> [].

% Parse whitespace
whites --> [C], { code_type(C, white) }, whites.
whites --> [].

% Parse a token (word followed by optional whitespace)
token(T) --> word(Cs), { Cs \= [], atom_codes(T, Cs) }, whites.

% Parse multiple tokens
tokens([T|Ts]) --> token(T), !, tokens(Ts).
tokens([]) --> [].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Test cases
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test_simple_word :-
    format('~n=== Test: Simple word parsing ===~n'),
    String = "hello",
    string_codes(String, Codes),
    phrase(word(W), Codes, Rest),
    atom_codes(Word, W),
    format('Input:  "~w"~n', [String]),
    format('Parsed: ~w~n', [Word]),
    format('Rest:   ~w~n', [Rest]),
    (Word == hello -> format('✅ PASS~n') ; format('❌ FAIL~n')).

test_word_with_rest :-
    format('~n=== Test: Word with remaining text ===~n'),
    String = "hello world",
    string_codes(String, Codes),
    phrase(word(W), Codes, Rest),
    atom_codes(Word, W),
    atom_codes(RestAtom, Rest),
    format('Input:  "~w"~n', [String]),
    format('Parsed: ~w~n', [Word]),
    format('Rest:   ~w~n', [RestAtom]),
    (Word == hello -> format('✅ PASS~n') ; format('❌ FAIL~n')).

test_multiple_tokens :-
    format('~n=== Test: Multiple tokens ===~n'),
    String = "hello world foo bar",
    string_codes(String, Codes),
    phrase(tokens(Ts), Codes),
    format('Input:  "~w"~n', [String]),
    format('Parsed: ~w~n', [Ts]),
    (Ts == [hello, world, foo, bar] -> format('✅ PASS~n') ; format('❌ FAIL~n')).

test_empty_input :-
    format('~n=== Test: Empty input ===~n'),
    String = "",
    string_codes(String, Codes),
    phrase(tokens(Ts), Codes),
    format('Input:  "~w"~n', [String]),
    format('Parsed: ~w~n', [Ts]),
    (Ts == [] -> format('✅ PASS~n') ; format('❌ FAIL~n')).

test_whitespace_only :-
    format('~n=== Test: Whitespace only ===~n'),
    String = "   \t\n  ",
    string_codes(String, Codes),
    phrase(tokens(Ts), Codes),
    format('Input:  (whitespace)~n'),
    format('Parsed: ~w~n', [Ts]),
    (Ts == [] -> format('✅ PASS~n') ; format('❌ FAIL~n')).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Metamath-style statement parsing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Parse a symbol (non-whitespace, non-dollar sequence)
mm_symbol(S) --> [C|Cs], { code_type(C, graph), C \= 36 }, mm_symbol_rest(Cs, [C|Cs], S).

mm_symbol_rest([C|Cs], Acc, S) --> [C], { code_type(C, graph), C \= 36 }, !, mm_symbol_rest(Cs, Acc, S).
mm_symbol_rest(_, Acc, S) --> { atom_codes(S, Acc) }.

% Parse dollar-keyword
dollar_keyword(K) --> "$", word(Cs), { atom_codes(K, Cs) }.

% Parse constant statement: $c symbols $.
mm_constant(c(Syms)) -->
    "$c", whites,
    mm_symbols(Syms),
    "$.", whites.

mm_symbols([S|Ss]) --> mm_symbol(S), !, whites, mm_symbols(Ss).
mm_symbols([]) --> [].

test_parse_constant :-
    format('~n=== Test: Parse Metamath $c statement ===~n'),
    String = "$c ( ) $.",
    string_codes(String, Codes),
    phrase(mm_constant(Result), Codes),
    format('Input:  "~w"~n', [String]),
    format('Parsed: ~w~n', [Result]),
    (Result = c(['(', ')']) -> format('✅ PASS~n') ; format('❌ FAIL~n')).

test_parse_constant_multi :-
    format('~n=== Test: Parse $c with multiple symbols ===~n'),
    String = "$c -> ( ) $.",
    string_codes(String, Codes),
    phrase(mm_constant(Result), Codes),
    format('Input:  "~w"~n', [String]),
    format('Parsed: ~w~n', [Result]),
    (Result = c(['->', '(', ')']) -> format('✅ PASS~n') ; format('❌ FAIL~n')).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Main test runner
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run_all_tests :-
    format('~n'),
    format('═══════════════════════════════════════════════════════════════~n'),
    format('  PeTTaVerify Test 1: Basic DCG Parsing~n'),
    format('═══════════════════════════════════════════════════════════════~n'),
    test_simple_word,
    test_word_with_rest,
    test_multiple_tokens,
    test_empty_input,
    test_whitespace_only,
    test_parse_constant,
    test_parse_constant_multi,
    format('~n'),
    format('═══════════════════════════════════════════════════════════════~n'),
    format('  All tests completed!~n'),
    format('═══════════════════════════════════════════════════════════════~n'),
    format('~n').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
