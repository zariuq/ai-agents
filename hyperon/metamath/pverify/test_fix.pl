:- use_module('/home/zar/claude/hyperon/metamath/pverify/mm_primitives.pl').

test1 :-
    phrase(mm_primitives:mm_token(T1), [36,99,32,65], R1),
    format('Test 1: T1=~w, R1=~w~n', [T1, R1]).

test2 :-
    read_file_to_codes('/tmp/test_mm.txt', [36,99,32,65], []),
    tokenize_mm_file('/tmp/test_mm.txt', Toks),
    format('Test 2: Tokens=~w~n', [Toks]).

test3 :-
    TestCodes = [36,99,32,65,32,0'$,0'(, 97,98,99, 0'$,0')],
    read_file_to_codes('/tmp/test_mm2.txt', TestCodes, []),
    tokenize_mm_file('/tmp/test_mm2.txt', Toks),
    format('Test 3 (with comment): Tokens=~w~n', [Toks]).

main :-
    test1,
    test2,
    test3,
    halt.

:- initialization(main).
