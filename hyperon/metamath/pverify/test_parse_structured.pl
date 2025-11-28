% Test the new structured statement parser
:- use_module('/home/zar/claude/hyperon/metamath/pverify/mm_primitives.pl').

test_parse_demo0 :-
    format('~n=== Testing parse_mm_file on demo0.mm ===~n'),
    parse_mm_file('/home/zar/claude/hyperon/metamath/mmverify/tests/demo0.mm', Statements),
    length(Statements, N),
    format('Parsed ~w statements~n~n', [N]),

    % Show first 10 statements
    format('First 10 statements:~n'),
    show_first_n(Statements, 10),

    % Count statement types
    count_statement_types(Statements).

show_first_n([], _).
show_first_n(_, 0) :- !.
show_first_n([S|Ss], N) :-
    N > 0,
    format('  ~q~n', [S]),
    N1 is N - 1,
    show_first_n(Ss, N1).

count_statement_types(Statements) :-
    format('~nStatement counts:~n'),
    count_type(Statements, c, NC),
    count_type(Statements, v, NV),
    count_type(Statements, f, NF),
    count_type(Statements, e, NE),
    count_type(Statements, a, NA),
    count_type(Statements, p, NP),
    count_type(Statements, d, ND),
    count_frames(Statements, NOpen, NClose),
    format('  $c: ~w~n', [NC]),
    format('  $v: ~w~n', [NV]),
    format('  $f: ~w~n', [NF]),
    format('  $e: ~w~n', [NE]),
    format('  $a: ~w~n', [NA]),
    format('  $p: ~w~n', [NP]),
    format('  $d: ~w~n', [ND]),
    format('  ${: ~w~n', [NOpen]),
    format('  $}: ~w~n', [NClose]).

count_type([], _, 0).
count_type([Stmt|Rest], Type, Count) :-
    (functor(Stmt, Type, _) ->
        count_type(Rest, Type, Count1),
        Count is Count1 + 1
    ;
        count_type(Rest, Type, Count)
    ).

count_frames([], 0, 0).
count_frames([open_frame|Rest], Open, Close) :-
    !,
    count_frames(Rest, Open1, Close),
    Open is Open1 + 1.
count_frames([close_frame|Rest], Open, Close) :-
    !,
    count_frames(Rest, Open, Close1),
    Close is Close1 + 1.
count_frames([_|Rest], Open, Close) :-
    count_frames(Rest, Open, Close).

main :-
    test_parse_demo0,
    halt.

:- initialization(main).
