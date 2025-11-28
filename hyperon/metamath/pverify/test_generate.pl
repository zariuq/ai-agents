% Test MeTTa generation
:- use_module('/home/zar/claude/hyperon/metamath/pverify/mm_primitives.pl').

test_generate :-
    format('~n=== Generating PeTTa MeTTa from demo0.mm ===~n'),
    generate_petta_verifier('/home/zar/claude/hyperon/metamath/mmverify/tests/demo0.mm',
                           '/home/zar/claude/hyperon/metamath/pverify/demo0_generated.metta'),
    format('Generated: demo0_generated.metta~n~n'),

    % Show first 30 lines
    format('First 30 lines:~n'),
    format('----------------------------------------~n'),
    open('/home/zar/claude/hyperon/metamath/pverify/demo0_generated.metta', read, In),
    show_lines(In, 30),
    close(In).

show_lines(_, 0) :- !.
show_lines(In, N) :-
    N > 0,
    (read_line_to_string(In, Line) ->
        format('~w~n', [Line]),
        N1 is N - 1,
        show_lines(In, N1)
    ;
        true
    ).

main :-
    test_generate,
    halt.

:- initialization(main).
