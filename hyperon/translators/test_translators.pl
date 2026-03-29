%% Test harness for HE ↔ PeTTa translators
%% Tests on hand-crafted examples covering all translation rules.
%%
%% Run: swipl -l test_translators.pl -g run_tests -g halt

:- use_module(he_to_petta, []).
:- use_module(petta_to_he, []).

he_translate_term(In, Out) :- he_to_petta:translate_term(In, Out).
he_translate_term_trusted(In, Out) :- he_to_petta:translate_term_trusted(In, Out).
he_translate_decl(In, Out) :- he_to_petta:translate_decl(In, Out).
he_translate_program(In, Out) :- he_to_petta:translate_program(In, Out).
pe_translate_term(In, Out) :- petta_to_he:translate_term(In, Out).
pe_translate_term_ext(In, Out) :- petta_to_he:translate_term_extended(In, Out).
pe_translate_term_trusted(In, Out) :- petta_to_he:translate_term_trusted(In, Out).
pe_translate_decl(In, Out) :- petta_to_he:translate_decl(In, Out).
pe_optimize_term(In, Out) :- petta_to_he:optimize_term(In, Out).

:- discontiguous test_he_to_petta/4.
:- discontiguous test_petta_to_he/4.
:- discontiguous run_one_pe/4.

%% ═══════════════════════════════════════════════════════════════
%% HE → PeTTa test cases
%% ═══════════════════════════════════════════════════════════════

test_he_to_petta(1, "chain → let",
    [chain, ['+', x, 1], y, ['*', y, y]],
    [let, y, ['+', x, 1], ['*', y, y]]).

test_he_to_petta(2, "nested chain → nested let",
    [chain, ['+', x, 1], y, [chain, ['*', y, 2], z, ['-', z, 1]]],
    [let, y, ['+', x, 1], [let, z, ['*', y, 2], ['-', z, 1]]]).

test_he_to_petta(3, "collapse-bind → collapse",
    ['collapse-bind', [superpose, [a, b, c]]],
    [collapse, [superpose, [a, b, c]]]).

test_he_to_petta(4, "superpose-bind → superpose",
    ['superpose-bind', [collapse, [foo]]],
    [superpose, [collapse, [foo]]]).

test_he_to_petta(5, "switch → case",
    [switch, x, [['1', one], ['2', two]]],
    [case, x, [['1', one], ['2', two]]]).

test_he_to_petta(6, "atom-subst → let",
    ['atom-subst', [foo], v, [bar, v]],
    [let, v, [foo], [bar, v]]).

test_he_to_petta(7, "nop → let $fresh X () (hygiene)",
    [nop, [println, hello]],
    capture_must_not_occur).

test_he_to_petta(8, "function/return → unwrap",
    [function, [return, 42]],
    42).

test_he_to_petta(9, "if passthrough (translate children)",
    [if, ['==', x, 0], zero, [chain, ['-', x, 1], n, [foo, n]]],
    [if, ['==', x, 0], zero, [let, n, ['-', x, 1], [foo, n]]]).

test_he_to_petta(10, "equation with chain body",
    ['=', [sq, x], [chain, ['+', x, 1], y, ['*', y, y]]],
    ['=', [sq, x], [let, y, ['+', x, 1], ['*', y, y]]]).

test_he_to_petta(11, "type declaration passthrough",
    [':', sq, ['->', 'Number', 'Number']],
    [':', sq, ['->', 'Number', 'Number']]).

test_he_to_petta(12, "bare fact passthrough",
    ['Inheritance', 'Abe', human],
    ['Inheritance', 'Abe', human]).

test_he_to_petta(13, "let passthrough (shared)",
    [let, x, ['+', 1, 2], ['*', x, x]],
    [let, x, ['+', 1, 2], ['*', x, x]]).

test_he_to_petta(14, "match passthrough (shared)",
    [match, '&self', ['Foo', '$x'], '$x'],
    [match, '&self', ['Foo', '$x'], '$x']).

test_he_to_petta(16, "add-atom passthrough (shared)",
    ['add-atom', '&self', ['Fact', a]],
    ['add-atom', '&self', ['Fact', a]]).

test_he_to_petta(17, "remove-atom passthrough (shared)",
    ['remove-atom', '&self', ['Fact', a]],
    ['remove-atom', '&self', ['Fact', a]]).

test_he_to_petta(18, "get-atoms passthrough (shared)",
    ['get-atoms', '&self'],
    ['get-atoms', '&self']).

test_he_to_petta(23, "explicit space handle passthrough (shared atomspace handle)",
    [match, '&bag', ['Fact', '$x'], '$x'],
    [match, '&bag', ['Fact', '$x'], '$x']).

test_he_to_petta(19, "new-space passthrough (extension surface)",
    ['new-space'],
    ['new-space']).

test_he_to_petta_trusted(1, "new-space → trusted PeTTa gensym call",
    ['new-space'],
    [call, [gensym, '&__tr_space_']]).

test_he_to_petta_trusted(2, "change-state! return value → (State val) wrapper via chain",
    [chain, ['change-state!', '&counter', 42], '$s', [use, '$s']],
    trusted_state_chain_shape('&counter', 42, '$s', [use, '$s'])).

test_he_to_petta(20, "new-state passthrough (shared surface)",
    ['new-state', 1],
    ['new-state', 1]).

test_he_to_petta(21, "get-state passthrough (shared surface)",
    ['get-state', '&state'],
    ['get-state', '&state']).

test_he_to_petta(22, "change-state! passthrough (shared surface)",
    ['change-state!', '&state', 5],
    ['change-state!', '&state', 5]).

test_he_to_petta(24, "unique → collapse + unique-atom + superpose",
    [unique, [let, '$x', [superpose, [1, 2, 1, 3, 2]], [pair, '$x', '$x']]],
    unique_shape([let, '$x', [superpose, [1, 2, 1, 3, 2]], [pair, '$x', '$x']])).

test_he_to_petta(15, "deduce-And → let* sequencing",
    ['And',
      ['deduce', ['Evaluation', ['philosopher', '$x']]],
      ['deduce', ['Evaluation', ['likes-to-wrestle', '$x']]]],
    ['let*',
      [['T', ['deduce', ['Evaluation', ['philosopher', '$x']]]],
       ['T', ['deduce', ['Evaluation', ['likes-to-wrestle', '$x']]]]],
      'T']).

test_he_program(1, "backchain kernel drops obsolete bool-And helper",
    [['=', ['deduce', ['And', '$a', '$b']],
          ['And', ['deduce', '$a'], ['deduce', '$b']]],
     ['=', ['And', 'T', 'T'], 'T'],
     ['=', ['ift', 'T', '$then'], '$then']],
    [['=', ['deduce', ['And', '$a', '$b']],
          ['let*', [['T', ['deduce', '$a']], ['T', ['deduce', '$b']]], 'T']],
     ['=', ['ift', 'T', '$then'], '$then']]).

test_he_program(2, "keep bool-And helper when other RHS And uses remain",
    [['=', ['deduce', ['And', '$a', '$b']],
          ['And', ['deduce', '$a'], ['deduce', '$b']]],
     ['=', ['And', 'T', 'T'], 'T'],
     ['=', ['explain', '$x'], ['And', '$x', '$x']]],
    [['=', ['deduce', ['And', '$a', '$b']],
          ['let*', [['T', ['deduce', '$a']], ['T', ['deduce', '$b']]], 'T']],
     ['=', ['And', 'T', 'T'], 'T'],
     ['=', ['explain', '$x'], ['And', '$x', '$x']]]).

%% ═══════════════════════════════════════════════════════════════
%% PeTTa → HE test cases
%% ═══════════════════════════════════════════════════════════════

%% PeTTa→HE tests use structural checking (fresh var names are counter-dependent).
%% We check: (a) correct shape, (b) binder has $__tr_ prefix, (c) source args preserved.

test_petta_to_he(1, "progn (2-arg) → nested let (fresh vars)",
    [progn, [println, hello], result],
    capture_must_not_occur).

test_petta_to_he(2, "progn (3-arg) → nested let (fresh vars)",
    [progn, a, b, c],
    capture_must_not_occur).

test_petta_to_he(3, "progn (0-arg) → unit",
    [progn],
    '()').

test_petta_to_he(4, "progn (1-arg) → translated term",
    [progn, ['@<', a, b]],
    ['<s', a, b]).

test_petta_to_he(5, "progn (4-arg) → nested lets (fresh vars)",
    [progn, a, b, c, d],
    capture_must_not_occur).

test_petta_to_he(6, "prog1 → let + let (fresh vars)",
    [prog1, first, [println, side]],
    capture_must_not_occur).

test_petta_to_he(7, "prog1 (0-arg) → unit",
    [prog1],
    '()').

test_petta_to_he(8, "prog1 (1-arg) → translated term",
    [prog1, ['@>', a, b]],
    [not, ['<s', a, b]]).

test_petta_to_he(9, "prog1 (3-arg) → let + nested let (fresh vars)",
    [prog1, first, second, third],
    capture_must_not_occur).

%% HYGIENE REGRESSION: these broke the OLD translator (hardcoded $_ / $__r)
%% Source contains the same variable names the old translator generated,
%% causing variable capture. The fix uses fresh $__tr_* names.

test_petta_to_he(100, "REGRESSION: prog1 with $__r in source (was captured)",
    [prog1, foo, '$__r'],
    capture_must_not_occur).
%% Old output: [let,$__r,foo,[let,$_,$__r,$__r]] ← $__r captured!
%% Fixed: $__tr_result_N is fresh, doesn't collide with source $__r

test_petta_to_he(101, "REGRESSION: progn with $_ in source (was captured)",
    [progn, foo, '$_'],
    capture_must_not_occur).
%% Old output: [let,$_,foo,$_] ← $_ captured!
%% Fixed: $__tr_discard_N is fresh, doesn't collide with source $_

test_petta_to_he(10, "@< → <s",
    ['@<', a, b],
    ['<s', a, b]).

test_petta_to_he(11, "@> → not(<s)",
    ['@>', a, b],
    [not, ['<s', a, b]]).

test_petta_to_he(12, "if passthrough",
    [if, true, yes, no],
    [if, true, yes, no]).

test_petta_to_he(15, "add-atom passthrough (shared)",
    ['add-atom', '&self', ['Fact', a]],
    ['add-atom', '&self', ['Fact', a]]).

test_petta_to_he(16, "remove-atom passthrough (shared)",
    ['remove-atom', '&self', ['Fact', a]],
    ['remove-atom', '&self', ['Fact', a]]).

test_petta_to_he(17, "match passthrough (shared)",
    [match, '&self', ['Fact', '$x'], '$x'],
    [match, '&self', ['Fact', '$x'], '$x']).

test_petta_to_he(18, "get-atoms passthrough (shared)",
    ['get-atoms', '&self'],
    ['get-atoms', '&self']).

test_petta_to_he(23, "explicit space handle passthrough (shared atomspace handle)",
    ['add-atom', '&bag', ['Fact', a]],
    ['add-atom', '&bag', ['Fact', a]]).

test_petta_to_he_trusted(1, "trusted gensym call → new-space",
    [call, [gensym, '&__tr_space_']],
    ['new-space']).

test_petta_to_he(19, "new-space passthrough (extension surface)",
    ['new-space'],
    ['new-space']).

test_petta_to_he(20, "new-state passthrough (shared surface)",
    ['new-state', 1],
    ['new-state', 1]).

test_petta_to_he(21, "get-state passthrough (shared surface)",
    ['get-state', '&state'],
    ['get-state', '&state']).

test_petta_to_he(22, "change-state! passthrough (shared surface)",
    ['change-state!', '&state', 5],
    ['change-state!', '&state', 5]).

test_petta_to_he(24, "unique-atom(collapse ...) → collapse(unique ...)",
    ['unique-atom', [collapse,
      [let, '$x', [superpose, [1, 2, 1, 3, 2]], [pair, '$x', '$x']]]],
    [collapse, [unique, [let, '$x', [superpose, [1, 2, 1, 3, 2]], [pair, '$x', '$x']]]]).

test_petta_to_he(13, "equation with progn body (fresh vars)",
    ['=', [foo, x], [progn, [bar, x], [baz, x]]],
    capture_must_not_occur).

test_petta_to_he(14, "foldall → let(collapse) + foldl-atom",
    [foldall, merge, [twohop-item], 0],
    foldall_shape(merge, [twohop-item], 0)).

%% ═══════════════════════════════════════════════════════════════
%% PeTTa → HE extended mode tests
%% ═══════════════════════════════════════════════════════════════

test_petta_to_he_ext(1, "foldall (extended) → let(collect) + foldl-atom",
    [foldall, merge, [twohop-item], 0],
    foldall_shape_ext(merge, [twohop-item], 0)).

%% ═══════════════════════════════════════════════════════════════
%% PeTTa → HE optimization tests
%% ═══════════════════════════════════════════════════════════════

test_petta_to_he_opt(1, "discard let → chain when body ignores binder",
    [let, '$__tr_discard_1', [println, hello], result],
    [chain, [println, hello], '$__tr_discard_1', result]).

test_petta_to_he_opt(2, "discard let → nop on unit tail",
    [let, '$__tr_discard_1', [println, hello], '()'],
    [nop, [println, hello]]).

test_petta_to_he_opt(3, "result let → direct expression",
    [let, '$__tr_result_1', [foo, bar], '$__tr_result_1'],
    [foo, bar]).

test_petta_to_he_opt(4, "keep foldall let(collapse ...) intact",
    [let, '$__tr_collapsed_1', [collapse, [twohop-item]],
      ['foldl-atom', '$__tr_collapsed_1', 0, '$__tr_acc_2', '$__tr_item_3',
        [eval, [merge, '$__tr_acc_2', '$__tr_item_3']]]],
    [let, '$__tr_collapsed_1', [collapse, [twohop-item]],
      ['foldl-atom', '$__tr_collapsed_1', 0, '$__tr_acc_2', '$__tr_item_3',
        [eval, [merge, '$__tr_acc_2', '$__tr_item_3']]]]).

%% ═══════════════════════════════════════════════════════════════
%% Normalization tests: HE → PeTTa → HE normal form
%% ═══════════════════════════════════════════════════════════════

test_roundtrip(1, "chain normalizes to let",
    [chain, ['+', x, 1], y, ['*', y, y]],
    [let, y, ['+', x, 1], ['*', y, y]]).

test_roundtrip(2, "nested chain normalizes to nested lets",
    [chain, a, x, [chain, b, y, [c, x, y]]],
    [let, x, a, [let, y, b, [c, x, y]]]).

test_roundtrip(3, "if with chain normalizes in branch",
    [if, cond, [chain, a, x, x], fallback],
    [if, cond, [let, x, a, x], fallback]).

%% ═══════════════════════════════════════════════════════════════
%% Test runner
%% ═══════════════════════════════════════════════════════════════

run_tests :-
    format("~n=== HE → PeTTa Tests ===~n"),
    forall(test_he_to_petta(N, Name, Input, Expected),
        run_one_he(N, Name, Input, Expected)),
    format("~n=== HE → PeTTa Trusted Tests ===~n"),
    forall(test_he_to_petta_trusted(N, Name, Input, Expected),
        run_one_he_trusted(N, Name, Input, Expected)),
    format("~n=== HE → PeTTa Program Tests ===~n"),
    forall(test_he_program(N, Name, Input, Expected),
        run_one_he_program(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE Tests ===~n"),
    forall(test_petta_to_he(N, Name, Input, Expected),
        run_one_pe(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE Trusted Tests ===~n"),
    forall(test_petta_to_he_trusted(N, Name, Input, Expected),
        run_one_pe_trusted(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE Extended Mode Tests ===~n"),
    forall(test_petta_to_he_ext(N, Name, Input, Expected),
        run_one_pe_ext(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE Optimization Tests ===~n"),
    forall(test_petta_to_he_opt(N, Name, Input, Expected),
        run_one_pe_opt(N, Name, Input, Expected)),
    format("~n=== Normalization Tests (HE → PeTTa → HE normal form) ===~n"),
    forall(test_roundtrip(N, Name, Input, Expected),
        run_one_rt(N, Name, Input, Expected)).

%% Special handler for HE capture tests
run_one_he(N, Name, Input, capture_must_not_occur) :- !,
    (   he_translate_term(Input, Result)
    ->  (   Result = [let, Binder | _],
            atom_string(Binder, BS),
            sub_string(BS, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w (fresh binder: ~w)~n", [N, Name, Binder])
        ;   format("  ✗ ~w: ~w (CAPTURE! got: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_he(N, Name, Input, unique_shape(ArgExpected)) :- !,
    (   he_translate_term(Input, Result)
    ->  (   Result = [let, ListVar, [collapse, ArgExpected],
                      [let, UniqueVar, ['unique-atom', ListVar],
                       [superpose, UniqueVar]]],
            atom_string(ListVar, ListS),
            atom_string(UniqueVar, UniqueS),
            sub_string(ListS, 0, _, _, "$__tr_"),
            sub_string(UniqueS, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w (fresh binders: ~w, ~w)~n",
                    [N, Name, ListVar, UniqueVar])
        ;   format("  ✗ ~w: ~w (bad unique lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_he(N, Name, Input, Expected) :-
    (   test_he_to_petta(N, _, Input, _),
        (   Input = ['=', _, _]
        ->  he_to_petta:translate_decl(Input, Result)
        ;   he_to_petta:translate_term(Input, Result)
        ),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n", [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_he_trusted(N, Name, Input, trusted_state_chain_shape(Ref, Val, Var, Body)) :- !,
    (   test_he_to_petta_trusted(N, _, Input, _),
        he_to_petta:translate_term_trusted(Input, Result),
        (   Result = [let, Fresh, ['change-state!', Ref, Val],
                      [let, Var, ['State', Val], Body]],
            atom_string(Fresh, FreshS),
            sub_string(FreshS, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got:      ~w~n",
                    [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_he_trusted(N, Name, Input, Expected) :-
    (   test_he_to_petta_trusted(N, _, Input, _),
        (   Input = ['=', _, _]
        ->  he_to_petta:translate_decl_trusted(Input, Result)
        ;   he_to_petta:translate_term_trusted(Input, Result)
        ),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n",
                    [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_he_program(N, Name, Input, Expected) :-
    (   test_he_program(N, _, Input, _),
        he_translate_program(Input, Result),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n",
                    [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

%% Special handler for capture regression tests
%% Checks that generated binder names have $__tr_ prefix (fresh, no capture)
run_one_pe(N, Name, Input, capture_must_not_occur) :- !,
    (   (Input = ['=', _, _] -> pe_translate_decl(Input, Result)
        ; pe_translate_term(Input, Result))
    ->  term_string(Result, RS),
        (   sub_string(RS, _, _, _, "$__tr_")
        ->  % Find the first fresh binder for display
            (   Result = [let, B | _] -> true
            ;   Result = ['=', _, [let, B | _]] -> true
            ;   B = '(see output)'
            ),
            format("  ✓ ~w: ~w (fresh binder: ~w)~n", [N, Name, B])
        ;   format("  ✗ ~w: ~w (NO fresh var! got: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, foldall_shape(Agg, Goal, Init)) :- !,
    (   pe_translate_term(Input, Result)
    ->  (   Result = [let, ListVar, ['collapse', Goal],
                      ['foldl-atom', ListVar, Init, AccVar, ItemVar,
                       [eval, [Agg, AccVar, ItemVar]]]],
            atom_string(ListVar, ListS),
            atom_string(AccVar, AccS),
            atom_string(ItemVar, ItemS),
            sub_string(ListS, 0, _, _, "$__tr_"),
            sub_string(AccS, 0, _, _, "$__tr_"),
            sub_string(ItemS, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w (fresh binders: ~w, ~w)~n",
                    [N, Name, AccVar, ItemVar])
        ;   format("  ✗ ~w: ~w (bad foldall lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_ext(N, Name, Input, foldall_shape_ext(Agg, Goal, Init)) :- !,
    (   pe_translate_term_ext(Input, Result)
    ->  (   Result = [let, ListVar, [collect, Goal],
                      ['foldl-atom', ListVar, Init, AccVar, ItemVar,
                       [eval, [Agg, AccVar, ItemVar]]]],
            atom_string(ListVar, ListS),
            atom_string(AccVar, AccS),
            atom_string(ItemVar, ItemS),
            sub_string(ListS, 0, _, _, "$__tr_"),
            sub_string(AccS, 0, _, _, "$__tr_"),
            sub_string(ItemS, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w (fresh binders: ~w, ~w)~n",
                    [N, Name, AccVar, ItemVar])
        ;   format("  ✗ ~w: ~w (bad extended foldall lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, Expected) :-
    (   test_petta_to_he(N, _, Input, _),
        (   Input = ['=', _, _]
        ->  petta_to_he:translate_decl(Input, Result)
        ;   petta_to_he:translate_term(Input, Result)
        ),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n", [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_pe_trusted(N, Name, Input, Expected) :-
    (   test_petta_to_he_trusted(N, _, Input, _),
        (   Input = ['=', _, _]
        ->  petta_to_he:translate_decl_trusted(Input, Result)
        ;   petta_to_he:translate_term_trusted(Input, Result)
        ),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n",
                    [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_pe_opt(N, Name, Input, Expected) :-
    (   test_petta_to_he_opt(N, _, Input, _),
        pe_optimize_term(Input, Result),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n",
                    [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_rt(N, Name, Input, Expected) :-
    (   he_to_petta:translate_term(Input, Mid),
        petta_to_he:translate_term(Mid, Back),
        (   Back == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Original:    ~w~n    Expected:    ~w~n    → PeTTa:     ~w~n    → HE (back): ~w~n",
                    [N, Name, Input, Expected, Mid, Back])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).
