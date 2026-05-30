%% Test harness for HE ↔ PeTTa translators
%% Tests on hand-crafted examples covering all translation rules.
%%
%% Run: swipl -l test_translators.pl -g run_tests -g halt

:- use_module(he_to_petta, []).
:- use_module(petta_to_he, []).
:- use_module(he_petta_relational, []).

he_translate_term(In, Out) :- he_to_petta:translate_term(In, Out).
he_translate_term_trusted(In, Out) :- he_to_petta:translate_term_trusted(In, Out).
he_translate_decl(In, Out) :- he_to_petta:translate_decl(In, Out).
he_translate_program(In, Out) :- he_to_petta:translate_program(In, Out).
pe_translate_term(In, Out) :- petta_to_he:translate_term(In, Out).
pe_translate_term_hyperpose(In, Out) :- petta_to_he:translate_term_hyperpose(In, Out).
pe_translate_term_ffi_tokens(In, Out) :- petta_to_he:translate_term_ffi_tokens(In, Out).
pe_translate_term_petta_he(In, Out) :- petta_to_he:translate_term_petta_he(In, Out).
pe_translate_term_petta_he_hyperpose(In, Out) :- petta_to_he:translate_term_petta_he_hyperpose(In, Out).
pe_translate_term_ext(In, Out) :- petta_to_he:translate_term_extended(In, Out).
pe_translate_term_ext_hyperpose(In, Out) :- petta_to_he:translate_term_extended_hyperpose(In, Out).
pe_translate_term_trusted(In, Out) :- petta_to_he:translate_term_trusted(In, Out).
pe_translate_decl(In, Out) :- petta_to_he:translate_decl(In, Out).
pe_translate_decl_hyperpose(In, Out) :- petta_to_he:translate_decl_hyperpose(In, Out).
pe_translate_decl_petta_he(In, Out) :- petta_to_he:translate_decl_petta_he(In, Out).
pe_translate_decl_petta_he_hyperpose(In, Out) :- petta_to_he:translate_decl_petta_he_hyperpose(In, Out).
pe_translate_decl_ext_hyperpose(In, Out) :- petta_to_he:translate_decl_extended_hyperpose(In, Out).
pe_translate_program(In, Out) :- petta_to_he:translate_program(In, Out).
pe_translate_program_ffi_tokens(In, Out) :- petta_to_he:translate_program_ffi_tokens(In, Out).
pe_optimize_term(In, Out) :- petta_to_he:optimize_term(In, Out).
rel_pe_translate_term(In, Out) :- he_petta_relational:petta_to_he(In, Out, 0, _).
rel_pe_append_suffix_head_extension(PrefixElems, Actual, TailVar, ApplyArg, Out) :-
    he_petta_relational:petta_append_suffix_head_extension(PrefixElems, Actual, TailVar, ApplyArg, Out, 0, _).
rel_pe_append_suffix_let_extension(PrefixElems, Observed, TailVar, RawBody, Out) :-
    he_petta_relational:petta_append_suffix_let_extension(PrefixElems, Observed, TailVar, RawBody, Out, 0, _).

:- discontiguous test_he_to_petta/4.
:- discontiguous test_petta_to_he/4.
:- discontiguous test_petta_to_he_program/4.
:- discontiguous test_petta_to_he_ffi_tokens/4.
:- discontiguous test_petta_to_he_petta_he/4.
:- discontiguous test_petta_to_he_petta_he_hyperpose/4.
:- discontiguous test_rel_petta_to_he/4.
:- discontiguous run_one_pe/4.
:- discontiguous run_one_pe_program/4.
:- discontiguous run_one_pe_ffi_tokens/4.

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

test_he_to_petta(4_1, "singleton-visible-witness → once",
    ['singleton-visible-witness', ['=', x, 42]],
    [once, ['=', x, 42]]).

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

test_he_to_petta(20, "new-state passthrough (HE native state spelling)",
    ['new-state', 1],
    ['new-state', 1]).

test_he_to_petta(21, "get-state passthrough (HE native state spelling)",
    ['get-state', '&state'],
    ['get-state', '&state']).

test_he_to_petta(22, "change-state! passthrough (HE native state spelling)",
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
    [if, 'True', yes, no]).

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

test_petta_to_he(20, "standalone new-state stays PeTTa data, not HE State handle",
    ['new-state', 1],
    ['quoted-syntax', [quote, ['new-state', 1]]]).

test_petta_to_he(20_1, "bind! name (new-state value) → PeTTa named-state helper",
    ['bind!', state, ['new-state', 1]],
    ['__tr-petta-state-set!', state, 1]).

test_petta_to_he(21, "get-state → PeTTa named-state helper",
    ['get-state', '&state'],
    ['__tr-petta-state-get', '&state']).

test_petta_to_he(22, "change-state! → PeTTa named-state helper",
    ['change-state!', '&state', 5],
    ['__tr-petta-state-set!', '&state', 5]).

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

test_petta_to_he(25, "3-arg foldl-atom → binder form (symbol combiner)",
    ['foldl-atom', [collapse, [twohop-item]], 0, merge],
    foldl_atom_short_shape([collapse, [twohop-item]], 0, merge)).

test_petta_to_he(26, "3-arg foldl-atom → binder form (expression combiner)",
    ['foldl-atom', [collapse, [twohop-item]], 0, ['λ', merge]],
    foldl_atom_short_shape([collapse, [twohop-item]], 0, ['λ', merge])).

test_petta_to_he(27, "raw reduce → unquote(quote ...)",
    [reduce, [fib, 5]],
    [unquote, [quote, [fib, 5]]]).

test_petta_to_he(28, "collapse(reduce $term) → collapse(unquote $term) for quoted-code variables",
    [collapse, [reduce, '$term']],
    [collapse, [unquote, '$term']]).

test_petta_to_he(29, "length(collapse ...) → bind + size-atom",
    [length, [collapse, '$term']],
    length_collapse_shape('$term')).

test_petta_to_he(30, "test scalar → source test form before program rewrite",
    [test, ['+', 1, 2], 3],
    [test, ['+', 1, 2], 3]).

test_petta_to_he(30_1, "pure quote lowers to native HE quote",
    [quote, ['fib', 5]],
    [quote, ['fib', 5]]).

test_petta_to_he(30_2, "eval lowers to unquote(quote ...)",
    [eval, ['fib', 5]],
    [unquote, [quote, ['fib', 5]]]).

test_petta_to_he(30_3, "call lowers to unquote(quote ...)",
    [call, ['fib', 5]],
    [unquote, [quote, ['fib', 5]]]).

test_petta_to_he(31, "test length(collapse ...) → quoted HE helper call",
    [test, [length, [collapse, [match, '&self', ['edge', '$x', '$y'], '$x']]], 2],
    test_length_collapse_shape([match, '&self', ['edge', '$x', '$y'], '$x'], 2)).

test_petta_to_he(31_1, "partial builtin value lowers to petta-lambda helper",
    ['+', 1],
    partial_builtin_lambda_shape('+', 1)).

test_petta_to_he(31_2, "assertion-only msort lowers to bag-equality helper",
    [test, [msort, [collapse, [match, '&self', [foo, '$x'], '$x']]], [1, 1, 2]],
    ['petta-test-bag-equal', [match, '&self', [foo, '$x'], '$x'], [1, 1, 2]]).

test_petta_to_he(31_3, "callable source-variable application lowers through petta-apply2",
    ['$f', 43, 44],
    ['petta-apply2', '$f', 43, 44]).

test_petta_to_he_program(1, "program-level direct test uses petta-test-equal helper",
    [['=', [probe], [test, ['+', 1, 2], 3]]],
    program_uses_builtin_test_helper).

test_petta_to_he_program(1_0_1, "program-level nondet test uses petta-test-results helper",
    [['=', [probe], [test, [if, '$x', yes, no], [yes, no]]]],
    program_uses_collapse_test_helper).

test_petta_to_he_program(1_0_2, "program-level mixed tests route per call",
    [['=', [probe_direct], [test, ['+', 1, 2], 3]],
     ['=', [probe_results], [test, [if, '$x', yes, no], [yes, no]]]],
    program_uses_mixed_test_helpers).

test_petta_to_he_program(1_0_3, "=alpha with free vars stays on direct test helper",
    [['=', [probe_alpha], [test, ['=alpha', ['Father', '$X'], ['Father', '$Y']], 'True']]],
    program_routes_alpha_test_direct).

test_petta_to_he_program(1_0_4, "locally bound chain vars stay on direct test helper",
    [['=', [probe_chain], [test, [chain, ['+', 2, 4], '$n', ['*', 3, '$n']], 18]]],
    program_routes_chain_test_direct).

test_petta_to_he_program(1_0_5, "program-level assertion-only msort uses bag test helper",
    [['=', [probe_bag], [test, [msort, [collapse, [match, '&self', [foo, '$x'], '$x']]], [1, 1, 2]]]],
    program_uses_bag_test_helper).

test_petta_to_he_program(1_1, "program-level pure quote uses native HE quote",
    [['=', [probe], [quote, ['+', 1, 2]]]],
    program_uses_native_quote).

test_petta_to_he_program(1_2, "program-level PeTTa named-state helpers are prepended",
    [['=', [probe],
      [progn,
       ['bind!', state, ['new-state', rest]],
       ['change-state!', state, active],
       ['get-state', state]]]],
    program_uses_petta_state_helpers).

test_petta_to_he_program(1_3, "native quote does not need a helper despite source quoted-syntax symbol",
    [['=', ['quoted-syntax', '$x'], [user_quote, '$x']],
     ['=', [probe], [quote, ['+', 1, 2]]]],
    program_native_quote_ignores_source_quoted_syntax).

test_petta_to_he_program(1_4, "state helpers avoid source helper-like symbols",
    [['=', ['__tr-petta-state-clear!', '$x'], [user_clear, '$x']],
     ['=', ['__tr-petta-state-set!', '$x', '$y'], [user_set, '$x', '$y']],
     ['=', ['__tr-petta-state-get', '$x'], [user_get, '$x']],
     ['=', ['__tr-petta-state-cell', '$x', '$y'], [user_cell, '$x', '$y']],
     ['=', [probe],
      [progn,
       ['bind!', state, ['new-state', rest]],
       ['change-state!', state, active],
       ['get-state', state]]]],
    program_state_helpers_avoid_source_symbols).

test_petta_to_he_program(1_5, "program-level append helper is prepended",
    [['=', [probe], [append, [1], [2, 3]]]],
    program_uses_append_helper).

test_petta_to_he_program(1_5_1, "program-level second-from-pair helper is prepended",
    [['=', [probe], ['second-from-pair', [a, b]]]],
    program_uses_second_from_pair_helper).

test_petta_to_he_program(1_5_2, "program-level user-defined second-from-pair stays user-defined",
    [['=', ['second-from-pair', '$pair'], '$pair'],
     ['=', [probe], ['second-from-pair', [a, b]]]],
    program_uses_user_defined_second_from_pair).

test_petta_to_he_program(1_5_3, "program-level builtin partial becomes generated first-order helper",
    [['=', [probe], ['+', 1]]],
    program_rewrites_partial_builtin_helper).

test_petta_to_he_program(1_5_4, "program-level zero-arity function returning callable is applied curried",
    [['=', [mp], ['+']],
     ['=', [probe], [mp, 1, 1]]],
    program_curried_callable_result).

test_petta_to_he_program(1_5_4_1, "program-level partial composition value lowers to direct nested helper composition",
    [['=', ['..', '$f1', '$f2', '$arg'], ['$f1', ['$f2', '$arg']]],
     ['=', [plus1times2], ['..', ['*', 2], ['+', 1]]]],
    program_rewrites_partial_composition_helper).

test_petta_to_he_program(1_5_5, "canonical map-flat pair lowers to map-atom",
    [['=', ['map-flat', '$f', '()'], '()'],
     ['=', ['map-flat', '$f', [cons, '$x', '$xs']],
      [cons, ['$f', '$x'], ['map-flat', '$f', '$xs']]]],
    program_canonicalizes_map_flat).

test_petta_to_he_program(1_5_6, "canonical fold-nested pair lowers to foldl-atom + metatype check",
    [['=', ['fold-nested', '$f', '$init', '()'], '$init'],
     ['=', ['fold-nested', '$f', '$init', [cons, '$x', '$xs']],
      [if, ['is-expr', '$x'],
       ['fold-nested', '$f', ['fold-nested', '$f', '$init', '$x'], '$xs'],
       ['fold-nested', '$f', ['$f', '$init', '$x'], '$xs']]]],
    program_canonicalizes_fold_nested).

test_petta_to_he_program(1_5_7, "two-argument composition helper keeps direct multiarg target call",
    [['=', ['.:', '$f1', '$f2', '$arg1', '$arg2'],
      ['$f1', ['$f2', '$arg1', '$arg2']]]],
    program_preserves_direct_binary_composition).

test_petta_to_he_program(1_5_8, "strict Roman intersection alias lowers to intersection-atom",
    [['=', ['/==\\', '$a', '$b'], ['/?\\', '==', '$a', '$b']]],
    program_canonicalizes_roman_eqeq_intersection).

test_petta_to_he_program(1_5_9, "strict Roman subtraction alias lowers to subtraction-atom",
    [['=', ['\\==', '$a', '$b'], ['\\?', '==', '$a', '$b']]],
    program_canonicalizes_roman_eqeq_subtraction).

test_petta_to_he_program(1_5_10, "strict Roman union alias lowers to subtraction plus union-atom",
    [['=', ['\\==/', '$a', '$b'], ['\\?/', '==', '$a', '$b']]],
    program_canonicalizes_roman_eqeq_union).

test_petta_to_he_program(1_5_11, "nontrivial function heads normalize into fresh args plus let guard",
    [['=', [in, '$x', '$L'], [let, 'True', ['is-member', '$x', '$L'], '$x']],
     ['=', [myplus, [in, '$X', [1, 2, 3]], [in, '$Y', [2, 3]]],
      [in, ['+', '$X', '$Y'], [3, 4, 5]]]],
    program_normalizes_function_head_patterns).

test_petta_to_he_program(1_5_11_1, "source-defined generator head only freshens the nontrivial argument",
    [['=', [animal, '$X'], [only, [[living, '$X'], [being, '$X']], '$X']],
     ['=', [tagged_cat, [animal, '$X'], '$tag'], [pair, '$X', '$tag']]],
    program_selectively_freshens_function_head_args).

test_petta_to_he_program(1_5_11_2, "duplicate source head variables become explicit unify guard",
    [['=', [same, '$x', '$x'], ok]],
    program_normalizes_duplicate_function_head_vars).

test_petta_to_he_program(1_5_11_3, "append-suffix function heads lower through structural decons and recover tail data",
    [['=', [myfunc, '$A', '$B'], [append, [append, [42], '$A'], '$B']],
     ['=', [h, [myfunc, [10], '$B'], '$C'], ['$B', '$C']]],
    program_normalizes_append_suffix_function_head).

test_petta_to_he_program(1_5_11_4, "equality-form function-call inversion rejoins the same structural head path",
    [['=', [myfunc, '$A', '$B'], [append, [append, [42], '$A'], '$B']],
     ['=', [h_unify, '$A', '$C'],
      [if, ['=', '$A', [myfunc, [10], '$B']], ['$B', '$C'], [empty]]]],
    program_normalizes_function_call_inversion_eq_guard).

test_petta_to_he_program(1_5_11_5, "structural function-call inversion let-patterns lower through decons and raw application",
    [['=', [f, '$Head', '$Tail'], [append, ['$Head'], '$Tail']],
     ['=', [probe], [let, [f, '$Head', '$Tail'], [1, 2, 3, 4], ['$Head', '$Tail']]]],
    program_normalizes_structural_function_call_inversion_let_pattern).

test_petta_to_he_program(1_5_11_6, "pure arithmetic function-call inversion let-patterns are rejected instead of miscompiled",
    [['=', [g, '$X', '$Y', '$Z'], [append, [['#+', '$X', '$Z']], '$Y']],
     ['=', [probe], [let, [g, '$X', '$Y', 35], [42, 2, 3], ['$X', '$Y', 40]]]],
    translation_error(domain_error(he_core_surface, arithmetic_inversion))).

test_petta_to_he_ffi_tokens(1, "ffi-tokens mode emits explicit function-call inversion marker for arithmetic let-patterns",
    [['=', [g, '$X', '$Y', '$Z'], [append, [['#+', '$X', '$Z']], '$Y']],
     ['=', [probe], [let, [g, '$X', '$Y', 35], [42, 2, 3], ['$X', '$Y', 40]]]],
    program_uses_ffi_function_call_inversion_helper).

test_petta_to_he_program(1_5_12, "call-result equality condition binds once and compares with ==",
    [['=', [trickyspec, '$f'],
      [if, ['=', ['$f', 1], 2], [trickyspec, ['+', 2]], ['$f', 1]]]],
    program_normalizes_callable_equality_condition).

test_petta_to_he_program(1_6, "program-level length helper uses direct size-atom",
    [['=', [probe], [length, [1, 2, 3]]]],
    program_uses_direct_length_helper).

test_petta_to_he_program(1_7, "program-level user-defined msort stays user-defined",
    [['=', [msort, '$x'], '$x'],
     ['=', [probe], [msort, [3, 1, 2]]]],
    program_uses_user_defined_msort).

test_petta_to_he_program(2, "program-level user-defined test stays user-defined",
    [['=', [test, '$x'], '$x'],
     ['=', [probe], [test, ['+', 1, 2], 3]]],
    program_uses_user_defined_test).

test_petta_to_he(32, "generic length stays length (compat helper is file-level)",
    [length, [foo, bar]],
    [length, [foo, bar]]).

test_petta_to_he(33, "hyperpose → superpose",
    [hyperpose, [['prime?', 2], ['prime?', 3]]],
    [superpose, [['prime?', 2], ['prime?', 3]]]).

test_petta_to_he(34, "pure once(hyperpose ...) → first result via collapse/case/decons",
    [once, [hyperpose, [[slow-branch], [cheap-branch]]]],
    pure_once_shape([superpose, [[slow-branch], [cheap-branch]]])).

test_petta_to_he(35, "computed hyperpose input stays computed after superpose lowering",
    [let, '$xs', [1, 2, 3], [hyperpose, '$xs']],
    [let, '$xs', [1, 2, 3], [superpose, '$xs']]).

test_petta_to_he(36, "pure cut is rejected rather than silently miscompiled",
    [cut],
    translation_error(domain_error(he_core_surface, cut))).

test_petta_to_he(37, "pure canonical Goal,cut idiom lowers to first-result once",
    ['let*', [['$x', [match, '&self', [foo, '$1'], '$1']],
              ['$temp', [cut]]],
     '$x'],
    pure_once_shape([match, '&self', [foo, '$1'], '$1'])).

test_petta_to_he(38, "pure unprovided msort is rejected rather than silently preserved",
    [msort, [collapse, [match, '&self', '$x', '$x']]],
    translation_error(domain_error(he_core_surface, msort))).

test_petta_to_he(38_1, "pure finite exists match emptiness check keeps the canonical once/collapse boundary",
    ['==', '()', [collapse, [once, [match, '$Space', '$Atom', '$Atom']]]],
    finite_exists_match_shape([match, '$Space', '$Atom', '$Atom'])).

test_petta_to_he(38_2, "pure singleton once over deterministic equality lowers to dedicated singleton witness surface",
    [once, ['=', '$x', 42]],
    singleton_visible_witness_shape([unify, '$x', 42, 'True', 'Empty'])).

test_petta_to_he(39, "plain let preserves tuple binders as patterns",
    [let, ['$x', '$y'], [1, 2], ['$x', '$y']],
    [let, ['$x', '$y'], [1, 2], [eval, ['atom-subst', '$x', '$fun', ['$fun', '$y']]]]).

test_petta_to_he(40, "let* preserves tuple binders as patterns",
    ['let*', [[['$x', '$y'], [1, 2]], ['$z', 3]], ['$x', '$y', '$z']],
    ['let*', [[['$x', '$y'], [1, 2]], ['$z', 3]], [eval, ['atom-subst', '$x', '$fun', ['$fun', '$y', '$z']]]]).

test_petta_to_he(41, "fake lambda preserves tuple parameters as patterns",
    [lambda, ['$x', '$y'], ['+', '$x', '$y']],
    [lambda, ['$x', '$y'], ['+', '$x', '$y']]).

test_petta_to_he(42, "compiled lambda preserves tuple parameters as patterns",
    ['|->', ['$x', '$y'], ['+', '$x', '$y']],
    ['|->', ['$x', '$y'], ['+', '$x', '$y']]).

%% ═══════════════════════════════════════════════════════════════
%% PeTTa → HE hyperpose-preserving mode tests
%% ═══════════════════════════════════════════════════════════════

test_petta_to_he_hyperpose(1, "hyperpose-preserving mode keeps hyperpose",
    [hyperpose, [['prime?', 2], ['prime?', 3]]],
    [hyperpose, [['prime?', 2], ['prime?', 3]]]).

test_petta_to_he_hyperpose(2, "pure preserve-hyperpose once(...) → first result via collapse/case/decons",
    [once, [hyperpose, [[slow-branch], [cheap-branch]]]],
    pure_once_shape([hyperpose, [[slow-branch], [cheap-branch]]])).

test_petta_to_he_hyperpose(3, "computed hyperpose input stays computed in preserve mode",
    [let, '$xs', [1, 2, 3], [hyperpose, '$xs']],
    [let, '$xs', [1, 2, 3], [hyperpose, '$xs']]).

test_petta_to_he_petta_he(1, "PeTTa HE profile keeps once(superpose ...)",
    [once, [hyperpose, [[slow-branch], [cheap-branch]]]],
    [once, [superpose, [[slow-branch], [cheap-branch]]]]).

test_petta_to_he_petta_he(2, "PeTTa HE profile preserves cut",
    [cut],
    [cut]).

test_petta_to_he_petta_he(3, "PeTTa HE profile preserves native msort",
    [msort, [collapse, [match, '&self', '$x', '$x']]],
    [msort, [collapse, [match, '&self', '$x', '$x']]]).

test_petta_to_he_petta_he(4, "PeTTa HE profile preserves lambda body variable-head tuples",
    ['|->', ['$x'], ['$x', 2, 3]],
    ['|->', ['$x'], ['$x', 2, 3]]).

test_petta_to_he_petta_he(5, "PeTTa HE profile preserves structured let* body variable-head tuples",
    ['let*', [[['$f1', '$c1', 3], [1, 2, '$d1']]], ['$f1', '$c1', '$d1']],
    ['let*', [[['$f1', '$c1', 3], [1, 2, '$d1']]], ['$f1', '$c1', '$d1']]).

test_petta_to_he_petta_he(5_1, "PeTTa HE profile preserves flat expression-head tuples",
    [[link, '$x', human], [link, '$y', human], [link, '$z', human]],
    [[link, '$x', human], [link, '$y', human], [link, '$z', human]]).

test_petta_to_he_petta_he(5_2, "PeTTa HE profile preserves expression-headed iterate state tuples",
    [[+, '$t', 1], 1, [+, '$sum', [*, '$t', '$i']]],
    [[+, '$t', 1], 1, [+, '$sum', [*, '$t', '$i']]]).

test_petta_to_he_petta_he(5_3, "PeTTa HE profile preserves non-variable function heads in declarations",
    ['=', [successor, b, a], 'True'],
    ['=', [successor, b, a], 'True']).

test_petta_to_he_petta_he(5_4, "PeTTa HE profile preserves native eval surface",
    [eval, '$code'],
    [eval, '$code']).

test_petta_to_he_petta_he(5_4_1, "PeTTa HE profile preserves native call surface",
    [call, '$code'],
    [call, '$code']).

test_petta_to_he_petta_he(5_4_2, "PeTTa HE profile preserves native reduce surface",
    [reduce, '$code'],
    [reduce, '$code']).

test_petta_to_he_petta_he(5_5, "PeTTa HE profile preserves member-filter source calls in bodies",
    [in, ['+', 1, 3], [3, 4, 5]],
    [in, ['+', 1, 3], [3, 4, 5]]).

test_petta_to_he_petta_he(5_6, "PeTTa HE profile preserves expression-data arguments without quote injection",
    [map-flat3, [p1, [1, 2]]],
    [map-flat3, [p1, [1, 2]]]).

test_petta_to_he_petta_he(6, "PeTTa HE profile preserves native partial builtin values",
    ['+', 2],
    ['+', 2]).

test_petta_to_he_petta_he_hyperpose(1, "PeTTa HE profile preserve-hyperpose keeps once(hyperpose ...)",
    [once, [hyperpose, [[slow-branch], [cheap-branch]]]],
    [once, [hyperpose, [[slow-branch], [cheap-branch]]]]).

%% ═══════════════════════════════════════════════════════════════
%% PeTTa → HE extended mode tests
%% ═══════════════════════════════════════════════════════════════

test_petta_to_he_ext(1, "foldall (extended) → let(collect) + foldl-atom",
    [foldall, merge, [twohop-item], 0],
    foldall_shape_ext(merge, [twohop-item], 0)).

test_petta_to_he_ext(2, "extended once(...) → select 1(...)",
    [once, [superpose, [1, 2]]],
    [select, 1, [superpose, [1, 2]]]).

test_petta_to_he_ext_hyperpose(1, "extended hyperpose-preserving mode keeps hyperpose",
    [hyperpose, [['prime?', 2], ['prime?', 3]]],
    [hyperpose, [['prime?', 2], ['prime?', 3]]]).

test_petta_to_he_ext_hyperpose(2, "extended hyperpose-preserving once(...) → select 1(hyperpose ...)",
    [once, [hyperpose, [[slow-branch], [cheap-branch]]]],
    [select, 1, [hyperpose, [[slow-branch], [cheap-branch]]]]).

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

test_rel_petta_to_he(1, "relational core rejects pure cut",
    [cut],
    fails).

test_rel_petta_to_he(2, "relational core rejects unprovided msort",
    [msort, [collapse, [match, '&self', '$x', '$x']]],
    fails).

test_rel_petta_to_he(3, "relational core exposes append-suffix head-pattern extension shape",
    [head_extension, [42, 10], '$arg', '$tail', '$C'],
    append_suffix_head_extension_shape).

test_rel_petta_to_he(4, "relational core exposes structural append-suffix let-pattern extension helper surface",
    [let_extension, ['$Head'], [1, 2, 3, 4], '$Tail', ['__tr-raw-apply1', '$Head', '$Tail']],
    append_suffix_let_extension_shape).

test_rel_petta_to_he(5, "relational core exposes singleton visible witness surface",
    [once, ['=', '$x', 42]],
    ['singleton-visible-witness', [unify, '$x', 42, 'True', 'Empty']]).

%% ═══════════════════════════════════════════════════════════════
%% Test runner
%% ═══════════════════════════════════════════════════════════════

run_tests :-
    with_output_to(string(Output), run_tests_body),
    write(Output),
    \+ sub_string(Output, _, _, _, "  ✗"),
    \+ sub_string(Output, _, _, _, "  ?").

run_tests_body :-
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
    format("~n=== PeTTa → HE Program Tests ===~n"),
    forall(test_petta_to_he_program(N, Name, Input, Expected),
        run_one_pe_program(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE FFI-Tokens Mode Tests ===~n"),
    forall(test_petta_to_he_ffi_tokens(N, Name, Input, Expected),
        run_one_pe_ffi_tokens(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE Hyperpose-Preserving Mode Tests ===~n"),
    forall(test_petta_to_he_hyperpose(N, Name, Input, Expected),
        run_one_pe_hyperpose(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE PeTTa Profile Mode Tests ===~n"),
    forall(test_petta_to_he_petta_he(N, Name, Input, Expected),
        run_one_pe_petta_he(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE PeTTa Profile Hyperpose Mode Tests ===~n"),
    forall(test_petta_to_he_petta_he_hyperpose(N, Name, Input, Expected),
        run_one_pe_petta_he_hyperpose(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE Trusted Tests ===~n"),
    forall(test_petta_to_he_trusted(N, Name, Input, Expected),
        run_one_pe_trusted(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE Extended Mode Tests ===~n"),
    forall(test_petta_to_he_ext(N, Name, Input, Expected),
        run_one_pe_ext(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE Extended Hyperpose-Preserving Mode Tests ===~n"),
    forall(test_petta_to_he_ext_hyperpose(N, Name, Input, Expected),
        run_one_pe_ext_hyperpose(N, Name, Input, Expected)),
    format("~n=== PeTTa → HE Optimization Tests ===~n"),
    forall(test_petta_to_he_opt(N, Name, Input, Expected),
        run_one_pe_opt(N, Name, Input, Expected)),
    format("~n=== Normalization Tests (HE → PeTTa → HE normal form) ===~n"),
    forall(test_roundtrip(N, Name, Input, Expected),
        run_one_rt(N, Name, Input, Expected)),
    format("~n=== Relational PeTTa → HE Boundary Tests ===~n"),
    forall(test_rel_petta_to_he(N, Name, Input, Expected),
        run_one_rel_pe(N, Name, Input, Expected)).

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

run_one_pe_hyperpose(N, Name, Input, pure_once_shape(ExpectedInner)) :- !,
    (   pe_translate_term_hyperpose(Input, Result)
    ->  (   pure_once_result_shape(Result, ExpectedInner)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w (bad pure once lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_hyperpose(N, Name, Input, Expected) :-
    (   test_petta_to_he_hyperpose(N, _, Input, _),
        (   Input = ['=', _, _]
        ->  pe_translate_decl_hyperpose(Input, Result)
        ;   pe_translate_term_hyperpose(Input, Result)
        ),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n", [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_pe_petta_he(N, Name, Input, Expected) :-
    (   test_petta_to_he_petta_he(N, _, Input, _),
        (   Input = ['=', _, _]
        ->  pe_translate_decl_petta_he(Input, Result)
        ;   pe_translate_term_petta_he(Input, Result)
        ),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n", [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_pe_petta_he_hyperpose(N, Name, Input, Expected) :-
    (   test_petta_to_he_petta_he_hyperpose(N, _, Input, _),
        (   Input = ['=', _, _]
        ->  pe_translate_decl_petta_he_hyperpose(Input, Result)
        ;   pe_translate_term_petta_he_hyperpose(Input, Result)
        ),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n", [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, foldl_atom_short_shape(List, Init, Agg)) :- !,
    (   pe_translate_term(Input, Result)
    ->  (   Result = ['foldl-atom', List, Init, AccVar, ItemVar,
                      [eval, [Agg, AccVar, ItemVar]]],
            atom_string(AccVar, AccS),
            atom_string(ItemVar, ItemS),
            sub_string(AccS, 0, _, _, "$__tr_"),
            sub_string(ItemS, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w (fresh binders: ~w, ~w)~n",
                    [N, Name, AccVar, ItemVar])
        ;   format("  ✗ ~w: ~w (bad short foldl-atom lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, length_collapse_shape(Goal)) :- !,
    (   pe_translate_term(Input, Result)
    ->  (   Result = [let, TupleVar, [collapse, Goal], ['size-atom', TupleVar]],
            atom_string(TupleVar, TupleS),
            sub_string(TupleS, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w (fresh tuple binder: ~w)~n", [N, Name, TupleVar])
        ;   format("  ✗ ~w: ~w (bad length(collapse ...) lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, test_length_collapse_shape(Goal, Expected)) :- !,
    (   pe_translate_term(Input, Result)
        ->  (   Result = [test, [let, TupleVar, [collapse, Goal], ['size-atom', TupleVar]], Expected],
            atom_string(TupleVar, TupleS),
            sub_string(TupleS, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w (fresh tuple binder: ~w)~n", [N, Name, TupleVar])
        ;   format("  ✗ ~w: ~w (bad test length(collapse ...) lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, pure_once_shape(ExpectedInner)) :- !,
    (   pe_translate_term(Input, Result)
    ->  (   pure_once_result_shape(Result, ExpectedInner)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w (bad pure once lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, finite_exists_match_shape(ExpectedInner)) :- !,
    (   pe_translate_term(Input, Result)
    ->  (   finite_exists_match_result_shape(Result, ExpectedInner)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w (bad finite exists-match lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, singleton_visible_witness_shape(ExpectedInner)) :- !,
    (   pe_translate_term(Input, Result)
    ->  (   singleton_visible_witness_result_shape(Result, ExpectedInner)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w (bad singleton-visible-witness lowering: ~w)~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, translation_error(ExpectedError)) :- !,
    catch((pe_translate_term(Input, Result),
           Outcome = translated(Result)),
          error(Error, _Context),
          Outcome = error(Error)),
    (   Outcome = error(ExpectedError)
    ->  format("  ✓ ~w: ~w~n", [N, Name])
    ;   format("  ✗ ~w: ~w~n    Expected error: ~w~n    Got:      ~w~n",
               [N, Name, ExpectedError, Outcome])
    ).

pure_once_result_shape(Result, ExpectedInner) :-
    Result = [let, TupleVar, [collapse, ExpectedInner],
              [case, TupleVar,
               [['()', 'Empty'],
                [NonemptyVar,
                 [let, [HeadVar, TailVar],
                  ['decons-atom', NonemptyVar],
                  HeadVar]]]]],
    atom_string(TupleVar, TupleS),
    atom_string(NonemptyVar, NonemptyS),
    atom_string(HeadVar, HeadS),
    atom_string(TailVar, TailS),
    sub_string(TupleS, 0, _, _, "$__tr_"),
    sub_string(NonemptyS, 0, _, _, "$__tr_"),
    sub_string(HeadS, 0, _, _, "$__tr_"),
    sub_string(TailS, 0, _, _, "$__tr_").

finite_exists_match_result_shape(Result, ExpectedInner) :-
    Result = ['==', '()', [collapse, OnceExpr]],
    pure_once_result_shape(OnceExpr, ExpectedInner).

singleton_visible_witness_result_shape(Result, ExpectedInner) :-
    Result = ['singleton-visible-witness', ExpectedInner].

run_one_pe_program(N, Name, Input, program_uses_builtin_test_helper) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                [':', 'petta-test-equal', ['->', 'Atom', 'Atom', 'Bool']],
                ['=', ['petta-test-equal', '$actual', '$expected'], TestBody],
                ['=', [probe], ['petta-test-equal', ['+', 1, 2], 3]]
            ],
            \+ contains_symbol(collapse, TestBody),
            contains_symbol('==', TestBody),
            contains_symbol('println!', TestBody),
            contains_symbol('format-args', TestBody)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_direct_length_helper) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', [length, '$expr'], ['size-atom', '$expr']],
                ['=', [probe], [length, [1, 2, 3]]]
            ]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_user_defined_msort) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [['=', [msort, '$x'], '$x'],
                     ['=', [probe], [msort, [3, 1, 2]]]]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_collapse_test_helper) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', [NormalizeFun, '$tuple'], NormalizeBody],
                [':', 'petta-test-results', ['->', 'Atom', 'Atom', 'Bool']],
                ['=', ['petta-test-results', '$actual', '$expected'], TestBody],
                ['=', [probe], ['petta-test-results', [if, '$x', yes, no], [yes, no]]]
            ],
            atom(NormalizeFun),
            contains_symbol(case, NormalizeBody),
            contains_symbol(collapse, TestBody),
            contains_symbol(NormalizeFun, TestBody),
            contains_symbol('==', TestBody),
            contains_symbol('println!', TestBody),
            contains_symbol('format-args', TestBody)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_bag_test_helper) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                [':', 'petta-test-bag-equal', ['->', 'Atom', 'Atom', 'Bool']],
                ['=', ['petta-test-bag-equal', '$actual', '$expected'], TestBody],
                ['=', [probe_bag], ['petta-test-bag-equal',
                                    [match, '&self', [foo, '$x'], '$x'],
                                    [1, 1, 2]]]
            ],
            contains_symbol(collapse, TestBody),
            contains_symbol('subtraction-atom', TestBody),
            contains_symbol('println!', TestBody)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_mixed_test_helpers) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   member([':', 'petta-test-equal', ['->', 'Atom', 'Atom', 'Bool']], Result),
            member(['=', ['petta-test-equal', '$actual', '$expected'], EqualBody], Result),
            member(['=', [NormalizeFun, '$tuple'], NormalizeBody], Result),
            member([':', 'petta-test-results', ['->', 'Atom', 'Atom', 'Bool']], Result),
            member(['=', ['petta-test-results', '$actual', '$expected'], ResultsBody], Result),
            member(['=', [probe_direct], ['petta-test-equal', ['+', 1, 2], 3]], Result),
            member(['=', [probe_results], ['petta-test-results', [if, '$x', yes, no], [yes, no]]], Result),
            atom(NormalizeFun),
            contains_symbol(case, NormalizeBody),
            contains_symbol(collapse, ResultsBody),
            contains_symbol(NormalizeFun, ResultsBody),
            \+ contains_symbol(collapse, EqualBody),
            contains_symbol('println!', ResultsBody),
            contains_symbol('println!', EqualBody)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_routes_alpha_test_direct) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   member(['=', [probe_alpha],
                     ['petta-test-equal',
                      ['=alpha', ['Father', '$X'], ['Father', '$Y']],
                      'True']], Result),
            \+ member(['=', [probe_alpha],
                       ['petta-test-results',
                        ['=alpha', ['Father', '$X'], ['Father', '$Y']],
                        'True']], Result)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_routes_chain_test_direct) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   member(['=', [probe_chain],
                     ['petta-test-equal',
                      [let, _, ['+', 2, 4], [let, _, ['*', 3, '$n'], ['*', 3, '$n']]],
                      18]], Result)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   member(['=', [probe_chain], ProbeBody], Result),
            ProbeBody = ['petta-test-equal', _, 18]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_native_quote) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [['=', [probe], [quote, ['+', 1, 2]]]]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_petta_state_helpers) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', ['__tr-petta-state-clear!', '$name'], _],
                ['=', ['__tr-petta-state-set!', '$name', '$value'], _],
                ['=', ['__tr-petta-state-get', '$name'], _],
                ['=', [probe],
                 [let, Discard1, ['__tr-petta-state-set!', state, rest],
                  [let, Discard2, ['__tr-petta-state-set!', state, active],
                   ['__tr-petta-state-get', state]]]]
            ],
            atom_string(Discard1, Discard1S),
            atom_string(Discard2, Discard2S),
            sub_string(Discard1S, 0, _, _, "$__tr_"),
            sub_string(Discard2S, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

contains_symbol(Sym, Term) :-
    Term == Sym.
contains_symbol(Sym, Term) :-
    is_list(Term),
    member(Subterm, Term),
    contains_symbol(Sym, Subterm).

run_one_pe_ffi_tokens(N, Name, Input, program_uses_ffi_function_call_inversion_helper) :- !,
    (   pe_translate_program_ffi_tokens(Input, Result)
    ->  (   member([':', 'petta-ffi-function-call-inversion', ['->', 'Atom', 'Atom', 'Atom', 'Atom', 'Atom']], Result),
            member(['=', ['petta-ffi-function-call-inversion', '$lane', '$pattern', '$observed', '$continuation'], OracleBody], Result),
            member(['=', [probe],
                    ['petta-ffi-function-call-inversion',
                     'arithmetic-append-suffix',
                     [quote, [g, '$X', '$Y', 35]],
                     [42, 2, 3],
                     [eval, ['atom-subst', '$X', '$fun', ['$fun', '$Y', 40]]]]], Result),
            contains_symbol('Error', OracleBody)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_native_quote_ignores_source_quoted_syntax) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', ['quoted-syntax', '$x'], [user_quote, '$x']],
                ['=', [probe], [quote, ['+', 1, 2]]]
            ]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_state_helpers_avoid_source_symbols) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', [Clear, '$name'], ClearBody],
                ['=', [Set, '$name', '$value'], SetBody],
                ['=', [Get, '$name'], GetBody],
                ['=', ['__tr-petta-state-clear!', '$x'], [user_clear, '$x']],
                ['=', ['__tr-petta-state-set!', '$x', '$y'], [user_set, '$x', '$y']],
                ['=', ['__tr-petta-state-get', '$x'], [user_get, '$x']],
                ['=', ['__tr-petta-state-cell', '$x', '$y'], [user_cell, '$x', '$y']],
                ['=', [probe],
                 [let, Discard1, [Set, state, rest],
                  [let, Discard2, [Set, state, active],
                   [Get, state]]]]
            ],
            Clear \= '__tr-petta-state-clear!',
            Set \= '__tr-petta-state-set!',
            Get \= '__tr-petta-state-get',
            contains_symbol(Clear, SetBody),
            \+ contains_symbol('__tr-petta-state-cell', ClearBody),
            \+ contains_symbol('__tr-petta-state-cell', GetBody),
            atom_string(Discard1, Discard1S),
            atom_string(Discard2, Discard2S),
            sub_string(Discard1S, 0, _, _, "$__tr_"),
            sub_string(Discard2S, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w (helpers: ~w, ~w, ~w)~n", [N, Name, Clear, Set, Get])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_append_helper) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', [append, '()', '$ys'], '$ys'],
                ['=', [append, '$xs', '$ys'], AppendBody],
                ['=', [probe], [append, [1], [2, 3]]]
            ],
            contains_symbol('decons-atom', AppendBody),
            contains_symbol('cons-atom', AppendBody)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_second_from_pair_helper) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                [':', 'second-from-pair', ['->', 'Atom', 'Atom']],
                ['=', ['second-from-pair', '$pair'], HelperBody],
                ['=', [probe], ['second-from-pair', [a, b]]]
            ],
            contains_symbol(unify, HelperBody),
            contains_symbol(return, HelperBody),
            contains_symbol('Error', HelperBody)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_user_defined_second_from_pair) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', ['second-from-pair', '$pair'], '$pair'],
                ['=', [probe], ['second-from-pair', [a, b]]]
            ]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_rewrites_partial_builtin_helper) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', [HelperName, ArgVar], ['+', 1, ArgVar]],
                ['=', [probe], HelperName]
            ],
            atom(HelperName),
            sub_atom(HelperName, 0, _, _, 'petta-partial-'),
            atom_string(ArgVar, ArgVarS),
            sub_string(ArgVarS, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_curried_callable_result) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                [':', 'petta-lambda', ['->', 'Atom', '$t', ['->', '$a', '$t']]],
                ['=', [['petta-lambda', '$var', '$body'], '$arg'],
                 [let, '$var', '$arg', '$body']],
                ['=', [mp], ['petta-lambda', Arg1, ['petta-lambda', Arg2, ['+', Arg1, Arg2]]]],
                ['=', [probe], [[[mp], 1], 1]]
            ],
            atom_string(Arg1, Arg1S),
            atom_string(Arg2, Arg2S),
            sub_string(Arg1S, 0, _, _, "$__tr_"),
            sub_string(Arg2S, 0, _, _, "$__tr_")
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_rewrites_partial_composition_helper) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   memberchk(['=', [HelperMul, ParamMul], ['*', 2, ParamMul]], Result),
            memberchk(['=', [HelperAdd, ParamAdd], ['+', 1, ParamAdd]], Result),
            memberchk(['=', [HelperCompose, Param],
                       [HelperMul, [HelperAdd, Param]]], Result),
            memberchk(['=', [plus1times2], HelperCompose], Result)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_canonicalizes_map_flat) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                [':', Apply1, ['->', 'Atom', 'Atom', 'Atom']]
                | _
            ],
            Apply1Body = [if, ['==', '$f', '+'],
                          ['petta-lambda', '$x', ['+', '$arg', '$x']],
                          [function,
                           [chain, [eval, ['atom-subst', '$f', '$fun', ['$fun', '$arg']]],
                            '$call',
                            [chain, [eval, '$call'], '$mid',
                             [chain, [eval, '$mid'], '$res', [return, '$res']]]]]],
            memberchk(['=', [Apply1, ['petta-lambda', '$var', '$body'], '$arg'],
                       [let, '$var', '$arg', '$body']], Result),
            memberchk(['=', [Apply1, '$f', '$arg'], Apply1Body], Result),
            memberchk(['=', ['map-flat', '$f', '$list'],
                       ['map-atom', '$list', '$item', [Apply1, '$f', '$item']]], Result)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_canonicalizes_fold_nested) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                [':', Apply1, ['->', 'Atom', 'Atom', 'Atom']]
                | _
            ],
            memberchk([':', Apply2, ['->', 'Atom', 'Atom', 'Atom', 'Atom']], Result),
            Apply1Body = [if, ['==', '$f', '+'],
                          ['petta-lambda', '$x', ['+', '$arg', '$x']],
                          [function,
                           [chain, [eval, ['atom-subst', '$f', '$fun', ['$fun', '$arg']]],
                            '$call',
                            [chain, [eval, '$call'], '$mid',
                             [chain, [eval, '$mid'], '$res', [return, '$res']]]]]],
            memberchk(['=', [Apply1, ['petta-lambda', '$var', '$body'], '$arg'],
                       [let, '$var', '$arg', '$body']], Result),
            memberchk(['=', [Apply1, '$f', '$arg'], Apply1Body], Result),
            memberchk(['=', [Apply2, '$f', '$arg1', '$arg2'],
                       [if, ['==', '$f', '+'],
                        ['+', '$arg1', '$arg2'],
                        [Apply1, [Apply1, '$f', '$arg1'], '$arg2']]], Result),
            memberchk(['=', ['fold-nested', '$f', '$init', '$list'],
                       ['foldl-atom', '$list', '$init', '$acc', '$item',
                        [if, ['==', ['get-metatype', '$item'], 'Expression'],
                         ['fold-nested', '$f', '$acc', '$item'],
                         [Apply2, '$f', '$acc', '$item']]]], Result)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_preserves_direct_binary_composition) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', ['.:', '$f1', '$f2', '$arg1', '$arg2'],
                 ['$f1', ['$f2', '$arg1', '$arg2']]]
            ]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_canonicalizes_roman_eqeq_intersection) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', ['/==\\', '$a', '$b'],
                 [let, '$intersection', ['intersection-atom', '$a', '$b'], '$intersection']]
            ]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_canonicalizes_roman_eqeq_subtraction) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', ['\\==', '$a', '$b'],
                 [let, '$difference', ['subtraction-atom', '$a', '$b'], '$difference']]
            ]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_canonicalizes_roman_eqeq_union) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', ['\\==/', '$a', '$b'],
                 [let, '$difference', ['subtraction-atom', '$a', '$b'],
                  ['union-atom', '$difference', '$b']]]
            ]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_normalizes_function_head_patterns) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', ['is-member', '$item', '$tuple'],
                 [not,
                  ['==',
                   [collapse,
                    [let, '$x', [superpose, '$tuple'],
                     [if, ['==', '$x', '$item'],
                      'True',
                      [empty]]]],
                   '()']]],
                ['=', [in, '$x', '$L'],
                 [let, 'True', ['is-member', '$x', '$L'], '$x']],
                ['=', [myplus, Arg1, Arg2],
                 [let, Candidate1, [superpose, [1, 2, 3]],
                  [unify, Candidate1, Arg1,
                   [let, Candidate2, [superpose, [2, 3]],
                    [unify, Candidate2, Arg2,
                     [let, SumVar, ['+', Candidate1, Candidate2],
                      [let, 'True', ['is-member', SumVar, [3, 4, 5]], SumVar]],
                     'Empty']],
                   'Empty']]]
            ],
            atom_string(Arg1, Arg1S),
            atom_string(Arg2, Arg2S),
            atom_string(Candidate1, Candidate1S),
            atom_string(Candidate2, Candidate2S),
            atom_string(SumVar, SumVarS),
            sub_string(Arg1S, 0, _, _, "$__tr_head_arg_"),
            sub_string(Arg2S, 0, _, _, "$__tr_head_arg_"),
            sub_string(Candidate1S, 0, _, _, "$__tr_head_candidate_"),
            sub_string(Candidate2S, 0, _, _, "$__tr_head_candidate_"),
            sub_string(SumVarS, 0, _, _, "$__tr_member_value_")
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_normalizes_append_suffix_function_head) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   memberchk(['=', [myfunc, '$A', '$B'], [append, [append, [42], '$A'], '$B']], Result),
            memberchk(['=', [h, Arg1, '$C'], Body], Result),
            atom_string(Arg1, Arg1S),
            sub_string(Arg1S, 0, _, _, "$__tr_head_arg_"),
            contains_symbol('decons-atom', Body),
            contains_symbol('first-from-pair', Body),
            contains_symbol('second-from-pair', Body),
            contains_symbol(unify, Body),
            contains_symbol('atom-subst', Body),
            \+ contains_symbol('petta-apply1', Body),
            \+ contains_symbol(case, Body)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_normalizes_function_call_inversion_eq_guard) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   memberchk(['=', [myfunc, '$A', '$B'], [append, [append, [42], '$A'], '$B']], Result),
            memberchk(['=', [h_unify, Arg1, '$C'], Body], Result),
            atom_string(Arg1, Arg1S),
            sub_string(Arg1S, 0, _, _, "$__tr_head_arg_"),
            contains_symbol('decons-atom', Body),
            contains_symbol('first-from-pair', Body),
            contains_symbol('second-from-pair', Body),
            contains_symbol(unify, Body),
            contains_symbol('atom-subst', Body),
            \+ contains_symbol('petta-apply1', Body),
            \+ contains_symbol(case, Body)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_normalizes_structural_function_call_inversion_let_pattern) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   memberchk(['=', [f, '$Head', '$Tail'], [append, ['$Head'], '$Tail']], Result),
            memberchk(['=', [probe], Body], Result),
            contains_symbol('decons-atom', Body),
            contains_symbol('first-from-pair', Body),
            contains_symbol('second-from-pair', Body),
            contains_symbol('atom-subst', Body),
            \+ contains_symbol('petta-apply1', Body),
            \+ contains_symbol([let, [f, '$Head', '$Tail']], Body)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, translation_error(ExpectedError)) :- !,
    catch((pe_translate_program(Input, Result),
           Outcome = translated(Result)),
          error(Error, _Context),
          Outcome = error(Error)),
    (   Outcome = error(ExpectedError)
    ->  format("  ✓ ~w: ~w~n", [N, Name])
    ;   format("  ✗ ~w: ~w~n    Expected error: ~w~n    Got: ~w~n",
                [N, Name, ExpectedError, Outcome])
    ).

run_one_pe_program(N, Name, Input, program_selectively_freshens_function_head_args) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', [animal, '$X'], [only, [[living, '$X'], [being, '$X']], '$X']],
                ['=', [tagged_cat, Arg1, '$tag'],
                 [chain, [animal, '$X'], Candidate,
                  [unify, Candidate, Arg1,
                   [pair, Candidate, '$tag'],
                   'Empty']]]
            ],
            atom_string(Arg1, Arg1S),
            atom_string(Candidate, CandidateS),
            sub_string(Arg1S, 0, _, _, "$__tr_head_arg_"),
            sub_string(CandidateS, 0, _, _, "$__tr_head_candidate_")
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_normalizes_duplicate_function_head_vars) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [
                ['=', [same, '$x', Arg2],
                 [unify, Arg2, '$x', ok, 'Empty']]
            ],
            atom_string(Arg2, Arg2S),
            sub_string(Arg2S, 0, _, _, "$__tr_head_arg_")
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_normalizes_callable_equality_condition) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   memberchk([':', Apply1, ['->', 'Atom', 'Atom', 'Atom']], Result),
            memberchk(['=', [PartialHelper, Param], ['+', 2, Param]], Result),
            memberchk(['=', [trickyspec, '$f'],
                       [let, CallResult, [Apply1, '$f', 1],
                        [if, ['==', CallResult, 2],
                         [trickyspec, PartialHelper],
                         CallResult]]], Result)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (translation error)~n", [N, Name])
    ).

run_one_pe_program(N, Name, Input, program_uses_user_defined_test) :- !,
    (   pe_translate_program(Input, Result)
    ->  (   Result = [['=', [test, '$x'], '$x'],
                     ['=', [probe], [test, ['+', 1, 2], 3]]]
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
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

run_one_pe_ext(N, Name, Input, Expected) :-
    (   test_petta_to_he_ext(N, _, Input, _),
        (   Input = ['=', _, _]
        ->  petta_to_he:translate_decl_extended(Input, Result)
        ;   petta_to_he:translate_term_extended(Input, Result)
        ),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n", [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_pe_ext_hyperpose(N, Name, Input, Expected) :-
    (   test_petta_to_he_ext_hyperpose(N, _, Input, _),
        (   Input = ['=', _, _]
        ->  pe_translate_decl_ext_hyperpose(Input, Raw),
            petta_to_he:optimize_decl(Raw, Result)
        ;   pe_translate_term_ext_hyperpose(Input, Result)
        ),
        (   Result == Expected
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Expected: ~w~n    Got:      ~w~n", [N, Name, Expected, Result])
        )
    ;   format("  ? ~w: ~w (error)~n", [N, Name])
    ).

run_one_pe(N, Name, Input, partial_builtin_lambda_shape(Fun, PrefixArg)) :- !,
    (   test_petta_to_he(N, _, Input, _),
        petta_to_he:translate_term(Input, Result),
        Result = ['petta-lambda', ArgVar, [Fun, PrefixArg, ArgVar]],
        atom_string(ArgVar, ArgVarS),
        sub_string(ArgVarS, 0, _, _, "$__tr_")
    ->  format("  ✓ ~w: ~w~n", [N, Name])
    ;   format("  ✗ ~w: ~w~n    Got unexpected partial builtin lowering~n", [N, Name])
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

run_one_rel_pe(N, Name, Input, fails) :- !,
    (   rel_pe_translate_term(Input, Result)
    ->  format("  ✗ ~w: ~w~n    Expected relational failure, got: ~w~n",
               [N, Name, Result])
    ;   format("  ✓ ~w: ~w~n", [N, Name])
    ).

run_one_rel_pe(N, Name,
               [head_extension, PrefixElems, Actual, TailVar, ApplyArg],
               append_suffix_head_extension_shape) :- !,
    (   rel_pe_append_suffix_head_extension(PrefixElems, Actual, TailVar, ApplyArg, Result)
    ->  (   contains_symbol('decons-atom', Result),
            contains_symbol('first-from-pair', Result),
            contains_symbol('second-from-pair', Result),
            contains_symbol('__tr-raw-apply1', Result),
            \+ contains_symbol(case, Result)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (relational translation error)~n", [N, Name])
    ).

run_one_rel_pe(N, Name,
               [let_extension, PrefixElems, Observed, TailVar, RawBody],
               append_suffix_let_extension_shape) :- !,
    (   rel_pe_append_suffix_let_extension(PrefixElems, Observed, TailVar, RawBody, Result)
    ->  (   contains_symbol('decons-atom', Result),
            contains_symbol('first-from-pair', Result),
            contains_symbol('second-from-pair', Result),
            contains_symbol('__tr-raw-apply1', Result),
            \+ contains_symbol(case, Result)
        ->  format("  ✓ ~w: ~w~n", [N, Name])
        ;   format("  ✗ ~w: ~w~n    Got: ~w~n", [N, Name, Result])
        )
    ;   format("  ? ~w: ~w (relational translation error)~n", [N, Name])
    ).

run_one_rel_pe(N, Name, Input, Expected) :-
    (   rel_pe_translate_term(Input, Result),
        Result == Expected
    ->  format("  ✓ ~w: ~w~n", [N, Name])
    ;   format("  ✗ ~w: ~w~n    Expected: ~w~n",
               [N, Name, Expected])
    ).
