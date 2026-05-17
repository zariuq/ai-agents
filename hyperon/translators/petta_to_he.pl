%% PeTTa → HE Translator (Prolog module)
%%
%% Faithful syntactic rewriting of PeTTa-specific constructs to HE form.

:- module(petta_to_he,
          [ translate_term/2,
            translate_term_hyperpose/2,
            translate_term_extended/2,
            translate_term_extended_hyperpose/2,
            translate_term_trusted/2,
            translate_term_trusted_extended/2,
            translate_decl/2,
            translate_decl_hyperpose/2,
            translate_decl_extended/2,
            translate_decl_extended_hyperpose/2,
            translate_decl_trusted/2,
            translate_decl_trusted_extended/2,
            translate_program/2,
            translate_program_hyperpose/2,
            translate_program_extended/2,
            translate_program_extended_hyperpose/2,
            translate_program_trusted/2,
            translate_program_trusted_extended/2,
            optimize_term/2,
            optimize_decl/2,
            optimize_program/2
          ]).

%% ── Fresh variable generation (capture-avoiding) ────────────────
%% Hardcoded $_ and $__r cause variable capture when source terms contain
%% those names. Use gensym-based fresh names instead.

:- dynamic tr_counter/1.
tr_counter(0).

fresh_var(Prefix, Var) :-
    retract(tr_counter(N)),
    N1 is N + 1,
    assert(tr_counter(N1)),
    atomic_list_concat(['$__tr_', Prefix, '_', N1], Var).

%% Quoted PeTTa syntax must be translated as code, but remain data.
%%
%% This helper rewrites source syntax into target HE syntax without executing
%% it, so later eval/unquote on the translated file sees the right target
%% code rather than the original PeTTa-specific surface forms.
translate_quoted_term_mode(Mode, [quote, Expr], ['quoted-syntax', [quote, TExpr]]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [eval, Expr], [unquote, [quote, TExpr]]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [reduce, Expr], [unquote, [quote, TExpr]]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [length, [collapse, Expr]],
                           [let, TupleVar, [collapse, TExpr], [size-atom, TupleVar]]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr),
    fresh_var(tuple, TupleVar), !.
translate_quoted_term_mode(Mode, [length, Expr], [length, TExpr]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [test, Actual, Expected],
                           [test, TActual, TExpected]) :-
    translate_quoted_term_mode(Mode, Actual, TActual),
    translate_quoted_term_mode(Mode, Expected, TExpected), !.
translate_quoted_term_mode(Mode, [hyperpose, Exprs], [hyperpose, TExprs]) :-
    preserve_hyperpose_mode(Mode),
    translate_quoted_term_mode(Mode, Exprs, TExprs), !.
translate_quoted_term_mode(Mode, [hyperpose, Exprs], [superpose, TExprs]) :-
    translate_quoted_term_mode(Mode, Exprs, TExprs), !.
translate_quoted_term_mode(Mode, ['@<', A, B], ['<s', TA, TB]) :-
    translate_quoted_term_mode(Mode, A, TA),
    translate_quoted_term_mode(Mode, B, TB), !.
translate_quoted_term_mode(Mode, ['@>', A, B], [not, ['<s', TA, TB]]) :-
    translate_quoted_term_mode(Mode, A, TA),
    translate_quoted_term_mode(Mode, B, TB), !.
translate_quoted_term_mode(Mode, List, TList) :-
    is_list(List),
    maplist(translate_quoted_term_mode(Mode), List, TList), !.
translate_quoted_term_mode(_, X, X).

%% ── Core rewrite rules ──────────────────────────────────────────
%%
%% Modes:
%%   pure             - conservative HE surface (default)
%%   hyperpose        - pure + preserve hyperpose for HE runtimes that support it
%%   extended         - may emit HE-extended heads (e.g. collect)
%%   extended_hyperpose - extended + preserve hyperpose
%%   trusted          - pure + trusted bridge reversals (e.g. new-space gensym)
%%   trusted_extended - trusted + extended
%%
%% Keeping pure as the default preserves the verified/portable path.

translate_term(Term, Out) :-
    translate_term_mode(pure, Term, Out).

translate_term_hyperpose(Term, Out) :-
    translate_term_mode(hyperpose, Term, Out).

translate_term_extended(Term, Out) :-
    translate_term_mode(extended, Term, Out).

translate_term_extended_hyperpose(Term, Out) :-
    translate_term_mode(extended_hyperpose, Term, Out).

translate_term_trusted(Term, Out) :-
    translate_term_mode(trusted, Term, Out).

translate_term_trusted_extended(Term, Out) :-
    translate_term_mode(trusted_extended, Term, Out).

translate_decl(Decl, Out) :-
    translate_decl_mode(pure, Decl, Out).

translate_decl_hyperpose(Decl, Out) :-
    translate_decl_mode(hyperpose, Decl, Out).

translate_decl_extended(Decl, Out) :-
    translate_decl_mode(extended, Decl, Out).

translate_decl_extended_hyperpose(Decl, Out) :-
    translate_decl_mode(extended_hyperpose, Decl, Out).

translate_decl_trusted(Decl, Out) :-
    translate_decl_mode(trusted, Decl, Out).

translate_decl_trusted_extended(Decl, Out) :-
    translate_decl_mode(trusted_extended, Decl, Out).

translate_program(Program, Out) :-
    translate_program_mode(pure, Program, Out).

translate_program_hyperpose(Program, Out) :-
    translate_program_mode(hyperpose, Program, Out).

translate_program_extended(Program, Out) :-
    translate_program_mode(extended, Program, Out).

translate_program_extended_hyperpose(Program, Out) :-
    translate_program_mode(extended_hyperpose, Program, Out).

translate_program_trusted(Program, Out) :-
    translate_program_mode(trusted, Program, Out).

translate_program_trusted_extended(Program, Out) :-
    translate_program_mode(trusted_extended, Program, Out).

trusted_new_space_prefix('&__tr_space_').

%% progn / prog1 are variadic in PeTTa.
%% progn []     → ()
%% progn [x]    → x'
%% progn [x..z] → let $d x' (let $d y' ... z')
translate_term_mode(Mode, [progn|Args], TExpr) :-
    translate_progn_args(Mode, Args, TExpr), !.

%% prog1 []     → ()
%% prog1 [x]    → x'
%% prog1 [x..z] → let $r x' (let $d y' ... $r)
translate_term_mode(Mode, [prog1|Args], TExpr) :-
    translate_prog1_args(Mode, Args, TExpr), !.

%% PeTTa quote Expr
%%   → quoted-syntax (quote Expr')
%%
%% PeTTa quote yields the syntax tree of the translated expression, not HE's
%% quoted wrapper value. quoted-syntax is a file-local compatibility helper
%% for the PeTTa HE target.
translate_term_mode(Mode, [quote, Expr], ['quoted-syntax', [quote, TExpr]]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr), !.

%% PeTTa eval Expr
%%   → unquote (quote Expr')
%%
%% Source eval executes syntax-as-data. In HE target code, unquote(quote ...)
%% matches that surface more closely than direct HE eval, which preserves
%% quoted wrappers on irreducible expressions.
translate_term_mode(Mode, [eval, Expr], [unquote, [quote, TExpr]]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr), !.

%% foldall Agg Goal Init
%%   pure mode:
%%     → let $list (collapse Goal')
%%         (foldl-atom $list Init' $acc $item (eval (Agg' $acc $item)))
%%
%%   extended mode:
%%     → let $list (collect Goal')
%%         (foldl-atom $list Init' $acc $item (eval (Agg' $acc $item)))
%%
%% This matches the public HE/CeTTa fold surface and preserves the benchmark
%% cases that aggregate over all generator results with a first-order reducer.
translate_term_mode(Mode, [foldall, Agg, Goal, Init],
               [let, ListVar, [CollectorHead, TGoal],
                ['foldl-atom', ListVar, TInit, AccVar, ItemVar,
                 [eval, [TAgg, AccVar, ItemVar]]]]) :-
    foldall_collector_head(Mode, CollectorHead),
    translate_term_mode(Mode, Agg, TAgg),
    translate_term_mode(Mode, Goal, TGoal),
    translate_term_mode(Mode, Init, TInit),
    fresh_var(collapsed, ListVar),
    fresh_var(acc, AccVar),
    fresh_var(item, ItemVar), !.

%% PeTTa short-form foldl-atom List Init Agg
%%   → foldl-atom List' Init' $acc $item (eval (Agg' $acc $item))
%%
%% This is a PeTTa surface convenience. HE/CeTTa only exposes the binder form,
%% so the translator must lower the reducer position explicitly.
translate_term_mode(Mode, ['foldl-atom', List, Init, Agg],
               ['foldl-atom', TList, TInit, AccVar, ItemVar,
                [eval, [TAgg, AccVar, ItemVar]]]) :-
    translate_term_mode(Mode, List, TList),
    translate_term_mode(Mode, Init, TInit),
    translate_term_mode(Mode, Agg, TAgg),
    fresh_var(acc, AccVar),
    fresh_var(item, ItemVar), !.

%% PeTTa raw reduce Expr
%%   → unquote (quote Expr')
%%
%% PeTTa's one-argument reduce dispatches syntax-as-data with source semantics.
%% Lower it through unquote(quote ...) so irreducible expressions become raw
%% data instead of HE quote wrappers.
translate_term_mode(Mode, [reduce, Expr], [unquote, [quote, TExpr]]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr), !.

%% PeTTa length(collapse Expr)
%%   → let $tuple (collapse Expr') (size-atom $tuple)
%%
%% This is the critical high-volume PeTTa pattern. Lower it directly to the
%% CeTTa shape that counts collapsed result tuples without relying on a generic
%% user-level wrapper around eval, which is fragile on very large tuples.
translate_term_mode(Mode, [length, [collapse, Expr]],
               [let, TupleVar, [collapse, TExpr], [size-atom, TupleVar]]) :-
    translate_term_mode(Mode, Expr, TExpr),
    fresh_var(tuple, TupleVar), !.

%% PeTTa length Expr
%%   → length Expr'
%%
%% Keep the source head intact for the remaining non-collapse cases and provide
%% a tiny compatibility definition at the file/program level when needed.
translate_term_mode(Mode, [length, Expr], [length, TExpr]) :-
    translate_term_mode(Mode, Expr, TExpr), !.

%% PeTTa test Actual Expected
%%   → test Actual' Expected'
%%
%% Keep the surface head intact and prepend one file-local definition only when
%% the source relied on the builtin PeTTa test. This keeps the actual
%% expression in ordinary call position instead of rebuilding evaluation from a
%% quoted helper argument later.
translate_term_mode(Mode, [test, Actual, Expected],
               [test, TActual, TExpected]) :-
    translate_term_mode(Mode, Actual, TActual),
    translate_term_mode(Mode, Expected, TExpected), !.

%% trusted HE→PeTTa new-space lowering reversal
translate_term_mode(Mode, [call, [gensym, Prefix]], ['new-space']) :-
    trusted_mode(Mode),
    trusted_new_space_prefix(Prefix), !.

%% PeTTa compatibility idiom: unique-atom(collapse X) computes a deduplicated
%% list, so raise it to the list-preserving HE surface collapse(unique X).
translate_term_mode(Mode, ['unique-atom', [collapse, Arg]], [collapse, [unique, TArg]]) :-
    translate_term_mode(Mode, Arg, TArg), !.

%% PeTTa hyperpose Exprs
%%   preserve mode:   → hyperpose Exprs'
%%   default/pure:    → superpose Exprs'
%%
%% Pure HE lacks a dedicated hyperpose surface. Default translation lowers
%% parallel choice to ordinary nondeterministic choice instead of rejecting the
%% program. This intentionally accepts engine-dependent differences in timing,
%% fairness, and once-selection behavior.
translate_term_mode(Mode, [hyperpose, Exprs], [hyperpose, TExprs]) :-
    preserve_hyperpose_mode(Mode),
    translate_term_mode(Mode, Exprs, TExprs), !.
translate_term_mode(Mode, [hyperpose, Exprs], [superpose, TExprs]) :-
    translate_term_mode(Mode, Exprs, TExprs), !.

%% @< → <s
translate_term_mode(Mode, ['@<', A, B], ['<s', TA, TB]) :-
    translate_term_mode(Mode, A, TA),
    translate_term_mode(Mode, B, TB), !.

%% @> → (not (<s A B))
translate_term_mode(Mode, ['@>', A, B], [not, ['<s', TA, TB]]) :-
    translate_term_mode(Mode, A, TA),
    translate_term_mode(Mode, B, TB), !.

%% ── Recursive traversal ─────────────────────────────────────────

%% Lists: translate each element
translate_term_mode(Mode, List, TList) :-
    is_list(List),
    maplist(translate_term_mode(Mode), List, TList), !.

%% Atoms: identity
translate_term_mode(_, X, X) :- \+ is_list(X).

%% ── Program-level translation ───────────────────────────────────

translate_decl_mode(Mode, ['=', LHS, RHS], ['=', LHS, TRHS]) :-
    translate_term_mode(Mode, RHS, TRHS), !.

translate_decl_mode(_, [':', Name, Type], [':', Name, Type]) :- !.

translate_decl_mode(_, X, X).

translate_program_mode(Mode, Decls, Program) :-
    maplist(translate_decl_mode(Mode), Decls, TDecls0),
    prepend_petta_compat_program_decls(Decls, TDecls0, Program).

%% ── Post-translation HE optimization ───────────────────────────
%%
%% Keep this as a separate pass instead of changing the core lowering rules.
%% Optimize only translator-generated administrative lets that are easy to
%% validate. Keep foldall's let(collapse ...) shape intact because
%% chain(collapse ...) is not a stable common path in current HE.

optimize_term([let, Var, Expr, Body], OptTerm) :-
    optimize_term(Expr, TExpr),
    optimize_term(Body, TBody),
    optimize_translator_let(Var, TExpr, TBody, OptTerm), !.
optimize_term(List, TList) :-
    is_list(List),
    maplist(optimize_term, List, TList), !.
optimize_term(X, X) :-
    \+ is_list(X).

optimize_decl(['=', LHS, RHS], ['=', LHS, TRHS]) :-
    optimize_term(RHS, TRHS), !.
optimize_decl([':', Name, Type], [':', Name, Type]) :- !.
optimize_decl(X, TX) :-
    optimize_term(X, TX).

optimize_program([], []).
optimize_program([D|Ds], [TD|TDs]) :-
    optimize_decl(D, TD),
    optimize_program(Ds, TDs).

optimize_translator_let(Var, Expr, '()', [nop, Expr]) :-
    translator_discard_var(Var), !.
optimize_translator_let(Var, Expr, Body, [chain, Expr, Var, Body]) :-
    translator_discard_var(Var),
    \+ contains_symbol(Var, Body),
    safe_chain_source(Expr), !.
optimize_translator_let(Var, Expr, Body, Expr) :-
    translator_result_var(Var),
    Body == Var,
    \+ contains_symbol(Var, Expr), !.
optimize_translator_let(Var, Expr, Body, [let, Var, Expr, Body]).

translator_generated_var(Var) :-
    atom(Var),
    sub_atom(Var, 0, _, _, '$__tr_').

translator_discard_var(Var) :-
    translator_generated_var(Var),
    sub_atom(Var, 0, _, _, '$__tr_discard_').

translator_result_var(Var) :-
    translator_generated_var(Var),
    sub_atom(Var, 0, _, _, '$__tr_result_').

safe_chain_source(Expr) :-
    \+ contains_head_symbol(collapse, Expr),
    \+ contains_head_symbol('collapse-bind', Expr).

contains_symbol(Sym, Term) :-
    Term == Sym.
contains_symbol(Sym, Term) :-
    is_list(Term),
    member(Subterm, Term),
    contains_symbol(Sym, Subterm).

contains_head_symbol(Sym, [Sym | _]).
contains_head_symbol(Sym, Term) :-
    is_list(Term),
    member(Subterm, Term),
    contains_head_symbol(Sym, Subterm).

translate_progn_args(_, [], '()').
translate_progn_args(Mode, [Last], TLast) :-
    translate_term_mode(Mode, Last, TLast).
translate_progn_args(Mode, [Expr|Rest], [let, FreshV, TExpr, TRest]) :-
    fresh_var(discard, FreshV),
    translate_term_mode(Mode, Expr, TExpr),
    translate_progn_args(Mode, Rest, TRest).

translate_prog1_args(_, [], '()').
translate_prog1_args(Mode, [First], TFirst) :-
    translate_term_mode(Mode, First, TFirst).
translate_prog1_args(Mode, [First|Rest], [let, FreshR, TFirst, TRest]) :-
    fresh_var(result, FreshR),
    translate_term_mode(Mode, First, TFirst),
    translate_prog1_rest(Mode, Rest, FreshR, TRest).

translate_prog1_rest(_, [], ResultVar, ResultVar).
translate_prog1_rest(Mode, [Expr|Rest], ResultVar, [let, FreshD, TExpr, TRest]) :-
    fresh_var(discard, FreshD),
    translate_term_mode(Mode, Expr, TExpr),
    translate_prog1_rest(Mode, Rest, ResultVar, TRest).

foldall_collector_head(pure, collapse).
foldall_collector_head(hyperpose, collapse).
foldall_collector_head(extended, collect).
foldall_collector_head(extended_hyperpose, collect).
foldall_collector_head(trusted, collapse).
foldall_collector_head(trusted_extended, collect).

preserve_hyperpose_mode(hyperpose).
preserve_hyperpose_mode(extended_hyperpose).

trusted_mode(trusted).
trusted_mode(trusted_extended).

prepend_petta_compat_program_decls(SourceDecls, TDecls0, TDecls) :-
    maybe_rewrite_builtin_test_calls(SourceDecls, TDecls0, TDecls1),
    maybe_prepend_quote_compat_decls(TDecls1, TDecls2),
    maybe_prepend_length_compat_decls(SourceDecls, TDecls2, TDecls3),
    TDecls = TDecls3.

maybe_prepend_quote_compat_decls(TDecls0, TDecls) :-
    (   program_uses_quoted_syntax(TDecls0),
        \+ program_defines_quoted_syntax(TDecls0)
    ->  petta_quote_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_length_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_length(SourceDecls),
        \+ program_defines_length(SourceDecls)
    ->  petta_length_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_rewrite_builtin_test_calls(SourceDecls, TDecls0, TDecls) :-
    (   program_defines_test(SourceDecls)
    ->  TDecls = TDecls0
    ;   maplist(rewrite_builtin_test_decl, TDecls0, TDecls)
    ).

program_uses_length(Term) :-
    is_list(Term),
    (   Term = [length, _]
    ;   member(Subterm, Term),
        program_uses_length(Subterm)
    ).

program_uses_length(_) :-
    fail.

program_uses_quoted_syntax(Term) :-
    is_list(Term),
    (   Term = ['quoted-syntax'|_]
    ;   member(Subterm, Term),
        program_uses_quoted_syntax(Subterm)
    ).

program_uses_quoted_syntax(_) :-
    fail.

program_uses_test(Term) :-
    is_list(Term),
    (   Term = [test, _, _]
    ;   member(Subterm, Term),
        program_uses_test(Subterm)
    ).

program_uses_test(_) :-
    fail.

program_defines_length([['=', [length|_], _]|_]) :- !.
program_defines_length([_|Rest]) :-
    program_defines_length(Rest).

program_defines_quoted_syntax([['=', ['quoted-syntax'|_], _]|_]) :- !.
program_defines_quoted_syntax([_|Rest]) :-
    program_defines_quoted_syntax(Rest).

program_defines_test([['=', [test|_], _]|_]) :- !.
program_defines_test([_|Rest]) :-
    program_defines_test(Rest).

petta_length_compat_decls([
    ['=', [length, '$expr'],
     [let, '$tuple', [eval, '$expr'], [size-atom, '$tuple']]]
]).

petta_quote_compat_decls([
    ['=', ['quoted-syntax', [quote, '$expr']], '$expr']
]).

rewrite_builtin_test_decl(['=', LHS, RHS], ['=', RLHS, RRHS]) :-
    !,
    rewrite_builtin_test_term(LHS, RLHS),
    rewrite_builtin_test_term(RHS, RRHS).
rewrite_builtin_test_decl(Term, Rewritten) :-
    rewrite_builtin_test_term(Term, Rewritten).

rewrite_builtin_test_term([test, Actual, Expected],
                          [assertEqualToEval, RActual, RExpected]) :-
    !,
    rewrite_builtin_test_term(Actual, RActual),
    rewrite_builtin_test_term(Expected, RExpected).
rewrite_builtin_test_term(List, Rewritten) :-
    is_list(List), !,
    maplist(rewrite_builtin_test_term, List, Rewritten).
rewrite_builtin_test_term(Term, Term).
