%% PeTTa → HE Translator (Prolog module)
%%
%% Faithful syntactic rewriting of PeTTa-specific constructs to HE form.

:- module(petta_to_he,
          [ translate_term/2,
            translate_term_extended/2,
            translate_term_trusted/2,
            translate_term_trusted_extended/2,
            translate_decl/2,
            translate_decl_extended/2,
            translate_decl_trusted/2,
            translate_decl_trusted_extended/2,
            translate_program/2,
            translate_program_extended/2,
            translate_program_trusted/2,
            translate_program_trusted_extended/2,
            optimize_term/2,
            optimize_decl/2,
            optimize_program/2
          ]).

%% ── Fresh variable generation (capture-avoiding) ────────────────
%% Council (Carneiro, Wadler, Pfenning): hardcoded $_ and $__r
%% cause variable capture when source terms contain those names.
%% Use gensym-based fresh names instead.

:- dynamic tr_counter/1.
tr_counter(0).

fresh_var(Prefix, Var) :-
    retract(tr_counter(N)),
    N1 is N + 1,
    assert(tr_counter(N1)),
    atomic_list_concat(['$__tr_', Prefix, '_', N1], Var).

%% ── Core rewrite rules ──────────────────────────────────────────
%%
%% Modes:
%%   pure             - conservative HE surface (default)
%%   extended         - may emit HE-extended heads (e.g. collect)
%%   trusted          - pure + trusted bridge reversals (e.g. new-space gensym)
%%   trusted_extended - trusted + extended
%%
%% Keeping pure as the default preserves the verified/portable path.

translate_term(Term, Out) :-
    translate_term_mode(pure, Term, Out).

translate_term_extended(Term, Out) :-
    translate_term_mode(extended, Term, Out).

translate_term_trusted(Term, Out) :-
    translate_term_mode(trusted, Term, Out).

translate_term_trusted_extended(Term, Out) :-
    translate_term_mode(trusted_extended, Term, Out).

translate_decl(Decl, Out) :-
    translate_decl_mode(pure, Decl, Out).

translate_decl_extended(Decl, Out) :-
    translate_decl_mode(extended, Decl, Out).

translate_decl_trusted(Decl, Out) :-
    translate_decl_mode(trusted, Decl, Out).

translate_decl_trusted_extended(Decl, Out) :-
    translate_decl_mode(trusted_extended, Decl, Out).

translate_program(Program, Out) :-
    translate_program_mode(pure, Program, Out).

translate_program_extended(Program, Out) :-
    translate_program_mode(extended, Program, Out).

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

%% trusted HE→PeTTa new-space lowering reversal
translate_term_mode(Mode, [call, [gensym, Prefix]], ['new-space']) :-
    trusted_mode(Mode),
    trusted_new_space_prefix(Prefix), !.

%% PeTTa compatibility idiom: unique-atom(collapse X) computes a deduplicated
%% list, so raise it to the list-preserving HE surface collapse(unique X).
translate_term_mode(Mode, ['unique-atom', [collapse, Arg]], [collapse, [unique, TArg]]) :-
    translate_term_mode(Mode, Arg, TArg), !.

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

translate_program_mode(_, [], []).
translate_program_mode(Mode, [D|Ds], [TD|TDs]) :-
    translate_decl_mode(Mode, D, TD),
    translate_program_mode(Mode, Ds, TDs).

%% ── Post-translation HE optimization ───────────────────────────
%%
%% Keep this as a separate pass instead of changing the core lowering rules.
%% The council direction here is to optimize only translator-generated
%% administrative lets that are easy to validate and keep foldall's
%% let(collapse ...) shape intact because chain(collapse ...) is not a stable
%% common path in current HE.

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
foldall_collector_head(extended, collect).
foldall_collector_head(trusted, collapse).
foldall_collector_head(trusted_extended, collect).

trusted_mode(trusted).
trusted_mode(trusted_extended).
