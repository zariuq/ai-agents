%% HE → PeTTa Translator (Prolog module)
%% Called from PeTTa via import_prolog_functions_from_file
%%
%% Prolog is purpose-built for structural term manipulation.
%% This does what MeTTa's unification-based matching cannot:
%% faithful syntactic rewriting without variable expansion.

:- module(he_to_petta,
          [ translate_term/2,
            translate_term_trusted/2,
            translate_decl/2,
            translate_decl_trusted/2,
            translate_program/2,
            translate_program_trusted/2,
            obsolete_bool_and_rule/1,
            should_drop_obsolete_bool_and_rule/1
          ]).

%% ── Core rewrite rules ──────────────────────────────────────────
%%
%% Modes:
%%   pure    - preserve the shared/common surface
%%   trusted - allow trusted HE→PeTTa lowerings for known PeTTa seams

translate_term(Term, Out) :-
    translate_term_mode(pure, Term, Out).

translate_term_trusted(Term, Out) :-
    translate_term_mode(trusted, Term, Out).

translate_decl(Decl, Out) :-
    translate_decl_mode(pure, Decl, Out).

translate_decl_trusted(Decl, Out) :-
    translate_decl_mode(trusted, Decl, Out).

translate_program(Program, Out) :-
    translate_program_mode(pure, Program, Out).

translate_program_trusted(Program, Out) :-
    translate_program_mode(trusted, Program, Out).

trusted_new_space_prefix('&__tr_space_').

fresh_var(Prefix, Var) :-
    (   predicate_property(petta_to_he:fresh_var(_,_), defined)
    ->  petta_to_he:fresh_var(Prefix, Var)
    ;   atomic_list_concat(['$__tr_', Prefix, '_0'], Var)
    ).

%% trusted change-state! return value bridge:
%% HE's change-state! returns (State val), PeTTa's returns true.
%% When the return value is bound (via chain), wrap to produce (State val)
%% explicitly after executing the side effect.
%% Council: Carneiro, Pfenning — handle dialect difference in the translator,
%% never modify PeTTa's core runtime.
%% MUST be before generic chain rule to take priority in trusted mode.
translate_term_mode(trusted, [chain, ['change-state!', Ref, Val], Var, Body],
                    TOut) :-
    translate_term_mode(trusted, Val, TVal),
    translate_term_mode(trusted, Body, TBody),
    fresh_var(discard, FV),
    TOut = [let, FV, ['change-state!', Ref, TVal],
            [let, Var, ['State', TVal], TBody]], !.

%% chain → let
translate_term_mode(Mode, [chain, Expr, Var, Body], [let, Var, TExpr, TBody]) :-
    translate_term_mode(Mode, Expr, TExpr),
    translate_term_mode(Mode, Body, TBody), !.

%% collapse-bind → collapse
translate_term_mode(Mode, ['collapse-bind', Inner], [collapse, TInner]) :-
    translate_term_mode(Mode, Inner, TInner), !.

%% superpose-bind → superpose
translate_term_mode(Mode, ['superpose-bind', Inner], [superpose, TInner]) :-
    translate_term_mode(Mode, Inner, TInner), !.

%% trusted new-space lowering:
%% PeTTa miscompiles `let $s (new-space) ...` in compiled function bodies.
%% In trusted mode, lower to a Prolog gensym call that PeTTa compiles reliably.
translate_term_mode(trusted, ['new-space'], [call, [gensym, Prefix]]) :-
    trusted_new_space_prefix(Prefix), !.

%% HE stdlib `unique` is generic: collapse the stream, deduplicate the resulting
%% list, then re-emit it as a stream. PeTTa only hardcodes the direct
%% `unique(superpose ...)` case, so the translator lowers the generic HE form.
translate_term_mode(Mode, [unique, Arg], TOut) :-
    translate_term_mode(Mode, Arg, TArg),
    fresh_var(collapsed, ListVar),
    fresh_var(unique, UniqueVar),
    TOut = [let, ListVar, [collapse, TArg],
            [let, UniqueVar, ['unique-atom', ListVar],
             [superpose, UniqueVar]]], !.

%% HE-style conjunction of recursive deductions needs explicit binding flow in PeTTa.
%% This preserves shared-variable scoping across the two deduction branches.
translate_term_mode(Mode, ['And', ['deduce', A], ['deduce', B]],
               ['let*', [['T', TLeft], ['T', TRight]], 'T']) :-
    translate_term_mode(Mode, ['deduce', A], TLeft),
    translate_term_mode(Mode, ['deduce', B], TRight), !.

%% switch → case
translate_term_mode(Mode, [switch, Scrut, Branches], [case, TScrut, TBranches]) :-
    translate_term_mode(Mode, Scrut, TScrut),
    translate_term_mode(Mode, Branches, TBranches), !.

%% switch-minimal → case
translate_term_mode(Mode, ['switch-minimal', Scrut, Branches], [case, TScrut, TBranches]) :-
    translate_term_mode(Mode, Scrut, TScrut),
    translate_term_mode(Mode, Branches, TBranches), !.

%% atom-subst → let
translate_term_mode(Mode, ['atom-subst', Atom, Var, Tmpl], [let, Var, TAtom, TTmpl]) :-
    translate_term_mode(Mode, Atom, TAtom),
    translate_term_mode(Mode, Tmpl, TTmpl), !.

%% nop → (let $fresh_ X ())
%% Fresh variable to avoid capture (council: Carneiro, Wadler)
translate_term_mode(Mode, [nop, X], [let, FV, TX, '()']) :-
    fresh_var(discard, FV),
    translate_term_mode(Mode, X, TX), !.

%% function/return unwrap
translate_term_mode(Mode, [function, [return, X]], TX) :-
    translate_term_mode(Mode, X, TX), !.

%% ── Recursive traversal (shared constructs) ─────────────────────

translate_term_mode(Mode, List, TList) :-
    is_list(List),
    maplist(translate_term_mode(Mode), List, TList), !.

translate_term_mode(_, X, X) :-
    \+ is_list(X).

%% ── Program-level translation ───────────────────────────────────

translate_decl_mode(Mode, ['=', LHS, RHS], ['=', LHS, TRHS]) :-
    translate_term_mode(Mode, RHS, TRHS), !.

translate_decl_mode(_, [':', Name, Type], [':', Name, Type]) :- !.

translate_decl_mode(Mode, X, TX) :-
    translate_term_mode(Mode, X, TX).

translate_program_mode(Mode, Decls, TDecls) :-
    translate_program_acc(Mode, Decls, TDecls0),
    (   should_drop_obsolete_bool_and_rule(Decls)
    ->  exclude(obsolete_bool_and_rule, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

translate_program_acc(_, [], []).
translate_program_acc(Mode, [Decl|Rest], [TDecl|TRest]) :-
    translate_decl_mode(Mode, Decl, TDecl),
    translate_program_acc(Mode, Rest, TRest).

deduce_and_kernel_rule(
    ['=', ['deduce', ['And', A, B]], ['And', ['deduce', A], ['deduce', B]]]).

obsolete_bool_and_rule(['=', ['And', 'T', 'T'], 'T']).

should_drop_obsolete_bool_and_rule(Atoms) :-
    contains_deduce_and_kernel_rule(Atoms),
    contains_obsolete_bool_and_rule(Atoms),
    \+ contains_live_rhs_or_query_and(Atoms).

contains_deduce_and_kernel_rule(['!', _ | Rest]) :-
    contains_deduce_and_kernel_rule(Rest).
contains_deduce_and_kernel_rule([Atom | Rest]) :-
    (   deduce_and_kernel_rule(Atom)
    ;   contains_deduce_and_kernel_rule(Rest)
    ).
contains_deduce_and_kernel_rule([]) :-
    fail.

contains_obsolete_bool_and_rule(['!', _ | Rest]) :-
    contains_obsolete_bool_and_rule(Rest).
contains_obsolete_bool_and_rule([Atom | Rest]) :-
    (   obsolete_bool_and_rule(Atom)
    ;   contains_obsolete_bool_and_rule(Rest)
    ).
contains_obsolete_bool_and_rule([]) :-
    fail.

contains_live_rhs_or_query_and(['!', Expr | _]) :-
    contains_and_term(Expr), !.
contains_live_rhs_or_query_and(['!', _ | Rest]) :-
    contains_live_rhs_or_query_and(Rest).
contains_live_rhs_or_query_and([Atom | _]) :-
    atom_has_live_rhs_and(Atom), !.
contains_live_rhs_or_query_and([_ | Rest]) :-
    contains_live_rhs_or_query_and(Rest).
contains_live_rhs_or_query_and([]) :-
    fail.

atom_has_live_rhs_and(Atom) :-
    deduce_and_kernel_rule(Atom), !, fail.
atom_has_live_rhs_and(Atom) :-
    obsolete_bool_and_rule(Atom), !, fail.
atom_has_live_rhs_and(['=', _, RHS]) :-
    contains_and_term(RHS), !.
atom_has_live_rhs_and(_) :-
    fail.

contains_and_term(['And', _, _]) :- !.
contains_and_term(List) :-
    is_list(List),
    member(Subterm, List),
    contains_and_term(Subterm), !.
