%% HE → PeTTa Translator (Prolog module)
%% Called from PeTTa via import_prolog_functions_from_file
%%
%% Prolog is purpose-built for structural term manipulation.
%% This does what MeTTa's unification-based matching cannot:
%% faithful syntactic rewriting without variable expansion.

:- module(he_to_petta,
          [ translate_term/2,
            translate_term_with_defined_funs/3,
            translate_term_with_fun_context/4,
            translate_term_trusted/2,
            translate_term_trusted_with_defined_funs/3,
            translate_term_trusted_with_fun_context/4,
            translate_decl/2,
            translate_decl_trusted/2,
            translate_program/2,
            translate_program_trusted/2,
            obsolete_bool_and_rule/1,
            should_drop_obsolete_bool_and_rule/1,
            rename_native_reserved_heads/2
          ]).

%% ── Core rewrite rules ──────────────────────────────────────────
%%
%% Modes:
%%   pure    - preserve the shared/common surface
%%   trusted - allow trusted HE→PeTTa lowerings for known PeTTa seams

translate_term(Term, Out) :-
    translate_term_mode(pure, Term, Out).

translate_term_with_defined_funs(Funs, Term, Out) :-
    with_source_defined_funs(Funs, translate_term_mode(pure, Term, Out)).

translate_term_with_fun_context(ActiveFuns, FutureFuns, Term, Out) :-
    with_source_defined_fun_context(ActiveFuns, FutureFuns,
        translate_term_mode(pure, Term, Out)).

translate_term_trusted(Term, Out) :-
    translate_term_mode(trusted, Term, Out).

translate_term_trusted_with_defined_funs(Funs, Term, Out) :-
    with_source_defined_funs(Funs, translate_term_mode(trusted, Term, Out)).

translate_term_trusted_with_fun_context(ActiveFuns, FutureFuns, Term, Out) :-
    with_source_defined_fun_context(ActiveFuns, FutureFuns,
        translate_term_mode(trusted, Term, Out)).

translate_decl(Decl, Out) :-
    translate_decl_mode(pure, Decl, Out).

translate_decl_trusted(Decl, Out) :-
    translate_decl_mode(trusted, Decl, Out).

translate_program(Program, Out) :-
    translate_program_mode(pure, Program, Out).

translate_program_trusted(Program, Out) :-
    translate_program_mode(trusted, Program, Out).

trusted_new_space_prefix('&__tr_space_').

with_source_defined_funs(Funs, Goal) :-
    with_source_defined_fun_context(Funs, [], Goal).

with_source_defined_fun_context(ActiveFuns, FutureFuns, Goal) :-
    (   catch(nb_getval(he2petta_source_defined_funs, OldFuns), _, fail)
    ->  Saved = saved(OldFuns)
    ;   Saved = none
    ),
    (   catch(nb_getval(he2petta_future_defined_funs, OldFutureFuns), _, fail)
    ->  SavedFuture = saved(OldFutureFuns)
    ;   SavedFuture = none
    ),
    setup_call_cleanup(
        ( nb_setval(he2petta_source_defined_funs, ActiveFuns),
          nb_setval(he2petta_future_defined_funs, FutureFuns)
        ),
        Goal,
        ( restore_source_defined_funs(Saved),
          restore_future_defined_funs(SavedFuture)
        )
    ).

restore_source_defined_funs(saved(Funs)) :-
    nb_setval(he2petta_source_defined_funs, Funs).
restore_source_defined_funs(none) :-
    nb_setval(he2petta_source_defined_funs, []).

restore_future_defined_funs(saved(Funs)) :-
    nb_setval(he2petta_future_defined_funs, Funs).
restore_future_defined_funs(none) :-
    nb_setval(he2petta_future_defined_funs, []).

%% ── Hygienic renaming of natively reserved heads ────────────────
%%
%% HE sources may define functions whose names native PeTTa reserves as
%% static Prolog procedures (e.g. `is`); loading such an equation aborts the
%% whole file. These names are NOT shared MeTTa surfaces, so renaming the
%% symbol consistently across definitions and uses preserves the program's
%% meaning. Shared MeTTa surfaces (add-atom, match, +, eval, ...) are
%% deliberately NOT in this list: defining them means union semantics with
%% the builtin, which renaming would break.
petta_reserved_nonmetta_head(is).
petta_reserved_nonmetta_head(min).
petta_reserved_nonmetta_head(max).
petta_reserved_nonmetta_head(assert).
petta_reserved_nonmetta_head(call).
petta_reserved_nonmetta_head(length).
petta_reserved_nonmetta_head(append).
petta_reserved_nonmetta_head(member).
petta_reserved_nonmetta_head(sort).
petta_reserved_nonmetta_head(msort).
petta_reserved_nonmetta_head(last).
petta_reserved_nonmetta_head(reverse).
petta_reserved_nonmetta_head(foldl).
petta_reserved_nonmetta_head(maplist).
petta_reserved_nonmetta_head(first).
petta_reserved_nonmetta_head(concat).
petta_reserved_nonmetta_head(parse).
petta_reserved_nonmetta_head(test).
petta_reserved_nonmetta_head(size).
petta_reserved_nonmetta_head(id).
petta_reserved_nonmetta_head('=').
petta_reserved_nonmetta_head('first-from-pair').
petta_reserved_nonmetta_head('second-from-pair').
%% Dynamic native surfaces: redefinition does not abort, it silently UNIONS
%% with the builtin (each call answers twice — exponential fan-out under
%% recursion), so these rename as well. None is an upstream HE builtin.
petta_reserved_nonmetta_head('is-space').
petta_reserved_nonmetta_head('is-var').
petta_reserved_nonmetta_head('is-ground').
petta_reserved_nonmetta_head('is-expr').
petta_reserved_nonmetta_head('get-mettatype').
petta_reserved_nonmetta_head('is-member').
petta_reserved_nonmetta_head('is-alpha-member').
petta_reserved_nonmetta_head('exclude-item').
petta_reserved_nonmetta_head(repra).
petta_reserved_nonmetta_head(sread).
petta_reserved_nonmetta_head('mm2-exec').
petta_reserved_nonmetta_head(atom_concat).
petta_reserved_nonmetta_head(atom_chars).
petta_reserved_nonmetta_head(copy_term).
petta_reserved_nonmetta_head(term_hash).
petta_reserved_nonmetta_head(list_to_set).
petta_reserved_nonmetta_head(exists_file).
petta_reserved_nonmetta_head(library).

rename_native_reserved_heads(Atoms, Out) :-
    source_defined_symbols(Atoms, SourceSs),
    source_defined_typed_symbols(Atoms, SourceTypedSs),
    findall(H,
            ( member(Decl, Atoms),
              defined_head(Decl, H),
              atom(H),
              petta_reserved_nonmetta_head(H)
            ),
            Hs0),
    sort(Hs0, Hs),
    (   Hs == []
    ->  Out1 = Atoms
    ;   maplist(reserved_rename_pair, Hs, Map),
        deep_rename_program_atoms(Map, Atoms, Out1)
    ),
    record_source_defined_funs(Out1, SourceSs),
    record_source_defined_typed_funs(Out1, SourceTypedSs),
    source_defined_marker_facts(Markers),
    append(Out1, Markers, Out).

source_defined_symbols(Atoms, Ss) :-
    findall(S,
            ( member(Decl, Atoms),
              defined_head(Decl, H0),
              base_head_symbol(H0, S)
            ),
            Ss0),
    sort(Ss0, Ss).

source_defined_typed_symbols(Atoms, Ss) :-
    findall(S,
            ( member([':', H0, _], Atoms),
              base_head_symbol(H0, S)
            ),
            Ss0),
    sort(Ss0, Ss).

%% Applications of heads the source itself defines are wrapped with
%% call-or-inert (see lib_he), reproducing upstream's no-matching-equation
%% inertness. The runtime markers include both the translated callable heads
%% and the original source spellings so pre-definition reserved-head surfaces
%% stay inert instead of falling through to native builtins.
record_source_defined_funs(Atoms, ExtraSs0) :-
    source_defined_symbols(Atoms, AtomSs),
    append(AtomSs, ExtraSs0, Ss0),
    sort(Ss0, Ss),
    nb_setval(he2petta_source_defined_funs, Ss).

record_source_defined_typed_funs(Atoms, ExtraSs0) :-
    source_defined_typed_symbols(Atoms, AtomSs),
    append(AtomSs, ExtraSs0, Ss0),
    sort(Ss0, Ss),
    nb_setval(he2petta_source_defined_typed_funs, Ss).

%% Marker facts let the runtime dispatch helper distinguish a source-defined
%% head (no unifying equation => inert) from a grounded builtin (evaluate).
source_defined_marker_facts(Markers) :-
    (   catch(nb_getval(he2petta_source_defined_funs, Ss), _, fail)
    ->  findall(['source-defined-function', S], member(S, Ss), Markers0)
    ;   Markers0 = []
    ),
    (   catch(nb_getval(he2petta_source_defined_typed_funs, TypedSs), _, fail)
    ->  findall(['source-defined-typed-function', S], member(S, TypedSs), Markers1)
    ;   Markers1 = []
    ),
    append(Markers0, Markers1, Markers).

base_head_symbol(H, H) :- atom(H), !.
base_head_symbol([H0|_], S) :- base_head_symbol(H0, S).

he2petta_source_defined_fun(F) :-
    atom(F),
    catch(nb_getval(he2petta_source_defined_funs, Ss), _, fail),
    memberchk(F, Ss).

he2petta_future_source_defined_fun(F) :-
    atom(F),
    catch(nb_getval(he2petta_future_defined_funs, Ss), _, fail),
    memberchk(F, Ss).

defined_head(['=', [H|_], _], H).
defined_head([':', H, _], H).

reserved_rename_pair(H, H-H2) :-
    atom_concat(H, '-he', H2).

deep_rename_program_atoms(_, [], []).
deep_rename_program_atoms(Map, Atoms, Out) :-
    deep_rename_program_atoms(Map, [], Atoms, Out).

deep_rename_program_atoms(_, _, [], []).
deep_rename_program_atoms(Map, ActiveMap, ['!', Expr | Rest], ['!', TExpr | OutRest]) :-
    !,
    deep_rename_atoms(ActiveMap, Expr, TExpr),
    deep_rename_program_atoms(Map, ActiveMap, Rest, OutRest).
deep_rename_program_atoms(Map, ActiveMap0, [Atom | Rest], [TAtom | OutRest]) :-
    extend_active_rename_map(Map, ActiveMap0, Atom, ActiveMap),
    deep_rename_top_level_atom(ActiveMap, Atom, TAtom),
    deep_rename_program_atoms(Map, ActiveMap, Rest, OutRest).

extend_active_rename_map(Map, ActiveMap0, Atom, ActiveMap) :-
    (   defined_head(Atom, H),
        atom(H),
        memberchk(H-Renamed, Map)
    ->  (   memberchk(H-_, ActiveMap0)
        ->  ActiveMap = ActiveMap0
        ;   ActiveMap = [H-Renamed | ActiveMap0]
        )
    ;   ActiveMap = ActiveMap0
    ).

deep_rename_top_level_atom(Map, ['=', LHS, RHS], ['=', TLHS, TRHS]) :-
    !,
    deep_rename_atoms(Map, LHS, TLHS),
    deep_rename_atoms(Map, RHS, TRHS).
deep_rename_top_level_atom(Map, [':', Head, Type], [':', THead, TType]) :-
    !,
    deep_rename_atoms(Map, Head, THead),
    deep_rename_atoms(Map, Type, TType).
deep_rename_top_level_atom(Map, X, Y) :-
    deep_rename_atoms(Map, X, Y).

deep_rename_atoms(Map, X, Y) :-
    atom(X),
    memberchk(X-Y, Map), !.
deep_rename_atoms(Map, X, Y) :-
    is_list(X), !,
    maplist(deep_rename_atoms(Map), X, Y).
deep_rename_atoms(_, X, X).

fresh_var(Prefix, Var) :-
    (   predicate_property(petta_to_he:fresh_var(_,_), defined)
    ->  petta_to_he:fresh_var(Prefix, Var)
    ;   atomic_list_concat(['$__tr_', Prefix, '_0'], Var)
    ).

results_bag_equal_term(A, B,
                       [if, ['==', ['subtraction-atom', A, B], '()'],
                        ['==', ['subtraction-atom', B, A], '()'],
                        'False']).

assert_error_quoted(SrcExpr, Msg, [quote, ['Error', [quote, SrcExpr], Msg]]).

%% trusted change-state! return value bridge:
%% HE's change-state! returns (State val), PeTTa's returns true.
%% When the return value is bound (via chain), wrap to produce (State val)
%% explicitly after executing the side effect.
%% Handle the dialect difference in the translator rather than modifying
%% PeTTa's core runtime.
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

%% singleton-visible-witness → once
translate_term_mode(Mode, ['singleton-visible-witness', Inner], [once, TInner]) :-
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

%% HE-style conjunction of recursive deductions needs explicit binding flow in
%% PeTTa. Literal patterns in let* are unreliable in native PeTTa, so the
%% T-filter is expressed as bind-then-guard (no result when a branch fails).
translate_term_mode(Mode, ['And', ['deduce', A], ['deduce', B]], TOut) :-
    translate_term_mode(Mode, ['deduce', A], TLeft),
    translate_term_mode(Mode, ['deduce', B], TRight),
    fresh_var(left, V1),
    fresh_var(right, V2),
    TOut = [let, V1, TLeft,
            [if, ['==', V1, 'T'],
             [let, V2, TRight,
              [if, ['==', V2, 'T'], 'T', [empty]]],
             [empty]]], !.

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
%% Fresh variable to avoid capture.
translate_term_mode(Mode, [nop, X], [let, FV, TX, '()']) :-
    fresh_var(discard, FV),
    translate_term_mode(Mode, X, TX), !.

%% function/return unwrap
translate_term_mode(Mode, [function, [return, X]], TX) :-
    translate_term_mode(Mode, X, TX), !.

%% Upstream assertEqual compares the full result sets of both sides; PeTTa
%% evaluates arguments eagerly (fanning out per result), so lower to explicit
%% collapses of both sides compared as bags.
translate_term_mode(Mode, ['assertEqual', A, B],
                    ['assert-result-sets-equal', [collapse, TA], [collapse, TB]]) :-
    translate_term_mode(Mode, A, TA),
    translate_term_mode(Mode, B, TB), !.

translate_term_mode(Mode, ['assertAlphaEqual', A, B],
                    ['assert-alpha-result-sets-equal', [collapse, TA], [collapse, TB]]) :-
    translate_term_mode(Mode, A, TA),
    translate_term_mode(Mode, B, TB), !.

%% Upstream assertEqualToResult compares the bag of results of the actual
%% expression against a literal, unevaluated expected tuple. Lower it inline
%% so observational surfaces like (get-atoms &self) are not polluted by
%% helper equations becoming visible in &self before the assertion runs.
translate_term_mode(Mode, ['assertEqualToResult', E, X], TOut) :-
    translate_term_mode(Mode, E, TE),
    fresh_var(actual, ActualV),
    results_bag_equal_term(ActualV, [quote, X], Cond),
    assert_error_quoted(['assertEqualToResult', ActualV, [quote, X]],
                        '"assertEqualToResult failed"', ErrorQ),
    TOut = [let, ActualV, [collapse, TE],
            [if, Cond, '()', ErrorQ]], !.

translate_term_mode(Mode, ['assertAlphaEqualToResult', E, X],
                    ['assert-alpha-results-equal', [collapse, TE], [quote, X]]) :-
    translate_term_mode(Mode, E, TE), !.

%% Upstream Error is a constructor with unevaluated (Atom-typed) payloads;
%% native PeTTa would eagerly evaluate the subterms (re-running side effects
%% and double-wrapping errors), so syntactic Error expressions are
%% quote-protected (native PeTTa strips (quote X) to X unevaluated).
translate_term_mode(_Mode, ['Error'|Args], [quote, ['Error'|Args]]) :- !.

%% Extended assert surfaces; error payloads embed the ORIGINAL expressions
%% (quote-protected against native eager re-evaluation).
translate_term_mode(Mode, [assert, E],
                    ['assert-unit', [quote, [assert, E]], [quote, E], TE]) :-
    translate_term_mode(Mode, E, TE), !.

translate_term_mode(Mode, ['assertIncludes', E, T],
                    ['assert-includes', [quote, ['assertIncludes', E, T]],
                     [quote, T], [collapse, TE]]) :-
    translate_term_mode(Mode, E, TE), !.

translate_term_mode(Mode, ['assertEqualMsg', A, B, M],
                    ['assert-equal-msg', [quote, ['assertEqualMsg', A, B]],
                     [collapse, TA], [collapse, TB], M]) :-
    translate_term_mode(Mode, A, TA),
    translate_term_mode(Mode, B, TB), !.

translate_term_mode(Mode, ['assertEqualToResultMsg', A, X, M], TOut) :-
    translate_term_mode(Mode, A, TA),
    fresh_var(actual, ActualV),
    results_bag_equal_term(ActualV, [quote, X], Cond),
    assert_error_quoted(['assertEqualToResultMsg', A, X], M, ErrorQ),
    TOut = [let, ActualV, [collapse, TA],
            [if, Cond, '()', ErrorQ]], !.

%% noreduce-eq compares unevaluated forms; protect both sides with quote.
translate_term_mode(_Mode, ['noreduce-eq', A, B],
                    ['==', [quote, A], [quote, B]]) :- !.

%% unquote of a syntactically quoted form evaluates the inner form. A bare
%% unquote stays inert (as in upstream HE), so only the quoted shape lowers.
translate_term_mode(Mode, [unquote, [quote, X]], TX) :-
    translate_term_mode(Mode, X, TX), !.

%% Upstream typed-call errors for change-state! embed the original source
%% expression; route through a helper that carries the quoted original.
translate_term_mode(Mode, ['change-state!', T, V],
                    ['change-state-with-source',
                     [quote, ['change-state!', T, V]], TT, TV]) :-
    translate_term_mode(Mode, T, TT),
    translate_term_mode(Mode, V, TV), !.

%% add-atom returns () in HE but True in PeTTa; wrap to the HE surface.
translate_term_mode(Mode, ['add-atom', S, A],
                    [let, FV, ['add-atom', TS, TA], '()']) :-
    translate_term_mode(Mode, S, TS),
    translate_term_mode(data, A, TA),
    fresh_var(discard, FV), !.

%% (import! is unit-wrapped at the file-writing stage, after module
%% relocation and dependency discovery, which key on the bare import shape.)

%% Upstream evaluates match results (the instantiated template reduces
%% further); native PeTTa returns them raw, so wrap with an explicit eval.
%% A quote-headed template is irreducible in upstream HE, so it is left
%% unwrapped (native quote-stripping then happens symmetrically on the
%% comparison sides). The match PATTERN is data and stays verbatim.
translate_term_mode(Mode, [match, S, P, T], TOut) :-
    translate_term_mode(Mode, S, TS),
    translate_term_mode(Mode, T, TT),
    (   T = [quote|_]
    ->  TOut = [match, TS, P, TT]
    ;   fresh_var(matched, RV),
        %% Upstream match result evaluation reduces builtin structure further
        %% but preserves non-builtin heads inert; the runtime helper mirrors
        %% that narrower behavior better than a full native eval.
        TOut = [let, RV, [match, TS, P, TT], ['match-template-eval', RV]]
    ), !.

%% case scrutinees evaluate; branch patterns are data and stay verbatim.
translate_term_mode(Mode, [case, Scrut, Branches], [case, TScrut, TBranches]) :-
    is_list(Branches),
    translate_term_mode(Mode, Scrut, TScrut),
    maplist(translate_case_branch(Mode), Branches, TBranches), !.

translate_case_branch(Mode, [Pat, Body], [Pat, TBody]) :-
    translate_term_mode(Mode, Body, TBody), !.
translate_case_branch(_, Branch, Branch).

%% quote payloads are unevaluated data; never rewrite inside them.
translate_term_mode(_Mode, [quote|Payload], [quote|Payload]) :- !.

%% let / let* binding patterns are data; only values and bodies translate.
translate_term_mode(Mode, [let, Pat, Val, Body], [let, Pat, TVal, TBody]) :-
    translate_term_mode(Mode, Val, TVal),
    translate_term_mode(Mode, Body, TBody), !.

translate_term_mode(Mode, ['let*', Bindings, Body], ['let*', TBindings, TBody]) :-
    is_list(Bindings),
    maplist(translate_letstar_binding(Mode), Bindings, TBindings),
    translate_term_mode(Mode, Body, TBody), !.

translate_letstar_binding(Mode, [Pat, Val], [Pat, TVal]) :-
    translate_term_mode(Mode, Val, TVal), !.
translate_letstar_binding(_, B, B).

%% Atomspace data positions still need HE-only control surfaces lowered, but
%% plain applications must stay as stored application data instead of becoming
%% runtime call-or-inert wrappers inside the atom being added.
translate_term_mode(data, [F|Args], [F|TArgs]) :-
    maplist(translate_term_mode(data), Args, TArgs), !.

%% Applications of source-defined heads route through call-or-inert so a
%% no-matching-equation call stays inert (with evaluated arguments), as in
%% upstream HE, instead of yielding an empty result. Expression arguments are
%% evaluated through let bindings at the call site so logical-variable
%% bindings thread out of argument evaluation (map/collapse would sever them).
translate_term_mode(Mode, [F|Args], TOut) :-
    (   he2petta_source_defined_fun(F)
    ;   atom(F), atom_concat('$', _, F)   % variable-headed application
    ),
    maplist(translate_term_mode(Mode), Args, TArgs),
    bind_expression_args(TArgs, BoundArgs, Bindings),
    wrap_call_with_bindings(Bindings, ['call-or-inert', [quote, [F|BoundArgs]]], TOut), !.

%% Native PeTTa's arithmetic/comparison runtime does not surface HE typed-call
%% errors faithfully (notably strings and custom typed atoms), so route the
%% shared numeric/comparison heads through the HE compatibility helper too.
translate_term_mode(Mode, [F|Args], TOut) :-
    typed_checked_builtin_head(F),
    maplist(translate_term_mode(Mode), Args, TArgs),
    bind_expression_args(TArgs, BoundArgs, Bindings),
    wrap_call_with_bindings(Bindings, ['call-or-inert', [quote, [F|BoundArgs]]], TOut), !.

%% Top-level HE bangs run before later declarations are loaded. When they
%% mention a head that the same source file defines only later, upstream HE
%% leaves the call inert with evaluated arguments. Quote-protect that future
%% source-defined application directly instead of routing through runtime
%% helper facts that would otherwise have to appear in &self too early.
translate_term_mode(Mode, [F|Args], TOut) :-
    he2petta_future_source_defined_fun(F),
    maplist(translate_term_mode(Mode), Args, TArgs),
    bind_expression_args(TArgs, BoundArgs, Bindings),
    wrap_call_with_bindings(Bindings, [quote, [F|BoundArgs]], TOut), !.

bind_expression_args([], [], []).
bind_expression_args([A|As], [V|Vs], [V-A|Bs]) :-
    is_list(A),
    arg_contains_evaluable(A), !,
    fresh_var(arg, V),
    bind_expression_args(As, Vs, Bs).
bind_expression_args([A|As], [A|Vs], Bs) :-
    bind_expression_args(As, Vs, Bs).

%% Pure constructor data passes verbatim into the quoted call; only arguments
%% containing something evaluable are pre-bound through let. Nested-head
%% applications (curried partial applications like ((curry +) 2)) count as
%% evaluable via their base head symbol.
arg_contains_evaluable([F|Rest]) :-
    (   atom(F),
        (   he2petta_source_defined_fun(F)
        ;   atom_concat('$', _, F)
        ;   evaluable_builtin_head(F)
        )
    ->  true
    ;   is_list(F),
        base_head_symbol(F, S),
        atom(S),
        he2petta_source_defined_fun(S)
    ->  true
    ;   ( member(Sub, [F|Rest]), is_list(Sub), arg_contains_evaluable(Sub) )
    ), !.

evaluable_builtin_head(F) :-
    memberchk(F, ['+', '-', '*', '/', '%', '<', '>', '==', '!=',
                  let, 'let*', if, case, match, collapse, superpose,
                  'car-atom', 'cdr-atom', 'cons-atom', eval,
                  'call-or-inert', 'eval-or-inert']).

typed_checked_builtin_head(F) :-
    memberchk(F, ['+', '-', '*', '/', '%', '<', '>', '==', '!=']).

wrap_call_with_bindings([], Call, Call).
wrap_call_with_bindings([V-A|Bs], Call, [let, V, A, Inner]) :-
    wrap_call_with_bindings(Bs, Call, Inner).

%% add-reduct stores the equation with an already-reduced body and returns ().
%% The stored equation is built around a runtime-reduced value; the equation
%% expression itself is a literal argument to add-atom, so PeTTa does not
%% re-evaluate it.
translate_term_mode(Mode, ['add-reduct', S, ['=', H, B]],
                    [let, ValV, TB,
                     [let, FV, ['add-atom', TS, ['=', H, ValV]], '()']]) :-
    translate_term_mode(Mode, S, TS),
    translate_term_mode(Mode, B, TB),
    fresh_var(reduced, ValV),
    fresh_var(discard, FV), !.

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

%% Plain facts are stored data: upstream HE does not evaluate them, so they
%% pass through verbatim (reserved-head renaming already ran as a pre-pass).
translate_decl_mode(_, X, X) :-
    is_list(X),
    X \= ['!'|_], !.

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
