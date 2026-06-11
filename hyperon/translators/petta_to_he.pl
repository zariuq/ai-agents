%% PeTTa → HE Translator (Prolog module)
%%
%% Faithful syntactic rewriting of PeTTa-specific constructs to HE form.

:- module(petta_to_he,
          [ translate_term/2,
            translate_term_hyperpose/2,
            translate_term_ffi_tokens/2,
            translate_term_petta_he/2,
            translate_term_petta_he_hyperpose/2,
            translate_term_extended/2,
            translate_term_extended_hyperpose/2,
            translate_term_trusted/2,
            translate_term_trusted_extended/2,
            translate_decl/2,
            translate_decl_hyperpose/2,
            translate_decl_ffi_tokens/2,
            translate_decl_petta_he/2,
            translate_decl_petta_he_hyperpose/2,
            translate_decl_extended/2,
            translate_decl_extended_hyperpose/2,
            translate_decl_trusted/2,
            translate_decl_trusted_extended/2,
            translate_program/2,
            translate_program_hyperpose/2,
            translate_program_ffi_tokens/2,
            translate_program_petta_he/2,
            translate_program_petta_he_hyperpose/2,
            translate_program_extended/2,
            translate_program_extended_hyperpose/2,
            translate_program_trusted/2,
            translate_program_trusted_extended/2,
            rewrite_partial_builtin_value_terms/3,
            normalize_callable_equality_program/2,
            optimize_term/2,
            optimize_decl/2,
            optimize_program/2,
            with_helper_context/2,
            quoted_syntax_fun/1,
            petta_test_equal_fun/1,
            petta_test_equal_data_fun/1,
            petta_test_runtime_bool_fun/1,
            petta_test_results_fun/1,
            petta_test_results_data_fun/1,
            petta_test_bag_fun/1,
            petta_test_normalize_fun/1,
            petta_test_public_term_fun/1,
            petta_test_public_syntax_fun/1,
            petta_if2_fun/1,
            petta_lambda_fun/1,
            petta_apply1_fun/1,
            petta_apply2_fun/1,
            petta_bool_and_fun/1,
            petta_bool_or_fun/1,
            petta_member_fun/1,
            petta_ffi_function_call_inversion_fun/1,
            petta_lib_petta_helper_decls/2,
            test_call_needs_collapse/1,
            test_call_needs_bag_equality/1,
            petta_state_clear_fun/1,
            petta_state_set_fun/1,
            petta_state_get_fun/1,
            petta_state_cell_fun/1
          ]).

:- use_module(metta_parser, [print_sexpr/1]).

%% ── Fresh variable generation (capture-avoiding) ────────────────
%% Hardcoded $_ and $__r cause variable capture when source terms contain
%% those names. Use gensym-based fresh names instead.

:- dynamic tr_counter/1.
tr_counter(0).

:- dynamic tr_helper_name/2.
:- dynamic tr_source_fun_arity/2.
:- dynamic tr_source_fun_count/2.
:- dynamic tr_expr_data_fun/2.
:- dynamic tr_source_return_arg/2.
:- dynamic tr_head_normalized_fun/2.
:- dynamic tr_member_filter_fun/3.
:- dynamic tr_source_fun_clause/3.

:- meta_predicate with_helper_context(+, 0).

fresh_var(Prefix, Var) :-
    retract(tr_counter(N)),
    N1 is N + 1,
    assert(tr_counter(N1)),
    atomic_list_concat(['$__tr_', Prefix, '_', N1], Var).

atom_subst_apply_term(THead, TArgs, TExpr) :-
    fresh_var(apply_fun, FunVar),
    TExpr = [eval, ['atom-subst', THead, FunVar, [FunVar|TArgs]]].

with_helper_context(SourceTerms, Goal) :-
    setup_call_cleanup(
        activate_helper_context(SourceTerms, Saved),
        Goal,
        restore_helper_context(Saved)).

activate_helper_context(SourceTerms, Saved) :-
    findall(Key-Name, tr_helper_name(Key, Name), SavedHelpers),
    findall(Fun-Arity, tr_source_fun_arity(Fun, Arity), SavedArities),
    findall(Fun-Count, tr_source_fun_count(Fun, Count), SavedCounts),
    findall(Fun-Positions, tr_expr_data_fun(Fun, Positions), SavedExprData),
    findall(Fun-Pos, tr_source_return_arg(Fun, Pos), SavedReturnArgs),
    findall(Fun-Arity, tr_head_normalized_fun(Fun, Arity), SavedHeadNormalized),
    findall(Fun-RetPos-TuplePos,
            tr_member_filter_fun(Fun, RetPos, TuplePos),
            SavedMemberFilters),
    findall(Fun-Args-RHS,
            tr_source_fun_clause(Fun, Args, RHS),
            SavedFunClauses),
    Saved = saved(SavedHelpers, SavedArities, SavedCounts, SavedExprData,
                  SavedReturnArgs, SavedHeadNormalized, SavedMemberFilters,
                  SavedFunClauses),
    retractall(tr_helper_name(_, _)),
    retractall(tr_source_fun_arity(_, _)),
    retractall(tr_source_fun_count(_, _)),
    retractall(tr_expr_data_fun(_, _)),
    retractall(tr_source_return_arg(_, _)),
    retractall(tr_head_normalized_fun(_, _)),
    retractall(tr_member_filter_fun(_, _, _)),
    retractall(tr_source_fun_clause(_, _, _)),
    helper_context_names(SourceTerms, HelperNames),
    forall(member(Key-Name, HelperNames),
           assertz(tr_helper_name(Key, Name))),
    source_fun_arities(SourceTerms, Arities),
    forall(member(Fun-Arity, Arities),
           assertz(tr_source_fun_arity(Fun, Arity))),
    source_fun_counts(SourceTerms, Counts),
    forall(member(Fun-Count, Counts),
           assertz(tr_source_fun_count(Fun, Count))),
    source_expr_data_fun_positions(SourceTerms, ExprDataFuns),
    forall(member(Fun-Positions, ExprDataFuns),
           assertz(tr_expr_data_fun(Fun, Positions))),
    source_fun_return_args(SourceTerms, ReturnArgs),
    forall(member(Fun-Pos, ReturnArgs),
           assertz(tr_source_return_arg(Fun, Pos))),
    source_head_normalized_funs(SourceTerms, HeadNormalized),
    forall(member(Fun-Arity, HeadNormalized),
           assertz(tr_head_normalized_fun(Fun, Arity))),
    source_member_filter_funs(SourceTerms, MemberFilters),
    forall(member(Fun-RetPos-TuplePos, MemberFilters),
           assertz(tr_member_filter_fun(Fun, RetPos, TuplePos))),
    source_fun_clauses(SourceTerms, FunClauses),
    forall(member(Fun-Args-RHS, FunClauses),
           assertz(tr_source_fun_clause(Fun, Args, RHS))).

restore_helper_context(saved(SavedHelpers, SavedArities, SavedCounts,
                             SavedExprData, SavedReturnArgs,
                             SavedHeadNormalized, SavedMemberFilters,
                             SavedFunClauses)) :-
    retractall(tr_helper_name(_, _)),
    retractall(tr_source_fun_arity(_, _)),
    retractall(tr_source_fun_count(_, _)),
    retractall(tr_expr_data_fun(_, _)),
    retractall(tr_source_return_arg(_, _)),
    retractall(tr_head_normalized_fun(_, _)),
    retractall(tr_member_filter_fun(_, _, _)),
    retractall(tr_source_fun_clause(_, _, _)),
    forall(member(Key-Name, SavedHelpers),
           assertz(tr_helper_name(Key, Name))),
    forall(member(Fun-Arity, SavedArities),
           assertz(tr_source_fun_arity(Fun, Arity))),
    forall(member(Fun-Count, SavedCounts),
           assertz(tr_source_fun_count(Fun, Count))),
    forall(member(Fun-Positions, SavedExprData),
           assertz(tr_expr_data_fun(Fun, Positions))),
    forall(member(Fun-Pos, SavedReturnArgs),
           assertz(tr_source_return_arg(Fun, Pos))),
    forall(member(Fun-Arity, SavedHeadNormalized),
           assertz(tr_head_normalized_fun(Fun, Arity))),
    forall(member(Fun-RetPos-TuplePos, SavedMemberFilters),
           assertz(tr_member_filter_fun(Fun, RetPos, TuplePos))),
    forall(member(Fun-Args-RHS, SavedFunClauses),
           assertz(tr_source_fun_clause(Fun, Args, RHS))).

source_fun_arities(SourceTerms, Arities) :-
    findall(Fun-Arity,
            ( member(['=', [Fun|Args], _], SourceTerms),
              atom(Fun),
              length(Args, Arity)
            ),
            Raw),
    sort(Raw, Arities).

source_fun_counts(SourceTerms, Counts) :-
    findall(Fun,
            ( member(['=', [Fun|_], _], SourceTerms),
              atom(Fun)
            ),
            Funs),
    sort(Funs, UniqueFuns),
    findall(Fun-Count,
            ( member(Fun, UniqueFuns),
              count_occurrences(Fun, Funs, Count)
            ),
            Counts).

source_expr_data_fun_positions(SourceTerms, Entries) :-
    findall(Fun-Positions,
            ( append(_, Tail, SourceTerms),
              expr_data_fun_entry(Tail, Fun, Positions)
            ),
            RawEntries),
    sort(RawEntries, Entries).

source_fun_return_args(SourceTerms, Entries) :-
    findall(Fun,
            ( member(['=', [Fun|_], _], SourceTerms),
              atom(Fun)
            ),
            Funs0),
    sort(Funs0, Funs),
    findall(Fun-Pos,
            ( member(Fun, Funs),
              source_fun_return_arg_position(SourceTerms, Fun, Pos)
            ),
            Entries).

source_head_normalized_funs(SourceTerms, Entries) :-
    findall(Fun-Arity,
            ( member(['=', [Fun|Args], _], SourceTerms),
              atom(Fun),
              head_args_need_normalization(Args),
              length(Args, Arity)
            ),
            Raw),
    sort(Raw, Entries).

source_member_filter_funs(SourceTerms, Entries) :-
    findall(Fun-RetPos-TuplePos,
            ( member(['=', [Fun|Args], RHS], SourceTerms),
              atom(Fun),
              member_filter_clause_positions(Args, RHS, RetPos, TuplePos)
            ),
            Raw),
    sort(Raw, Entries).

member_filter_clause_positions(Args,
                               [let, Truth, ['is-member', RetVar, TupleVar], RetVar],
                               RetPos, TuplePos) :-
    member_filter_truth_atom(Truth),
    nth1(RetPos, Args, RetVar),
    nth1(TuplePos, Args, TupleVar),
    RetPos =\= TuplePos,
    source_variable_atom(RetVar),
    source_variable_atom(TupleVar).

member_filter_truth_atom('True').
member_filter_truth_atom(true).

source_fun_return_arg_position(SourceTerms, Fun, Pos) :-
    findall(Args-RHS,
            member(['=', [Fun|Args], RHS], SourceTerms),
            Clauses),
    Clauses \= [],
    maplist(clause_return_arg_position, Clauses, Positions),
    sort(Positions, [Pos]).

clause_return_arg_position(Args-RHS, Pos) :-
    findall(Idx,
            ( nth1(Idx, Args, Var),
              source_variable_atom(Var),
              rhs_returns_arg_var(RHS, Var)
            ),
            Positions),
    sort(Positions, [Pos]).

rhs_returns_arg_var(Var, Var) :-
    source_variable_atom(Var),
    !.
rhs_returns_arg_var([let, _, _, Inner], Var) :-
    rhs_returns_arg_var(Inner, Var),
    !.
rhs_returns_arg_var([only, _, Inner], Var) :-
    rhs_returns_arg_var(Inner, Var),
    !.

expr_data_fun_entry(
    [['=', ['map-flat3', [_, Nil]], Nil],
     ['=', ['map-flat3', [_, [cons, _, _]]], _]
     | _],
    'map-flat3', [1]) :-
    source_nil(Nil).
expr_data_fun_entry(
    [['=', ['map-flat4', [_, [_, Nil]]], Nil],
     ['=', ['map-flat4', [_, [_, [cons, _, _]]]], _]
     | _],
    'map-flat4', [1]) :-
    source_nil(Nil).

source_fun_clauses(SourceTerms, Clauses) :-
    findall(Fun-Args-RHS,
            ( member(['=', [Fun|Args], RHS], SourceTerms),
              atom(Fun)
            ),
            Clauses).

count_occurrences(_, [], 0).
count_occurrences(Fun, [Fun|Rest], Count) :-
    !,
    count_occurrences(Fun, Rest, RestCount),
    Count is RestCount + 1.
count_occurrences(Fun, [_|Rest], Count) :-
    count_occurrences(Fun, Rest, Count).

helper_context_names(SourceTerms, HelperNames) :-
    term_atom_set(SourceTerms, Used0),
    choose_helper_name(quoted_syntax, Used0, Used1, Quote),
    choose_helper_name(test_equal, Used1, Used2, TestEqual),
    choose_helper_name(test_equal_data, Used2, Used3, TestEqualData),
    choose_helper_name(test_runtime_bool, Used3, Used4, TestRuntimeBool),
    choose_helper_name(test_results, Used4, Used5, TestResults),
    choose_helper_name(test_results_data, Used5, Used6, TestResultsData),
    choose_helper_name(test_bag, Used6, Used7, TestBag),
    choose_helper_name(test_normalize, Used7, Used8, TestNormalize),
    choose_helper_name(test_public_term, Used8, Used9, TestPublicTerm),
    choose_helper_name(test_public_syntax, Used9, Used10, TestPublicSyntax),
    choose_helper_name(alpha_equal_eval, Used10, Used11, AlphaEqualEval),
    choose_helper_name(runtime_call, Used11, Used12, RuntimeCall),
    choose_helper_name(runtime_eval, Used12, Used13, RuntimeEval),
    choose_helper_name(runtime_reduce, Used13, Used14, RuntimeReduce),
    choose_helper_name(if2, Used14, Used15, If2),
    choose_helper_name(lambda, Used15, Used16, Lambda),
    choose_helper_name(apply1, Used16, Used17, Apply1),
    choose_helper_name(apply2, Used17, Used18, Apply2),
    choose_helper_name(bool_and, Used18, Used19, BoolAnd),
    choose_helper_name(bool_or, Used19, Used20, BoolOr),
    choose_helper_name(member, Used20, Used21, Member),
    choose_helper_name(ffi_function_call_inversion, Used21, Used22, FfiFunctionCallInversion),
    choose_helper_name(state_clear, Used22, Used23, Clear),
    choose_helper_name(state_set, Used23, Used24, Set),
    choose_helper_name(state_get, Used24, Used25, Get),
    choose_helper_name(state_cell, Used25, _Used26, Cell),
    HelperNames = [
        quoted_syntax-Quote,
        test_equal-TestEqual,
        test_equal_data-TestEqualData,
        test_runtime_bool-TestRuntimeBool,
        test_results-TestResults,
        test_results_data-TestResultsData,
        test_bag-TestBag,
        test_normalize-TestNormalize,
        test_public_term-TestPublicTerm,
        test_public_syntax-TestPublicSyntax,
        alpha_equal_eval-AlphaEqualEval,
        runtime_call-RuntimeCall,
        runtime_eval-RuntimeEval,
        runtime_reduce-RuntimeReduce,
        if2-If2,
        lambda-Lambda,
        apply1-Apply1,
        apply2-Apply2,
        bool_and-BoolAnd,
        bool_or-BoolOr,
        member-Member,
        ffi_function_call_inversion-FfiFunctionCallInversion,
        state_clear-Clear,
        state_set-Set,
        state_get-Get,
        state_cell-Cell
    ].

choose_helper_name(Key, Used0, [Name|Used0], Name) :-
    helper_default_name(Key, Default),
    \+ memberchk(Default, Used0),
    !,
    Name = Default.
choose_helper_name(Key, Used0, [Name|Used0], Name) :-
    helper_fallback_base(Key, Base),
    unique_helper_name(Base, Used0, 1, Name).

unique_helper_name(Base, Used, N, Name) :-
    atomic_list_concat([Base, N], '-', Candidate),
    (   memberchk(Candidate, Used)
    ->  N1 is N + 1,
        unique_helper_name(Base, Used, N1, Name)
    ;   Name = Candidate
    ).

term_atom_set(Term, Atoms) :-
    collect_term_atoms(Term, [], RawAtoms),
    sort(RawAtoms, Atoms).

collect_term_atoms(Term, Acc, [Term|Acc]) :-
    atom(Term),
    !.
collect_term_atoms(Term, Acc0, Acc) :-
    is_list(Term),
    !,
    collect_term_atoms_list(Term, Acc0, Acc).
collect_term_atoms(_, Acc, Acc).

collect_term_atoms_list([], Acc, Acc).
collect_term_atoms_list([Term|Terms], Acc0, Acc) :-
    collect_term_atoms(Term, Acc0, Acc1),
    collect_term_atoms_list(Terms, Acc1, Acc).

helper_default_name(quoted_syntax, 'quoted-syntax').
helper_default_name(test_equal, 'petta-test-equal').
helper_default_name(test_equal_data, 'petta-test-equal-data').
helper_default_name(test_runtime_bool, 'petta-test-runtime-bool').
helper_default_name(test_results, 'petta-test-results').
helper_default_name(test_results_data, 'petta-test-results-data').
helper_default_name(test_bag, 'petta-test-bag-equal').
helper_default_name(test_normalize, 'petta-normalize-results').
helper_default_name(test_public_term, 'petta-public-term').
helper_default_name(test_public_syntax, 'petta-public-syntax').
helper_default_name(alpha_equal_eval, 'petta-alpha-equal-eval').
helper_default_name(runtime_call, 'petta-runtime-call').
helper_default_name(runtime_eval, 'petta-runtime-eval').
helper_default_name(runtime_reduce, 'petta-runtime-reduce').
helper_default_name(if2, 'petta-if2').
helper_default_name(lambda, 'petta-lambda').
helper_default_name(apply1, 'petta-apply1').
helper_default_name(apply2, 'petta-apply2').
helper_default_name(bool_and, 'petta-bool-and').
helper_default_name(bool_or, 'petta-bool-or').
helper_default_name(member, 'petta-member').
helper_default_name(ffi_function_call_inversion, 'petta-ffi-function-call-inversion').
helper_default_name(state_clear, '__tr-petta-state-clear!').
helper_default_name(state_set, '__tr-petta-state-set!').
helper_default_name(state_get, '__tr-petta-state-get').
helper_default_name(state_cell, '__tr-petta-state-cell').

helper_fallback_base(quoted_syntax, '__tr-quoted-syntax').
helper_fallback_base(test_equal, 'petta-test-equal').
helper_fallback_base(test_equal_data, 'petta-test-equal-data').
helper_fallback_base(test_runtime_bool, 'petta-test-runtime-bool').
helper_fallback_base(test_results, 'petta-test-results').
helper_fallback_base(test_results_data, 'petta-test-results-data').
helper_fallback_base(test_bag, 'petta-test-bag-equal').
helper_fallback_base(test_normalize, 'petta-normalize-results').
helper_fallback_base(test_public_term, 'petta-public-term').
helper_fallback_base(test_public_syntax, 'petta-public-syntax').
helper_fallback_base(alpha_equal_eval, 'petta-alpha-equal-eval').
helper_fallback_base(runtime_call, 'petta-runtime-call').
helper_fallback_base(runtime_eval, 'petta-runtime-eval').
helper_fallback_base(runtime_reduce, 'petta-runtime-reduce').
helper_fallback_base(if2, 'petta-if2').
helper_fallback_base(lambda, 'petta-lambda').
helper_fallback_base(apply1, 'petta-apply1').
helper_fallback_base(apply2, 'petta-apply2').
helper_fallback_base(bool_and, 'petta-bool-and').
helper_fallback_base(bool_or, 'petta-bool-or').
helper_fallback_base(member, 'petta-member').
helper_fallback_base(ffi_function_call_inversion, 'petta-ffi-function-call-inversion').
helper_fallback_base(state_clear, '__tr-petta-state-clear').
helper_fallback_base(state_set, '__tr-petta-state-set').
helper_fallback_base(state_get, '__tr-petta-state-get').
helper_fallback_base(state_cell, '__tr-petta-state-cell').

helper_name(Key, Name) :-
    tr_helper_name(Key, Active),
    !,
    Name = Active.
helper_name(Key, Name) :-
    helper_default_name(Key, Name).

quoted_syntax_fun(Name) :-
    helper_name(quoted_syntax, Name).

petta_test_equal_fun(Name) :-
    helper_name(test_equal, Name).

petta_test_equal_data_fun(Name) :-
    helper_name(test_equal_data, Name).

petta_test_runtime_bool_fun(Name) :-
    helper_name(test_runtime_bool, Name).

petta_test_results_fun(Name) :-
    helper_name(test_results, Name).

petta_test_results_data_fun(Name) :-
    helper_name(test_results_data, Name).

petta_test_bag_fun(Name) :-
    helper_name(test_bag, Name).

petta_test_normalize_fun(Name) :-
    helper_name(test_normalize, Name).

petta_test_public_term_fun(Name) :-
    helper_name(test_public_term, Name).

petta_test_public_syntax_fun(Name) :-
    helper_name(test_public_syntax, Name).

petta_alpha_equal_eval_fun(Name) :-
    helper_name(alpha_equal_eval, Name).

petta_runtime_call_fun(Name) :-
    helper_name(runtime_call, Name).

petta_runtime_eval_fun(Name) :-
    helper_name(runtime_eval, Name).

petta_runtime_reduce_fun(Name) :-
    helper_name(runtime_reduce, Name).

petta_if2_fun(Name) :-
    helper_name(if2, Name).

petta_lambda_fun(Name) :-
    helper_name(lambda, Name).

petta_apply1_fun(Name) :-
    helper_name(apply1, Name).

petta_apply2_fun(Name) :-
    helper_name(apply2, Name).

petta_bool_and_fun(Name) :-
    helper_name(bool_and, Name).

petta_bool_or_fun(Name) :-
    helper_name(bool_or, Name).

petta_member_fun(Name) :-
    helper_name(member, Name).

petta_ffi_function_call_inversion_fun(Name) :-
    helper_name(ffi_function_call_inversion, Name).

%% Quoted PeTTa syntax must be translated as code, but remain data.
%%
%% This helper rewrites source syntax into target HE syntax without executing
%% it, so later eval/unquote on the translated file sees the right target
%% code rather than the original PeTTa-specific surface forms.
translate_quoted_term_mode(Mode, [quote, Expr], [quote, TExpr]) :-
    native_quote_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [quote, Expr], [QuoteFun, [quote, TExpr]]) :-
    quoted_syntax_fun(QuoteFun),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [call, Expr], [call, TExpr]) :-
    petta_he_profile_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [eval, Expr], [eval, TExpr]) :-
    petta_he_profile_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [reduce, Expr], [reduce, TExpr]) :-
    petta_he_profile_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, ['=alpha', Left, Right], TExpr) :-
    \+ petta_he_profile_mode(Mode),
    translate_alpha_equal_mode(Mode, Left, Right, TExpr), !.
translate_quoted_term_mode(Mode, [call, Expr], TExpr) :-
    translate_call_like_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [eval, Expr], TExpr) :-
    translate_eval_like_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [reduce, Expr], TExpr) :-
    translate_reduce_like_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, ['__tr-raw-apply1', Head, Arg], TExpr) :-
    translate_quoted_term_mode(Mode, Head, THead),
    translate_quoted_term_mode(Mode, Arg, TArg),
    atom_subst_apply_term(THead, [TArg], TExpr),
    !.
translate_quoted_term_mode(Mode, ['__tr-raw-apply', Head|Args], TExpr) :-
    Args \= [],
    translate_quoted_term_mode(Mode, Head, THead),
    translate_quoted_term_list_mode(Mode, Args, TArgs),
    atom_subst_apply_term(THead, TArgs, TExpr),
    !.
translate_quoted_term_mode(Mode, ['bind!', Ref, ['new-state', Init]],
                           [SetFun, TRef, TInit]) :-
    petta_state_set_fun(SetFun),
    translate_quoted_term_mode(Mode, Ref, TRef),
    translate_quoted_term_mode(Mode, Init, TInit), !.
translate_quoted_term_mode(Mode, ['change-state!', Ref, Value],
                           [SetFun, TRef, TValue]) :-
    petta_state_set_fun(SetFun),
    translate_quoted_term_mode(Mode, Ref, TRef),
    translate_quoted_term_mode(Mode, Value, TValue), !.
translate_quoted_term_mode(Mode, ['get-state', Ref], [GetFun, TRef]) :-
    petta_state_get_fun(GetFun),
    translate_quoted_term_mode(Mode, Ref, TRef), !.
translate_quoted_term_mode(Mode, ['new-state', Init],
                           [QuoteFun, [quote, ['new-state', TInit]]]) :-
    quoted_syntax_fun(QuoteFun),
    translate_quoted_term_mode(Mode, Init, TInit), !.
translate_quoted_term_mode(Mode, [length, [collapse, Expr]],
                           [let, TupleVar, [collapse, TExpr], ['size-atom', TupleVar]]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr),
    fresh_var(tuple, TupleVar), !.
translate_quoted_term_mode(Mode, [length, Expr], [length, TExpr]) :-
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [if, Cond, Then], [If2Fun, TCond, TThen]) :-
    \+ petta_he_profile_mode(Mode),
    petta_if2_fun(If2Fun),
    translate_quoted_term_mode(Mode, Cond, TCond),
    translate_quoted_term_mode(Mode, Then, TThen), !.
translate_quoted_term_mode(Mode, [if, Cond, Then, Else], [if, TCond, TThen, TElse]) :-
    translate_quoted_term_mode(Mode, Cond, TCond),
    translate_quoted_term_mode(Mode, Then, TThen),
    translate_quoted_term_mode(Mode, Else, TElse), !.
translate_quoted_term_mode(Mode, [and, Left, Right],
                          [let, LeftVar, TLeft,
                           [let, RightVar, TRight,
                            [AndFun, LeftVar, RightVar]]]) :-
    \+ petta_he_profile_mode(Mode),
    petta_bool_and_fun(AndFun),
    translate_quoted_term_mode(Mode, Left, TLeft),
    translate_quoted_term_mode(Mode, Right, TRight),
    fresh_var(bool_left, LeftVar),
    fresh_var(bool_right, RightVar), !.
translate_quoted_term_mode(Mode, [or, Left, Right],
                          [let, LeftVar, TLeft,
                           [let, RightVar, TRight,
                            [OrFun, LeftVar, RightVar]]]) :-
    \+ petta_he_profile_mode(Mode),
    petta_bool_or_fun(OrFun),
    translate_quoted_term_mode(Mode, Left, TLeft),
    translate_quoted_term_mode(Mode, Right, TRight),
    fresh_var(bool_left, LeftVar),
    fresh_var(bool_right, RightVar), !.
translate_quoted_term_mode(Mode, [member, Item, Tuple], [MemberFun, TItem, TTuple]) :-
    \+ petta_he_profile_mode(Mode),
    petta_member_fun(MemberFun),
    translate_quoted_term_mode(Mode, Item, TItem),
    translate_quoted_term_mode(Mode, Tuple, TTuple), !.
translate_quoted_term_mode(Mode, [maplist, Fun, List],
                           ['map-atom', TList, ItemVar, TBody]) :-
    translate_quoted_term_mode(Mode, List, TList),
    fresh_var(item, ItemVar),
    partial_application_quoted_body(Mode, Fun, ItemVar, TBody), !.
translate_quoted_term_mode(Mode, ['filter-atom', List, Fun],
                           ['filter-atom', TList, ItemVar, TBody]) :-
    translate_quoted_term_mode(Mode, List, TList),
    fresh_var(item, ItemVar),
    partial_application_quoted_body(Mode, Fun, ItemVar, TBody), !.
translate_quoted_term_mode(Mode, PartialCall, TExpr) :-
    source_defined_partial_value_call(PartialCall, _Head, _PrefixArgs, _Arity),
    translate_quoted_term_list_mode(Mode, PartialCall, TExpr), !.
translate_quoted_term_mode(Mode, PartialCall, TExpr) :-
    petta_he_profile_mode(Mode),
    partial_value_source_call(PartialCall, _Head, _PrefixArgs, _Arity),
    translate_quoted_term_list_mode(Mode, PartialCall, TExpr), !.
translate_quoted_term_mode(Mode, PartialCall, TExpr) :-
    partial_value_source_call(PartialCall, Head, PrefixArgs, Arity),
    translate_partial_value_quoted_mode(Mode, Head, PrefixArgs, Arity, TExpr), !.
translate_quoted_term_mode(Mode, [test, Actual, Expected],
                           [test, TActual, TExpected]) :-
    translate_quoted_term_mode(Mode, Actual, TActual),
    translate_quoted_term_mode(Mode, Expected, TExpected), !.
translate_quoted_term_mode(Mode, [msort, Expr], [msort, TExpr]) :-
    petta_he_profile_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [msort, Expr], [msort, TExpr]) :-
    tr_source_fun_arity(msort, 1),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [msort, _], _) :-
    throw_unsupported_petta_native_for_he_core(Mode, msort, translate_quoted_term_mode/3).
translate_quoted_term_mode(Mode, [cut], [cut]) :-
    petta_he_profile_mode(Mode), !.
translate_quoted_term_mode(Mode, [cut], _) :-
    throw_unsupported_cut_for_he_core(Mode, translate_quoted_term_mode/3).
translate_quoted_term_mode(Mode, [once, Expr], [once, TExpr]) :-
    petta_he_profile_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [once, Expr], [select, 1, TExpr]) :-
    he_extended_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_quoted_term_mode(Mode, [once, Expr], TExpr) :-
    translate_quoted_term_mode(Mode, Expr, TExpr0),
    pure_once_lowering(TExpr0, TExpr), !.
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
translate_quoted_term_mode(Mode, [Head|Args], TExpr) :-
    raw_expr_data_quote_mode(Mode),
    expr_data_fun_positions(Head, QuotePositions),
    translate_quoted_args_with_quote_positions(Mode, Args, QuotePositions, TArgs),
    TExpr = [Head|TArgs], !.
translate_quoted_term_mode(Mode, [Head], ['cons-atom', THead, '()']) :-
    source_variable_atom(Head),
    \+ petta_he_profile_mode(Mode),
    translate_quoted_term_mode(Mode, Head, THead), !.
translate_quoted_term_mode(Mode, [Head|Args], [Head|TArgs]) :-
    petta_he_profile_mode(Mode),
    source_variable_atom(Head),
    translate_quoted_term_list_mode(Mode, Args, TArgs), !.
translate_quoted_term_mode(Mode, [Head|Args], [THead|TArgs]) :-
    source_variable_atom(Head),
    \+ petta_he_profile_mode(Mode),
    Args \= [],
    translate_quoted_term_mode(Mode, Head, THead),
    translate_quoted_term_list_mode(Mode, Args, TArgs), !.
translate_quoted_term_mode(Mode, [Head|Args], TExpr) :-
    is_list(Head),
    Args \= [],
    expression_head_needs_curried_application(Head),
    translate_curried_application_quoted_mode(Mode, Head, Args, TExpr), !.
translate_quoted_term_mode(Mode, [Head|Args], [THead|TArgs]) :-
    is_list(Head),
    Args \= [],
    translate_quoted_term_mode(Mode, Head, THead),
    translate_quoted_term_list_mode(Mode, Args, TArgs), !.
translate_quoted_term_mode(Mode, [Head|Args], TExpr) :-
    Args \= [],
    needs_curried_application(Head, Args),
    translate_curried_application_quoted_mode(Mode, Head, Args, TExpr), !.
translate_quoted_term_mode(_, true, 'True') :- !.
translate_quoted_term_mode(_, false, 'False') :- !.
translate_quoted_term_mode(Mode, List, TList) :-
    is_list(List),
    maplist(translate_quoted_term_mode(Mode), List, TList), !.
translate_quoted_term_mode(_, X, X).

%% ── Core rewrite rules ──────────────────────────────────────────
%%
%% Modes:
%%   pure             - conservative HE surface (default)
%%   hyperpose        - pure + preserve hyperpose for HE runtimes that support it
%%   ffi_tokens       - explicit FFI-token target for non-pure inversion
%%   petta_he         - PeTTa --he profile target; preserves PeTTa goal control
%%   petta_he_hyperpose - petta_he + preserve hyperpose
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

translate_term_ffi_tokens(Term, Out) :-
    translate_term_mode(ffi_tokens, Term, Out).

translate_term_petta_he(Term, Out) :-
    translate_term_mode(petta_he, Term, Out).

translate_term_petta_he_hyperpose(Term, Out) :-
    translate_term_mode(petta_he_hyperpose, Term, Out).

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

translate_decl_ffi_tokens(Decl, Out) :-
    translate_decl_mode(ffi_tokens, Decl, Out).

translate_decl_petta_he(Decl, Out) :-
    translate_decl_mode(petta_he, Decl, Out).

translate_decl_petta_he_hyperpose(Decl, Out) :-
    translate_decl_mode(petta_he_hyperpose, Decl, Out).

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

translate_program_ffi_tokens(Program, Out) :-
    translate_program_mode(ffi_tokens, Program, Out).

translate_program_petta_he(Program, Out) :-
    translate_program_mode(petta_he, Program, Out).

translate_program_petta_he_hyperpose(Program, Out) :-
    translate_program_mode(petta_he_hyperpose, Program, Out).

translate_program_extended(Program, Out) :-
    translate_program_mode(extended, Program, Out).

translate_program_extended_hyperpose(Program, Out) :-
    translate_program_mode(extended_hyperpose, Program, Out).

translate_program_trusted(Program, Out) :-
    translate_program_mode(trusted, Program, Out).

translate_program_trusted_extended(Program, Out) :-
    translate_program_mode(trusted_extended, Program, Out).

trusted_new_space_prefix('&__tr_space_').
petta_state_clear_fun(Name) :-
    helper_name(state_clear, Name).
petta_state_set_fun(Name) :-
    helper_name(state_set, Name).
petta_state_get_fun(Name) :-
    helper_name(state_get, Name).
petta_state_cell_fun(Name) :-
    helper_name(state_cell, Name).

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
%%   pure/profile-independent lane → quote Expr'
%%   PeTTa --he profile lane        → quoted-syntax (quote Expr')
%%
%% Pure HE exposes a visible quote wrapper, so the backend-agnostic lane keeps
%% that native representation. The PeTTa profile can use quoted-syntax when it
%% needs PeTTa-visible raw syntax behavior.
translate_term_mode(Mode, [quote, Expr], [quote, TExpr]) :-
    native_quote_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.
translate_term_mode(Mode, [quote, Expr], [QuoteFun, [quote, TExpr]]) :-
    quoted_syntax_fun(QuoteFun),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.

%% PeTTa call/eval/reduce Expr
%%   → unquote (quote Expr')
%%
%% Source call/eval/reduce execute syntax-as-data. In pure HE target code,
%% unquote on translated syntax is the portable full-evaluation request.
translate_term_mode(Mode, [eval, Expr], TExpr) :-
    petta_he_profile_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TQuoted),
    TExpr = [eval, TQuoted], !.

%% PeTTa call/eval/reduce Expr
%%   PeTTa --he profile lane -> preserve native source evaluator surface
%%   portable lanes          -> unquote (quote Expr')
%%
%% The profile target runs on the PeTTa --he runtime, where eval/call/reduce
%% retain their source-level behavior over syntax objects. Lowering them to
%% HE-core unquote changes observable meaning for examples such as eval.metta.
translate_term_mode(Mode, [call, Expr], TExpr) :-
    petta_he_profile_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TQuoted),
    TExpr = [call, TQuoted], !.
translate_term_mode(Mode, [eval, Expr], TExpr) :-
    translate_eval_like_mode(Mode, Expr, TExpr0),
    force_runtime_helper_value(runtime_eval, TExpr0, TExpr), !.
translate_term_mode(Mode, ['=alpha', Left, Right], TExpr) :-
    \+ petta_he_profile_mode(Mode),
    translate_alpha_equal_mode(Mode, Left, Right, TExpr0),
    force_runtime_helper_value(alpha_equal_eval, TExpr0, TExpr), !.
translate_term_mode(Mode, [if, [once, Goal], Then], TExpr) :-
    \+ petta_he_profile_mode(Mode),
    translate_term_mode(Mode, [once, [let, 'True', Goal, Then]], TExpr), !.
translate_term_mode(Mode, [if, Cond, Then], [If2Fun, TCond, TThen]) :-
    \+ petta_he_profile_mode(Mode),
    petta_if2_fun(If2Fun),
    translate_term_mode(Mode, Cond, TCond),
    translate_term_mode(Mode, Then, TThen), !.
translate_term_mode(Mode, [if, Cond, Then, Else], [if, TCond, TThen, TElse]) :-
    translate_term_mode(Mode, Cond, TCond),
    translate_term_mode(Mode, Then, TThen),
    translate_term_mode(Mode, Else, TElse), !.
translate_term_mode(_Mode, ['is-var', Expr], 'True') :-
    source_variable_atom(Expr), !.
translate_term_mode(_Mode, ['is-var', Expr], 'False') :-
    nonvar(Expr),
    \+ source_variable_atom(Expr), !.
translate_term_mode(Mode, [and, Left, Right],
                    [let, LeftVar, TLeft,
                     [let, RightVar, TRight,
                      [AndFun, LeftVar, RightVar]]]) :-
    \+ petta_he_profile_mode(Mode),
    petta_bool_and_fun(AndFun),
    translate_term_mode(Mode, Left, TLeft),
    translate_term_mode(Mode, Right, TRight),
    fresh_var(bool_left, LeftVar),
    fresh_var(bool_right, RightVar), !.
translate_term_mode(Mode, [or, Left, Right],
                    [let, LeftVar, TLeft,
                     [let, RightVar, TRight,
                      [OrFun, LeftVar, RightVar]]]) :-
    \+ petta_he_profile_mode(Mode),
    petta_bool_or_fun(OrFun),
    translate_term_mode(Mode, Left, TLeft),
    translate_term_mode(Mode, Right, TRight),
    fresh_var(bool_left, LeftVar),
    fresh_var(bool_right, RightVar), !.
translate_term_mode(Mode, [member, Item, Tuple], [MemberFun, TItem, TTuple]) :-
    \+ petta_he_profile_mode(Mode),
    petta_member_fun(MemberFun),
    translate_term_mode(Mode, Item, TItem),
    translate_term_mode(Mode, Tuple, TTuple), !.

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
                TBody]) :-
    translate_term_mode(Mode, List, TList),
    translate_term_mode(Mode, Init, TInit),
    translate_term_mode(Mode, Agg, TAgg),
    fresh_var(acc, AccVar),
    fresh_var(item, ItemVar),
    reducer_application_body(Agg, TAgg, AccVar, ItemVar, TBody), !.

%% PeTTa short-form map-atom List Fun
%%   → map-atom List' $item (Fun' $item)
translate_term_mode(Mode, ['map-atom', List, Fun],
               ['map-atom', TList, ItemVar, TBody]) :-
    translate_term_mode(Mode, List, TList),
    fresh_var(item, ItemVar),
    partial_application_body(Mode, Fun, ItemVar, TBody), !.

%% PeTTa short-form maplist Fun List
%%   → map-atom List' $item (Fun' $item)
translate_term_mode(Mode, [maplist, Fun, List],
               ['map-atom', TList, ItemVar, TBody]) :-
    translate_term_mode(Mode, List, TList),
    fresh_var(item, ItemVar),
    partial_application_body(Mode, Fun, ItemVar, TBody), !.

%% PeTTa short-form filter-atom List Fun
%%   → filter-atom List' $item (Fun' $item)
translate_term_mode(Mode, ['filter-atom', List, Fun],
               ['filter-atom', TList, ItemVar, TBody]) :-
    translate_term_mode(Mode, List, TList),
    fresh_var(item, ItemVar),
    partial_application_body(Mode, Fun, ItemVar, TBody), !.

translate_term_mode(Mode, PartialCall, TExpr) :-
    petta_he_profile_mode(Mode),
    source_defined_partial_value_call(PartialCall, _Head, _PrefixArgs, _Arity),
    translate_term_list_mode(Mode, PartialCall, TExpr), !.

%% PeTTa renders under-applied calls as partial values.
translate_term_mode(Mode, PartialCall, TExpr) :-
    petta_he_profile_mode(Mode),
    partial_value_source_call(PartialCall, _Head, _PrefixArgs, _Arity),
    translate_term_list_mode(Mode, PartialCall, TExpr), !.

%% PeTTa renders under-applied calls as partial values.
translate_term_mode(Mode, PartialCall, TExpr) :-
    partial_value_source_call(PartialCall, Head, PrefixArgs, Arity),
    translate_partial_value_mode(Mode, Head, PrefixArgs, Arity, TExpr), !.

%% PeTTa renders under-applied calls as partial values.
translate_term_mode(_, [repr, PartialCall], ReprString) :-
    partial_call_repr(PartialCall, ReprString), !.

%% PeTTa raw reduce Expr
%%   → unquote (quote Expr')
%%
%% PeTTa's one-argument reduce dispatches syntax-as-data with source semantics.
%% Lower it through unquote(quote ...) so irreducible expressions become raw
%% data instead of HE quote wrappers.
translate_term_mode(Mode, [reduce, Expr], TExpr) :-
    petta_he_profile_mode(Mode),
    translate_quoted_term_mode(Mode, Expr, TQuoted),
    TExpr = [reduce, TQuoted], !.
translate_term_mode(Mode, [reduce, Expr], TExpr) :-
    translate_reduce_like_mode(Mode, Expr, TExpr0),
    force_runtime_helper_value(runtime_reduce, TExpr0, TExpr), !.

%% PeTTa named-state surface:
%%   bind! name (new-state value)  sets a named mutable cell and returns true
%%   change-state! name value      updates that cell and returns true
%%   get-state name                reads that cell
%%
%% HE's `new-state` is an actual State handle constructor, while PeTTa stores
%% state by symbolic name via nb_setval/2. Passing this syntax through creates
%% State handles in HE and changes both observable results and later mutation.
%% Lower PeTTa named states to a file-local atomspace-backed compatibility
%% surface instead of relying on HE's native StateMonad representation.
translate_term_mode(Mode, ['bind!', Ref, ['new-state', Init]],
                    [SetFun, TRef, TInit]) :-
    petta_state_set_fun(SetFun),
    translate_term_mode(Mode, Ref, TRef),
    translate_term_mode(Mode, Init, TInit), !.

translate_term_mode(Mode, ['change-state!', Ref, Value],
                    [SetFun, TRef, TValue]) :-
    petta_state_set_fun(SetFun),
    translate_term_mode(Mode, Ref, TRef),
    translate_term_mode(Mode, Value, TValue), !.

translate_term_mode(Mode, ['get-state', Ref], [GetFun, TRef]) :-
    petta_state_get_fun(GetFun),
    translate_term_mode(Mode, Ref, TRef), !.

%% Standalone PeTTa `(new-state value)` is not a constructor call in PeTTa's
%% runtime; outside `bind!` it behaves as ordinary expression data. Use the
%% existing quoted-syntax helper so HE does not allocate a native state handle.
translate_term_mode(Mode, ['new-state', Init],
                    [QuoteFun, [quote, ['new-state', TInit]]]) :-
    quoted_syntax_fun(QuoteFun),
    translate_term_mode(Mode, Init, TInit), !.

%% PeTTa length(collapse Expr)
%%   → let $tuple (collapse Expr') (size-atom $tuple)
%%
%% This is the critical high-volume PeTTa pattern. Lower it directly to the
%% CeTTa shape that counts collapsed result tuples without relying on a generic
%% user-level wrapper around eval, which is fragile on very large tuples.
translate_term_mode(Mode, [length, [collapse, Expr]],
               [let, TupleVar, [collapse, TExpr], ['size-atom', TupleVar]]) :-
    translate_term_mode(Mode, Expr, TExpr),
    fresh_var(tuple, TupleVar), !.

%% PeTTa length Expr
%%   → length Expr'
%%
%% Keep the source head intact for the remaining non-collapse cases and provide
%% a tiny compatibility definition at the file/program level when needed.
translate_term_mode(Mode, [length, Expr], [length, TExpr]) :-
    translate_term_mode(Mode, Expr, TExpr), !.

translate_term_mode(Mode, [test, [msort, [collapse, Actual]], Expected],
               [TestBag, TActual, TExpected]) :-
    \+ source_program_defines_fun(test),
    \+ source_program_defines_fun(msort),
    \+ petta_he_profile_mode(Mode),
    petta_test_bag_fun(TestBag),
    translate_term_mode(Mode, Actual, TActual),
    translate_term_mode(Mode, Expected, TExpected), !.

translate_term_mode(Mode, [test, [collapse, Actual], Expected],
               [TestBag, TActual, TExpected]) :-
    \+ source_program_defines_fun(test),
    \+ petta_he_profile_mode(Mode),
    test_call_needs_bag_equality([collapse, Actual]),
    petta_test_bag_fun(TestBag),
    translate_term_mode(Mode, Actual, TActual),
    translate_term_mode(Mode, Expected, TExpected), !.

%% PeTTa test Actual Expected
%%   → test Actual' Expected'
%%
%% Keep observable source test behavior intact. File/program translation
%% prepends a small HE definition when the source uses the builtin test.
translate_term_mode(Mode, [test, Actual, Expected],
               [test, TActual, TExpected]) :-
    translate_term_mode(Mode, Actual, TActual),
    translate_term_mode(Mode, Expected, TExpected), !.

%% PeTTa-native multiset sort
%%   PeTTa HE profile -> msort Expr'
%%   source-defined msort/1 -> user function call
%%   pure/extended lanes without a source definition -> explicit translation error
%%
%% PeTTa's `msort` depends on host/runtime term ordering. HE core has no
%% specified order over arbitrary atoms, so silently preserving it would make a
%% backend-agnostic translation look more portable than it is.
translate_term_mode(Mode, [msort, Expr], [msort, TExpr]) :-
    petta_he_profile_mode(Mode),
    translate_term_mode(Mode, Expr, TExpr), !.
translate_term_mode(Mode, [msort, Expr], [msort, TExpr]) :-
    tr_source_fun_arity(msort, 1),
    translate_term_mode(Mode, Expr, TExpr), !.
translate_term_mode(Mode, [msort, _], _) :-
    throw_unsupported_petta_native_for_he_core(Mode, msort, translate_term_mode/3).

%% PeTTa cut
%%   PeTTa HE profile -> cut
%%   pure/extended lanes -> explicit translation error
%%
%% `cut` is scoped search control.  Unlike `once`, it cannot be reduced to a
%% local first-result expression without changing the surrounding search tree.
translate_term_mode(Mode, [cut], [cut]) :-
    petta_he_profile_mode(Mode), !.
translate_term_mode(Mode, [cut], _) :-
    throw_unsupported_cut_for_he_core(Mode, translate_term_mode/3).

%% PeTTa once Expr
%%   pure lane       -> first result via collapse/case/decons-atom
%%   extended lane   -> select 1 Expr'
%%   PeTTa HE profile -> once Expr'
%%
%% `select` is not upstream HE core, so default translation uses only HE-core
%% surfaces. The explicit extended and PeTTa-profile modes keep their native
%% committed-choice forms.
translate_term_mode(Mode, [once, Expr], [once, TExpr]) :-
    petta_he_profile_mode(Mode),
    translate_term_mode(Mode, Expr, TExpr), !.
translate_term_mode(Mode, [once, Expr], [select, 1, TExpr]) :-
    he_extended_mode(Mode),
    translate_term_mode(Mode, Expr, TExpr), !.
translate_term_mode(Mode, [once, Expr], ['singleton-visible-witness', TExpr]) :-
    pure_once_surface_mode(Mode),
    singleton_visible_witness_source_expr(Expr),
    normalize_singleton_visible_witness_term(Expr, NormExpr),
    translate_term_mode(Mode, NormExpr, TExpr), !.
translate_term_mode(Mode, [once, Expr], TExpr) :-
    translate_term_mode(Mode, Expr, TExpr0),
    pure_once_lowering(TExpr0, TExpr), !.

%% Finite existence-only search check
%%   == () (collapse (once (match Space Pattern Body)))
%%
%% This is the narrow portable fragment behind duplicate-suppression and
%% existence-gated effect families such as peano/matespace.  Keep the lowering
%% explicit and canonical so downstream runtimes can recognize the pure HE
%% shape without mistaking it for a broader first-witness contract.
translate_term_mode(Mode, ['==', Left, Right], TExpr) :-
    finite_exists_match_empty_surface(Left, Right, MatchExpr), !,
    translate_term_mode(Mode, [once, MatchExpr], TOnce),
    finite_exists_match_empty_lowering(TOnce, TExpr).

%% Canonical PeTTa single-result idiom:
%%   let* (($x Goal)
%%         ($tmp (cut)))
%%     Body
%%
%% When the cut binding is not observed, this is just once(Goal) with the
%% chosen result bound to $x. Lower that tractable shape before the generic
%% cut rejection so pure HE translation can keep working on examples such as
%% matchsingle/cut without pretending that arbitrary cut is portable.
translate_term_mode(Mode, ['let*', [[Var, Goal], [CutVar, [cut]]], Var], TExpr) :-
    \+ petta_he_profile_mode(Mode),
    CutVar \== Var,
    translate_term_mode(Mode, [once, Goal], TExpr), !.
translate_term_mode(Mode, ['let*', [[Var, Goal], [CutVar, [cut]]], Body], TExpr) :-
    \+ petta_he_profile_mode(Mode),
    CutVar \== Var,
    \+ term_mentions_atom(Body, CutVar),
    translate_term_mode(Mode, [let, Var, [once, Goal], Body], TExpr), !.

translate_term_mode(Mode, ['let*', Bindings, Body], ['let*', TBindings, TBody]) :-
    petta_he_profile_mode(Mode),
    translate_let_bindings_mode(Mode, Bindings, TBindings),
    translate_term_mode(Mode, Body, TBody), !.

translate_term_mode(Mode, ['let*', Bindings, Body], ['let*', TBindings, TBody]) :-
    rawify_pattern_bound_bindings([], Bindings, RawBindings, BodyVars),
    rawify_pattern_bound_body(BodyVars, Body, RawBody),
    translate_let_bindings_mode(Mode, RawBindings, TBindings),
    translate_term_mode(Mode, RawBody, TBody), !.

%% trusted HE→PeTTa new-space lowering reversal
translate_term_mode(Mode, [call, [gensym, Prefix]], ['new-space']) :-
    trusted_mode(Mode),
    trusted_new_space_prefix(Prefix), !.

translate_term_mode(Mode, [call, Expr], TExpr) :-
    translate_call_like_mode(Mode, Expr, TExpr0),
    force_runtime_helper_value(runtime_call, TExpr0, TExpr), !.

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

translate_term_mode(Mode, [Head|Args], TExpr) :-
    tr_member_filter_fun(Head, RetPos, TuplePos),
    \+ petta_he_profile_mode(Mode),
    nth1(RetPos, Args, ValueArg),
    nth1(TuplePos, Args, TupleArg),
    fresh_var(member_value, ValueVar),
    translate_term_mode(Mode, ValueArg, TValue),
    translate_term_mode(Mode, TupleArg, TTuple),
    TExpr = [let, ValueVar, TValue,
             [let, 'True', ['is-member', ValueVar, TTuple], ValueVar]],
    !.

translate_term_mode(Mode, [Head|Args], [Head|TArgs]) :-
    raw_expr_data_quote_mode(Mode),
    expr_data_fun_positions(Head, QuotePositions),
    translate_args_with_quote_positions(Mode, Args, QuotePositions, TArgs), !.

translate_term_mode(Mode, [let, Pattern, Observed, Body], TExpr) :-
    ffi_tokens_mode(Mode),
    function_call_inversion_surface(let_pattern, Pattern, Observed, extended_witness,
                                    arithmetic_append_suffix(_PrefixElems, _TailSourceVar)),
    function_call_inversion_bound_vars(Pattern, BoundVars),
    rawify_function_call_inversion_body(BoundVars, Body, RawBody),
    petta_ffi_function_call_inversion_fun(OracleFun),
    translate_term_mode(Mode, Observed, TObserved),
    translate_term_mode(Mode, RawBody, TContinuation),
    TExpr = [OracleFun, 'arithmetic-append-suffix', [quote, Pattern], TObserved, TContinuation],
    !.

translate_term_mode(Mode, [let, Pattern, Observed, Body], TExpr) :-
    function_call_inversion_surface(let_pattern, Pattern, Observed, pure,
                                    append_suffix(PrefixElems, TailSourceVar)),
    function_call_inversion_bound_vars(Pattern, BoundVars),
    rawify_function_call_inversion_body(BoundVars, Body, RawBody),
    build_structural_decons_guard(PrefixElems, Observed, TailSourceVar,
                                  RawBody, Wrapped),
    translate_term_mode(Mode, Wrapped, TExpr),
    !.

translate_term_mode(Mode, [let, Pattern, Observed, _Body], _) :-
    \+ petta_he_profile_mode(Mode),
    function_call_inversion_surface(let_pattern, Pattern, Observed, extended_witness,
                                    arithmetic_append_suffix(_PrefixElems, _TailSourceVar)),
    throw_unsupported_arithmetic_inversion_for_he_core(Mode, translate_term_mode/3).

translate_term_mode(Mode, [let, Pattern, Observed, Body],
                    [let, TPattern, TObserved, TBody]) :-
    function_call_inversion_surface(let_pattern, Pattern, Observed, _Lane, _Spec),
    function_call_inversion_bound_vars(Pattern, BoundVars),
    rawify_function_call_inversion_body(BoundVars, Body, RawBody),
    translate_pattern_mode(Mode, Pattern, TPattern),
    translate_term_mode(Mode, Observed, TObserved),
    translate_term_mode(Mode, RawBody, TBody),
    !.

translate_term_mode(Mode, [let, Pattern, Observed, Body],
                    [let, TPattern, TObserved, TBody]) :-
    petta_he_profile_mode(Mode),
    translate_pattern_mode(Mode, Pattern, TPattern),
    translate_term_mode(Mode, Observed, TObserved),
    translate_term_mode(Mode, Body, TBody),
    !.

translate_term_mode(Mode, [let, Pattern, Observed, Body],
                    [let, TPattern, TObserved, TBody]) :-
    pattern_bound_source_variables(Pattern, BoundVars),
    rawify_pattern_bound_body(BoundVars, Body, RawBody),
    translate_pattern_mode(Mode, Pattern, TPattern),
    translate_term_mode(Mode, Observed, TObserved),
    translate_term_mode(Mode, RawBody, TBody),
    !.

translate_term_mode(Mode, [lambda, Params, Body], [lambda, TParams, TBody]) :-
    petta_he_profile_mode(Mode),
    translate_pattern_mode(Mode, Params, TParams),
    translate_term_mode(Mode, Body, TBody),
    !.

translate_term_mode(Mode, [lambda, Params, Body], [lambda, TParams, TBody]) :-
    pattern_bound_source_variables(Params, ParamVars),
    rawify_pattern_bound_body(ParamVars, Body, RawBody),
    translate_pattern_mode(Mode, Params, TParams),
    translate_term_mode(Mode, RawBody, TBody),
    !.

translate_term_mode(Mode, ['|->', Params, Body], ['|->', TParams, TBody]) :-
    petta_he_profile_mode(Mode),
    translate_pattern_mode(Mode, Params, TParams),
    translate_term_mode(Mode, Body, TBody),
    !.

translate_term_mode(Mode, ['|->', Params, Body], TExpr) :-
    translate_nested_lambda_mode(Mode, Params, Body, TExpr), !.

translate_term_mode(Mode, ['|->', Params, Body], ['|->', TParams, TBody]) :-
    pattern_bound_source_variables(Params, ParamVars),
    rawify_pattern_bound_body(ParamVars, Body, RawBody),
    translate_pattern_mode(Mode, Params, TParams),
    translate_term_mode(Mode, RawBody, TBody),
    !.

translate_term_mode(Mode, ['__tr-raw-apply1', Head, Arg], TExpr) :-
    translate_term_mode(Mode, Head, THead),
    translate_term_mode(Mode, Arg, TArg),
    atom_subst_apply_term(THead, [TArg], TExpr),
    !.

translate_term_mode(Mode, ['__tr-raw-apply', Head|Args], TExpr) :-
    Args \= [],
    translate_term_mode(Mode, Head, THead),
    translate_term_list_mode(Mode, Args, TArgs),
    atom_subst_apply_term(THead, TArgs, TExpr),
    !.

translate_term_mode(Mode, [case, Scrutinee, Branches], [case, TScrutinee, TBranches]) :-
    translate_term_mode(Mode, Scrutinee, TScrutinee),
    translate_case_branches_mode(Mode, Branches, TBranches),
    !.

translate_term_mode(Mode, [Head], ['cons-atom', THead, '()']) :-
    source_variable_atom(Head),
    \+ petta_he_profile_mode(Mode),
    translate_term_mode(Mode, Head, THead), !.
translate_term_mode(Mode, [Head|Args], [Head|TArgs]) :-
    petta_he_profile_mode(Mode),
    source_variable_atom(Head),
    translate_term_list_mode(Mode, Args, TArgs), !.
translate_term_mode(Mode, [Head|Args], [THead|TArgs]) :-
    source_variable_atom(Head),
    \+ petta_he_profile_mode(Mode),
    Args \= [],
    translate_term_mode(Mode, Head, THead),
    translate_term_list_mode(Mode, Args, TArgs), !.
translate_term_mode(Mode, [Head|Args], TExpr) :-
    is_list(Head),
    Args \= [],
    expression_head_needs_curried_application(Head),
    translate_curried_application_mode(Mode, Head, Args, TExpr), !.
translate_term_mode(Mode, [Head|Args], [THead|TArgs]) :-
    raw_expr_data_quote_mode(Mode),
    is_list(Head),
    Args \= [],
    translate_data_tuple_element_mode(Mode, Head, THead),
    translate_data_tuple_element_list_mode(Mode, Args, TArgs), !.
translate_term_mode(Mode, [Head|Args], [THead|TArgs]) :-
    is_list(Head),
    Args \= [],
    translate_term_mode(Mode, Head, THead),
    translate_term_list_mode(Mode, Args, TArgs), !.

%% PeTTa applies first-class callables left-associatively:
%%   ($f a b) → (($f a) b)
%%   (mp 1 1) → (((mp) 1) 1) when mp returns a callable value
translate_term_mode(Mode, [Head|Args], TExpr) :-
    Args \= [],
    needs_curried_application(Head, Args),
    translate_curried_application_mode(Mode, Head, Args, TExpr), !.

%% ── Recursive traversal ─────────────────────────────────────────

%% PeTTa accepts lowercase boolean atoms in examples; HE profiles use the
%% standard True/False boolean constructors.
translate_term_mode(_, true, 'True') :- !.
translate_term_mode(_, false, 'False') :- !.

%% Lists: translate each element
translate_term_mode(Mode, List, TList) :-
    is_list(List),
    maplist(translate_term_mode(Mode), List, TList), !.

%% Atoms: identity
translate_term_mode(_, X, X) :- \+ is_list(X).

translate_case_branches_mode(_, [], []).
translate_case_branches_mode(Mode, [[Pattern, Body]|Rest], [[TPattern, TBody]|TRest]) :-
    petta_he_profile_mode(Mode),
    translate_pattern_mode(Mode, Pattern, TPattern),
    translate_term_mode(Mode, Body, TBody),
    translate_case_branches_mode(Mode, Rest, TRest).
translate_case_branches_mode(Mode, [[Pattern, Body]|Rest], [[TPattern, TBody]|TRest]) :-
    pattern_bound_source_variables(Pattern, PatternVars),
    rawify_pattern_bound_body(PatternVars, Body, RawBody),
    translate_pattern_mode(Mode, Pattern, TPattern),
    translate_term_mode(Mode, RawBody, TBody),
    translate_case_branches_mode(Mode, Rest, TRest).

translate_pattern_mode(_, true, 'True') :- !.
translate_pattern_mode(_, false, 'False') :- !.
translate_pattern_mode(Mode, [quote, Expr], [quote, Expr]) :-
    raw_expr_data_quote_mode(Mode),
    !.
translate_pattern_mode(Mode, List, TList) :-
    is_list(List),
    !,
    maplist(translate_pattern_mode(Mode), List, TList).
translate_pattern_mode(_, X, X).

translate_let_bindings_mode(_Mode, [], []).
translate_let_bindings_mode(Mode, [[Pattern, Value]|Rest], [[TPattern, TValue]|TRest]) :-
    translate_pattern_mode(Mode, Pattern, TPattern),
    translate_term_mode(Mode, Value, TValue),
    translate_let_bindings_mode(Mode, Rest, TRest).

%% ── Program-level translation ───────────────────────────────────

normalize_function_head_decl(['=', [Head|Args], RHS],
                             ['=', [Head|NormArgs], GuardedRHS]) :-
    atom(Head),
    Args \= [],
    head_args_need_normalization(Args),
    normalize_head_args(Args, [], [], NormArgs, GuardSpecs, Substs),
    GuardSpecs \= [],
    apply_source_substitutions(Substs, RHS, RSub),
    wrap_head_pattern_guards(GuardSpecs, RSub, GuardedRHS).

head_args_need_normalization(Args) :-
    \+ head_args_are_distinct_source_vars(Args).

head_args_are_distinct_source_vars(Args) :-
    maplist(source_variable_atom, Args),
    sort(Args, Unique),
    length(Args, Count),
    length(Unique, Count).

normalize_head_args([], Seen, Substs, [], [], Substs) :-
    Seen = Seen.
normalize_head_args([Arg0|Args], Seen0, Substs0, [NormArg|NormArgs], Guards,
                    SubstsOut) :-
    apply_source_substitutions(Substs0, Arg0, Arg),
    normalize_head_arg(Arg, Seen0, Seen1, NormArg, Guard, NewSubsts),
    append(Substs0, NewSubsts, Substs1),
    normalize_head_args(Args, Seen1, Substs1, NormArgs, RestGuards, SubstsOut),
    prepend_head_guard(Guard, RestGuards, Guards).

normalize_head_arg(Arg, Seen0, [Arg|Seen0], Arg, none, []) :-
    source_variable_atom(Arg),
    \+ memberchk(Arg, Seen0),
    !.
normalize_head_arg(Arg, Seen, Seen, Fresh, unify_guard(Fresh, Arg), []) :-
    source_variable_atom(Arg),
    memberchk(Arg, Seen),
    fresh_var(head_arg, Fresh),
    !.
normalize_head_arg(Arg, Seen, Seen, Fresh, Guard, Substs) :-
    fresh_var(head_arg, Fresh),
    head_arg_guard(Arg, Fresh, Guard, Substs).

function_call_inversion_capability(pure, [Functor|ActualArgs],
                                   append_suffix(PrefixElems, TailSourceVar)) :-
    atom(Functor),
    source_fun_structural_append_suffix_prefix(Functor, ActualArgs,
                                               PrefixElems, TailSourceVar).
function_call_inversion_capability(extended_witness, [Functor|ActualArgs],
                                   arithmetic_append_suffix(PrefixElems, TailSourceVar)) :-
    atom(Functor),
    source_fun_symbolic_append_suffix_prefix(Functor, ActualArgs,
                                             PrefixElems, TailSourceVar),
    prefix_elems_need_arithmetic_witness(PrefixElems).
function_call_inversion_capability(extended_witness, [Functor|ActualArgs],
                                   append_suffix_with_free_prefix(PrefixElems, TailSourceVar)) :-
    atom(Functor),
    source_fun_symbolic_append_suffix_prefix(Functor, ActualArgs,
                                             PrefixElems, TailSourceVar),
    \+ prefix_elems_need_arithmetic_witness(PrefixElems),
    term_has_free_source_variable(PrefixElems).
function_call_inversion_capability(extended_witness, [Functor|_ActualArgs],
                                   source_defined_fun(Functor)) :-
    atom(Functor),
    source_defined_head_fun(Functor).

function_call_inversion_surface(head_pattern, Call, _Observed, Lane, Spec) :-
    is_list(Call),
    function_call_inversion_capability(Lane, Call, Spec).
function_call_inversion_surface(eq_guard, Call, Observed, Lane, Spec) :-
    source_variable_atom(Observed),
    is_list(Call),
    function_call_inversion_capability(Lane, Call, Spec).
function_call_inversion_surface(let_pattern, Pattern, _Observed, Lane, Spec) :-
    is_list(Pattern),
    function_call_inversion_capability(Lane, Pattern, Spec).

head_arg_guard(Arg, Fresh, member_filter_guard(Tuple, Fresh, Candidate), Substs) :-
    Arg = [Functor|Args],
    tr_member_filter_fun(Functor, RetPos, TuplePos),
    nth1(RetPos, Args, Var),
    source_variable_atom(Var),
    nth1(TuplePos, Args, Tuple),
    fresh_var(head_candidate, Candidate),
    head_arg_candidate_substitutions(Arg, Candidate, Substs),
    !.
head_arg_guard(Arg, Fresh, structural_decons_guard(Fresh, PrefixElems, TailVar), Substs) :-
    function_call_inversion_surface(head_pattern, Arg, Fresh, pure,
                                    append_suffix(PrefixElems, TailSourceVar)),
    fresh_var(head_suffix, TailVar),
    Substs = [TailSourceVar-TailVar],
    !.
head_arg_guard(Arg, Fresh, generated_guard(Arg, Fresh, Candidate), Substs) :-
    function_call_inversion_surface(head_pattern, Arg, Fresh, extended_witness,
                                    source_defined_fun(_Functor)),
    fresh_var(head_candidate, Candidate),
    head_arg_candidate_substitutions(Arg, Candidate, Substs),
    !.
head_arg_guard(Arg, Fresh, unify_guard(Fresh, Arg), []).

source_defined_head_fun(Functor) :-
    tr_source_fun_arity(Functor, _).

source_fun_structural_append_suffix_prefix(Functor, ActualArgs,
                                           PrefixElems, TailSourceVar) :-
    findall(Prefix-TailVar,
            append_suffix_call_shape(Functor, ActualArgs, structural,
                                     Prefix, TailVar),
            RawSpecs),
    sort(RawSpecs, [PrefixElems-TailSourceVar]).

source_fun_symbolic_append_suffix_prefix(Functor, ActualArgs,
                                         PrefixElems, TailSourceVar) :-
    findall(Prefix-TailVar,
            append_suffix_call_shape(Functor, ActualArgs, symbolic,
                                     Prefix, TailVar),
            RawSpecs),
    sort(RawSpecs, [PrefixElems-TailSourceVar]).

append_suffix_call_shape(Functor, ActualArgs, Flavor, PrefixElems, TailSourceVar) :-
    tr_source_fun_clause(Functor, FormalArgs, RHS),
    same_length(FormalArgs, ActualArgs),
    formal_actual_substitutions(FormalArgs, ActualArgs, FormalSubsts),
    append_suffix_segments(RHS, Segments0),
    apply_source_substitutions(FormalSubsts, Segments0, Segments),
    segments_prefix_and_tail_var(Flavor, Segments, PrefixElems, TailSourceVar).

formal_actual_substitutions([], [], []).
formal_actual_substitutions([Formal|Formals], [Actual|Actuals], [Formal-Actual|Rest]) :-
    source_variable_atom(Formal),
    !,
    formal_actual_substitutions(Formals, Actuals, Rest).
formal_actual_substitutions([_|Formals], [_|Actuals], Rest) :-
    formal_actual_substitutions(Formals, Actuals, Rest).

append_suffix_segments([append, Left, Right], Segments) :-
    append_suffix_segments(Left, LeftSegs),
    append_suffix_segments(Right, RightSegs),
    append(LeftSegs, RightSegs, Segments),
    !.
append_suffix_segments(Segment, [Segment]) :-
    source_variable_atom(Segment),
    !.
append_suffix_segments(Segment, [Segment]) :-
    source_nil(Segment),
    !.
append_suffix_segments(Segment, [Segment]) :-
    is_list(Segment),
    !.

segments_prefix_and_tail_var(Flavor, Segments, PrefixElems, TailSourceVar) :-
    append(PrefixSegments, [TailSourceVar], Segments),
    PrefixSegments \= [],
    source_variable_atom(TailSourceVar),
    prefix_segment_mapper(Flavor, Mapper),
    maplist(Mapper, PrefixSegments, PrefixLists),
    append(PrefixLists, PrefixElems),
    PrefixElems \= [].

prefix_segment_mapper(structural, prefix_segment_structural_elems).
prefix_segment_mapper(symbolic, prefix_segment_symbolic_elems).

prefix_segment_structural_elems(Segment, []) :-
    source_nil(Segment),
    !.
prefix_segment_structural_elems(Segment, Elems) :-
    is_list(Segment),
    maplist(structural_prefix_elem, Segment),
    Elems = Segment.

prefix_segment_symbolic_elems(Segment, []) :-
    source_nil(Segment),
    !.
prefix_segment_symbolic_elems(Segment, Elems) :-
    is_list(Segment),
    Elems = Segment.

structural_prefix_elem(Elem) :-
    source_variable_atom(Elem),
    !.
structural_prefix_elem(Elem) :-
    \+ term_contains_source_var(Elem).

term_contains_source_var(Term) :-
    source_variable_atom(Term),
    !.
term_contains_source_var(Term) :-
    is_list(Term),
    member(Subterm, Term),
    term_contains_source_var(Subterm).

prefix_elems_need_arithmetic_witness(PrefixElems) :-
    member(PrefixElem, PrefixElems),
    term_has_clp_arith_call(PrefixElem),
    !.

term_has_clp_arith_call(Term) :-
    is_list(Term),
    Term = [Head|Args],
    clp_arithmetic_fun(Head),
    Args \= [],
    !.
term_has_clp_arith_call(Term) :-
    is_list(Term),
    member(Subterm, Term),
    term_has_clp_arith_call(Subterm).

clp_arithmetic_fun('#+').
clp_arithmetic_fun('#-').
clp_arithmetic_fun('#*').
clp_arithmetic_fun('#div').
clp_arithmetic_fun('#//').
clp_arithmetic_fun('#mod').
clp_arithmetic_fun('#min').
clp_arithmetic_fun('#max').

head_arg_candidate_substitutions([Functor|Args], Candidate, [Var-Candidate]) :-
    tr_source_return_arg(Functor, Pos),
    nth1(Pos, Args, Var),
    source_variable_atom(Var),
    !.
head_arg_candidate_substitutions(_, _, []).

apply_source_substitutions([], Term, Term).
apply_source_substitutions(Substs, Term0, Term) :-
    source_variable_atom(Term0),
    !,
    (   memberchk(Term0-Term, Substs)
    ->  true
    ;   Term = Term0
    ).
apply_source_substitutions(_, [quote, Expr], [quote, Expr]) :- !.
apply_source_substitutions(Substs, List0, List) :-
    is_list(List0),
    !,
    maplist(apply_source_substitutions(Substs), List0, List).
apply_source_substitutions(_, Term, Term).

prepend_head_guard(none, Guards, Guards) :- !.
prepend_head_guard(Guard, Guards, [Guard|Guards]).

wrap_head_pattern_guards([], RHS, RHS).
wrap_head_pattern_guards([Guard|Guards], RHS0, Wrapped) :-
    wrap_head_pattern_guards(Guards, RHS0, Inner),
    wrap_head_pattern_guard(Guard, Inner, Wrapped).

wrap_head_pattern_guard(unify_guard(Actual, Pattern), RHS,
                        [unify, Actual, Pattern, RHS, 'Empty']).
wrap_head_pattern_guard(member_filter_guard(Tuple, Actual, Candidate), RHS,
                        [let, Candidate, [superpose, Tuple],
                         [unify, Candidate, Actual, RHS, 'Empty']]).
wrap_head_pattern_guard(structural_decons_guard(Actual, PrefixElems, TailVar), RHS,
                        Wrapped) :-
    build_structural_decons_guard(PrefixElems, Actual, TailVar, RHS, Wrapped).
wrap_head_pattern_guard(generated_guard(Expr, Actual, Candidate), RHS,
                        [chain, Expr, Candidate,
                         [unify, Candidate, Actual, RHS, 'Empty']]).

build_structural_decons_guard([], Actual, TailVar, RHS, [let, TailVar, Actual, FinalRHS]) :-
    structural_tail_rhs(TailVar, RHS, FinalRHS).
build_structural_decons_guard([PrefixElem|Rest], Actual, TailVar, RHS,
                              [chain, ['decons-atom', Actual], PairVar,
                               [let, HeadVar, ['first-from-pair', PairVar],
                                [let, TailExpr, ['second-from-pair', PairVar],
                                 [unify, HeadVar, PrefixElem, Inner, 'Empty']]]]) :-
    fresh_var(head_pair, PairVar),
    fresh_var(head_elem, HeadVar),
    fresh_var(head_tail, TailExpr),
    build_structural_decons_guard(Rest, TailExpr, TailVar, RHS, Inner).

structural_tail_rhs(TailVar, [TailVar, Arg], ['__tr-raw-apply1', TailVar, Arg]) :-
    !.
structural_tail_rhs(_, RHS, RHS).

normalize_function_call_inversion_decl(['=', [Head|Args], RHS],
                                       ['=', [Head|NormArgs], Then]) :-
    equality_function_call_inversion_surface(Args, RHS, Observed, Call, Then),
    function_call_inversion_surface(eq_guard, Call, Observed, _Lane, _Spec),
    \+ term_mentions_atom(Then, Observed),
    replace_exact_head_arg(Args, Observed, Call, NormArgs).

equality_function_call_inversion_surface(Args, [if, ['=', Observed, Call], Then, Else],
                                         Observed, Call, Then) :-
    source_variable_atom(Observed),
    source_empty_term(Else),
    occurs_once_in_list(Observed, Args).
equality_function_call_inversion_surface(Args, [if, ['=', Call, Observed], Then, Else],
                                         Observed, Call, Then) :-
    source_variable_atom(Observed),
    source_empty_term(Else),
    occurs_once_in_list(Observed, Args).

source_empty_term([empty]).

occurs_once_in_list(Term, List) :-
    include(==(Term), List, Matches),
    Matches = [_].

function_call_inversion_bound_vars(Term, Vars) :-
    findall(Var, term_source_var(Term, Var), Vars0),
    sort(Vars0, Vars).

term_source_var(Term, Term) :-
    atom(Term),
    source_variable_atom(Term),
    !.
term_source_var(Term, Var) :-
    is_list(Term),
    member(Subterm, Term),
    term_source_var(Subterm, Var).

rawify_function_call_inversion_body(BoundVars, [quote, Expr], [quote, Expr]) :-
    BoundVars = BoundVars,
    !.
rawify_function_call_inversion_body(BoundVars, [let, Binder, Value, Body],
                                    [let, Binder, RawValue, RawBody]) :-
    !,
    rawify_function_call_inversion_body(BoundVars, Value, RawValue),
    function_call_inversion_bound_vars(Binder, BinderVars),
    subtract(BoundVars, BinderVars, BodyVars),
    rawify_function_call_inversion_body(BodyVars, Body, RawBody).
rawify_function_call_inversion_body(BoundVars, ['let*', Bindings, Body],
                                    ['let*', RawBindings, RawBody]) :-
    !,
    rawify_function_call_inversion_bindings(BoundVars, Bindings, RawBindings, BodyVars),
    rawify_function_call_inversion_body(BodyVars, Body, RawBody).
rawify_function_call_inversion_body(BoundVars, [case, Expr, Branches],
                                    [case, RawExpr, RawBranches]) :-
    !,
    rawify_function_call_inversion_body(BoundVars, Expr, RawExpr),
    rawify_function_call_inversion_branches(BoundVars, Branches, RawBranches).
rawify_function_call_inversion_body(BoundVars, [Head|Args], RawApply) :-
    source_variable_atom(Head),
    memberchk(Head, BoundVars),
    !,
    rawify_function_call_inversion_list(BoundVars, Args, RawArgs),
    build_raw_function_call_inversion_apply(Head, RawArgs, RawApply).
rawify_function_call_inversion_body(BoundVars, List, RawList) :-
    is_list(List),
    !,
    rawify_function_call_inversion_list(BoundVars, List, RawList).
rawify_function_call_inversion_body(_, Term, Term).

rawify_function_call_inversion_list(_, [], []).
rawify_function_call_inversion_list(BoundVars, [Term|Rest], [RawTerm|RawRest]) :-
    rawify_function_call_inversion_body(BoundVars, Term, RawTerm),
    rawify_function_call_inversion_list(BoundVars, Rest, RawRest).

rawify_function_call_inversion_branches(_, [], []).
rawify_function_call_inversion_branches(BoundVars, [[Pattern, Body]|Rest],
                                        [[Pattern, RawBody]|RawRest]) :-
    function_call_inversion_bound_vars(Pattern, PatternVars),
    subtract(BoundVars, PatternVars, BranchVars),
    rawify_function_call_inversion_body(BranchVars, Body, RawBody),
    rawify_function_call_inversion_branches(BoundVars, Rest, RawRest).

rawify_function_call_inversion_bindings(BoundVars, [], [], BoundVars).
rawify_function_call_inversion_bindings(BoundVars, [[Binder, Value]|Rest],
                                        [[Binder, RawValue]|RawRest], FinalVars) :-
    rawify_function_call_inversion_body(BoundVars, Value, RawValue),
    function_call_inversion_bound_vars(Binder, BinderVars),
    subtract(BoundVars, BinderVars, NextVars),
    rawify_function_call_inversion_bindings(NextVars, Rest, RawRest, FinalVars).

rawify_pattern_bound_body(BoundVars, [quote, Expr], [quote, Expr]) :-
    BoundVars = BoundVars,
    !.
rawify_pattern_bound_body(BoundVars, [let, Binder, Value, Body],
                          [let, Binder, RawValue, RawBody]) :-
    !,
    rawify_pattern_bound_body(BoundVars, Value, RawValue),
    pattern_bound_source_variables(Binder, BinderVars),
    append(BinderVars, BoundVars, NextVars0),
    sort(NextVars0, NextVars),
    rawify_pattern_bound_body(NextVars, Body, RawBody).
rawify_pattern_bound_body(BoundVars, ['let*', Bindings, Body],
                          ['let*', RawBindings, RawBody]) :-
    !,
    rawify_pattern_bound_bindings(BoundVars, Bindings, RawBindings, FinalVars),
    rawify_pattern_bound_body(FinalVars, Body, RawBody).
rawify_pattern_bound_body(BoundVars, [lambda, Params, Body],
                          [lambda, Params, RawBody]) :-
    !,
    pattern_bound_source_variables(Params, ParamVars),
    append(ParamVars, BoundVars, NextVars0),
    sort(NextVars0, NextVars),
    rawify_pattern_bound_body(NextVars, Body, RawBody).
rawify_pattern_bound_body(BoundVars, ['|->', Params, Body],
                          ['|->', Params, RawBody]) :-
    !,
    pattern_bound_source_variables(Params, ParamVars),
    append(ParamVars, BoundVars, NextVars0),
    sort(NextVars0, NextVars),
    rawify_pattern_bound_body(NextVars, Body, RawBody).
rawify_pattern_bound_body(BoundVars, [case, Expr, Branches],
                          [case, RawExpr, RawBranches]) :-
    !,
    rawify_pattern_bound_body(BoundVars, Expr, RawExpr),
    rawify_pattern_bound_branches(BoundVars, Branches, RawBranches).
rawify_pattern_bound_body(BoundVars, [Head|Args], [Head|RawArgs]) :-
    source_variable_atom(Head),
    memberchk(Head, BoundVars),
    !,
    rawify_pattern_bound_list(BoundVars, Args, RawArgs).
rawify_pattern_bound_body(BoundVars, List, RawList) :-
    is_list(List),
    !,
    rawify_pattern_bound_list(BoundVars, List, RawList).
rawify_pattern_bound_body(_, Term, Term).

rawify_pattern_bound_list(_, [], []).
rawify_pattern_bound_list(BoundVars, [Term|Rest], [RawTerm|RawRest]) :-
    rawify_pattern_bound_body(BoundVars, Term, RawTerm),
    rawify_pattern_bound_list(BoundVars, Rest, RawRest).

rawify_pattern_bound_branches(_, [], []).
rawify_pattern_bound_branches(BoundVars, [[Pattern, Body]|Rest],
                              [[Pattern, RawBody]|RawRest]) :-
    pattern_bound_source_variables(Pattern, PatternVars),
    append(PatternVars, BoundVars, NextVars0),
    sort(NextVars0, NextVars),
    rawify_pattern_bound_body(NextVars, Body, RawBody),
    rawify_pattern_bound_branches(BoundVars, Rest, RawRest).

rawify_pattern_bound_bindings(BoundVars, [], [], BoundVars).
rawify_pattern_bound_bindings(BoundVars, [[Binder, Value]|Rest],
                              [[Binder, RawValue]|RawRest], FinalVars) :-
    rawify_pattern_bound_body(BoundVars, Value, RawValue),
    pattern_bound_source_variables(Binder, BinderVars),
    append(BinderVars, BoundVars, NextVars0),
    sort(NextVars0, NextVars),
    rawify_pattern_bound_bindings(NextVars, Rest, RawRest, FinalVars).

build_raw_function_call_inversion_apply(Head, [], ['cons-atom', Head, '()']) :-
    !.
build_raw_function_call_inversion_apply(Head, [Arg], ['__tr-raw-apply1', Head, Arg]) :-
    !.
build_raw_function_call_inversion_apply(Head, Args, ['__tr-raw-apply', Head|Args]).

replace_exact_head_arg([Observed|Args], Observed, Call, [Call|Args]) :-
    !.
replace_exact_head_arg([Arg|Args], Observed, Call, [Arg|NormArgs]) :-
    replace_exact_head_arg(Args, Observed, Call, NormArgs).

translate_decl_mode(Mode, Decl, Out) :-
    petta_he_profile_mode(Mode),
    Decl = ['=', LHS, RHS],
    translate_term_mode(Mode, RHS, TRHS),
    Out = ['=', LHS, TRHS],
    !.

translate_decl_mode(Mode, Decl, Out) :-
    normalize_function_call_inversion_decl(Decl, Normalized),
    !,
    translate_decl_mode(Mode, Normalized, Out).

translate_decl_mode(Mode, Decl, Out) :-
    normalize_function_head_decl(Decl, Normalized),
    !,
    translate_decl_mode(Mode, Normalized, Out).

translate_decl_mode(Mode, ['=', LHS, [Head|Args]], ['=', LHS, TRHS]) :-
    \+ petta_he_profile_mode(Mode),
    LHS = [_Functor|FormalArgs],
    source_variable_atom(Head),
    memberchk(Head, FormalArgs),
    Args \= [],
    translate_callable_source_var_application_mode(Mode, Head, Args, TRHS),
    !.

translate_decl_mode(Mode, ['=', LHS, RHS], ['=', LHS, TRHS]) :-
    translate_term_mode(Mode, RHS, TRHS), !.

translate_decl_mode(_, [':', Name, Type], [':', Name, Type]) :- !.

translate_decl_mode(_, X, X).

translate_program_mode(Mode, Decls, Program) :-
    canonicalize_helper_context_decls(Decls, ContextDecls),
    with_helper_context(ContextDecls,
        ( translate_program_decl_list(Mode, Decls, TDecls0),
          rewrite_partial_builtin_value_terms(TDecls0, PartialHelperDecls, TDecls1),
          normalize_callable_equality_program(TDecls1, TDecls2),
          append(PartialHelperDecls, TDecls2, TDecls3),
          prepend_petta_compat_program_decls(Mode, ContextDecls, TDecls3, Program)
        )).

translate_program_decl_list(_, [], []).
translate_program_decl_list(Mode, Decls, [TDecl|TRest]) :-
    canonicalized_translated_decl_mode(Mode, Decls, TDecl, RestDecls),
    !,
    translate_program_decl_list(Mode, RestDecls, TRest).
translate_program_decl_list(Mode, [Decl|Rest], [TDecl|TRest]) :-
    translate_decl_mode(Mode, Decl, TDecl),
    translate_program_decl_list(Mode, Rest, TRest).

%% The PeTTa --he profile can evaluate these recursive source definitions
%% directly, so keep program-level canonicalization for the portable lanes and
%% avoid rewriting profile programs into helper-heavy pure-core shapes.
canonicalized_translated_decl_mode(Mode, _Decls, _TDecl, _RestDecls) :-
    petta_he_profile_mode(Mode),
    !,
    fail.
canonicalized_translated_decl_mode(_Mode, Decls, TDecl, RestDecls) :-
    canonicalized_translated_decl(Decls, TDecl, RestDecls).

canonicalize_helper_context_decls([], []).
canonicalize_helper_context_decls(Decls, [CanonDecl|CanonRest]) :-
    canonicalized_source_decl(Decls, CanonDecl, RestDecls),
    !,
    canonicalize_helper_context_decls(RestDecls, CanonRest).
canonicalize_helper_context_decls([Decl|Rest], [Decl|CanonRest]) :-
    canonicalize_helper_context_decls(Rest, CanonRest).

source_nil('()').
source_nil([]).

canonicalized_translated_decl(
    [['=', ['map-flat', F, Nil], Nil],
     ['=', ['map-flat', F, [cons, X, Xs]],
      [cons, [F, X], ['map-flat', F, Xs]]]
     | Rest],
    ['=', ['map-flat', F, '$list'],
     ['map-atom', '$list', '$item', [Apply1, F, '$item']]],
    Rest) :-
    source_nil(Nil),
    petta_apply1_fun(Apply1).

canonicalized_translated_decl(
    [['=', ['map-flat2', [Nil, F]], Nil],
     ['=', ['map-flat2', [[cons, X, Xs], F]],
      [cons, [F, X], ['map-flat2', [Xs, F]]]]
     | Rest],
    ['=', ['map-flat2', '$pair'],
     [let, ['$list', F], '$pair',
      ['map-atom', '$list', '$item', [Apply1, F, '$item']]]],
    Rest) :-
    source_nil(Nil),
    petta_apply1_fun(Apply1).

canonicalized_translated_decl(
    [['=', ['map-flat3', [F, Nil]], Nil],
     ['=', ['map-flat3', [F, [cons, X, Xs]]],
      [cons, [F, X], ['map-flat3', [F, Xs]]]]
     | Rest],
    ['=', ['map-flat3', '$pairq'],
     Body],
    Rest) :-
    source_nil(Nil),
    petta_apply1_fun(Apply1),
    map_flat3_exprdata_body(Apply1, F, Body).

canonicalized_translated_decl(
    [['=', ['map-flat4', [V, [F, Nil]]], Nil],
     ['=', ['map-flat4', [V, [F, [cons, X, Xs]]]],
      [cons, [F, X], ['map-flat4', [V, [F, Xs]]]]]
     | Rest],
    ['=', ['map-flat4', '$pairq'],
     Body],
    Rest) :-
    source_nil(Nil),
    petta_apply1_fun(Apply1),
    map_flat4_exprdata_body(Apply1, F, V, Body).

canonicalized_translated_decl(
    [['=', ['map-nested', F, Nil], Nil],
     ['=', ['map-nested', F, [cons, X, Xs]],
      [if, ['is-expr', X],
       [cons, ['map-nested', F, X], ['map-nested', F, Xs]],
       [cons, [F, X], ['map-nested', F, Xs]]]]
     | Rest],
    ['=', ['map-nested', F, '$list'],
     ['map-atom', '$list', '$item',
      [if, ['==', ['get-metatype', '$item'], 'Expression'],
       ['map-nested', F, '$item'],
       [Apply1, F, '$item']]]],
    Rest) :-
    source_nil(Nil),
    petta_apply1_fun(Apply1).

canonicalized_translated_decl(
    [['=', ['fold-flat', F, Init, Nil], Init],
     ['=', ['fold-flat', F, Init, [cons, X, Xs]],
      ['fold-flat', F, [F, Init, X], Xs]]
     | Rest],
    ['=', ['fold-flat', F, Init, '$list'],
     ['foldl-atom', '$list', Init, '$acc', '$item',
      [Apply2, F, '$acc', '$item']]],
    Rest) :-
    source_nil(Nil),
    petta_apply2_fun(Apply2).

canonicalized_translated_decl(
    [['=', ['fold-nested', F, Init, Nil], Init],
     ['=', ['fold-nested', F, Init, [cons, X, Xs]],
      [if, ['is-expr', X],
       ['fold-nested', F, ['fold-nested', F, Init, X], Xs],
       ['fold-nested', F, [F, Init, X], Xs]]]
     | Rest],
    ['=', ['fold-nested', F, Init, '$list'],
     ['foldl-atom', '$list', Init, '$acc', '$item',
      [if, ['==', ['get-metatype', '$item'], 'Expression'],
       ['fold-nested', F, '$acc', '$item'],
       [Apply2, F, '$acc', '$item']]]],
    Rest) :-
    source_nil(Nil),
    petta_apply2_fun(Apply2).

canonicalized_translated_decl(
    [['=', ['/==\\', A, B], ['/?\\', '==', A, B]] | Rest],
    ['=', ['/==\\', A, B],
     [let, '$intersection', ['intersection-atom', A, B], '$intersection']],
    Rest).

canonicalized_translated_decl(
    [['=', ['\\==', A, B], ['\\?', '==', A, B]] | Rest],
    ['=', ['\\==', A, B],
     [let, '$difference', ['subtraction-atom', A, B], '$difference']],
    Rest).

canonicalized_translated_decl(
    [['=', ['\\==/', A, B], ['\\?/', '==', A, B]] | Rest],
    ['=', ['\\==/', A, B],
     [let, '$difference', ['subtraction-atom', A, B],
      ['union-atom', '$difference', B]]],
    Rest).

canonicalized_translated_decl(
    [['=', ['.:', F1, F2, Arg1, Arg2], [F1, [F2, Arg1, Arg2]]] | Rest],
    ['=', ['.:', F1, F2, Arg1, Arg2], [F1, [F2, Arg1, Arg2]]],
    Rest).

map_flat3_exprdata_body(Apply1, F,
                        [let, ['$head', '$tail'], ['decons-atom', '$pairq'],
                         [if, ['==', '$head', quote],
                          QuoteBranch,
                          RawBranch]]) :-
    QuoteBranch =
        [let, ['$pair', '$quote-tail'], ['decons-atom', '$tail'],
         [let, [F, '$tail1'], ['decons-atom', '$pair'],
          [let, ['$list', '$tail2'], ['decons-atom', '$tail1'],
           ['map-atom', '$list', '$item', [Apply1, F, '$item']]]]],
    RawBranch =
        [let, [F, '$tail1'], ['decons-atom', '$pairq'],
         [let, ['$list', '$tail2'], ['decons-atom', '$tail1'],
          ['map-atom', '$list', '$item', [Apply1, F, '$item']]]].

map_flat4_exprdata_body(Apply1, F, V,
                        [let, ['$head', '$tail'], ['decons-atom', '$pairq'],
                         [if, ['==', '$head', quote],
                          QuoteBranch,
                          RawBranch]]) :-
    QuoteBranch =
        [let, ['$pair', '$quote-tail'], ['decons-atom', '$tail'],
         [let, [V, '$tail0'], ['decons-atom', '$pair'],
          [let, ['$inner', '$tailv'], ['decons-atom', '$tail0'],
           [let, [F, '$tail1'], ['decons-atom', '$inner'],
            [let, ['$list', '$tail2'], ['decons-atom', '$tail1'],
             ['map-atom', '$list', '$item', [Apply1, F, '$item']]]]]]],
    RawBranch =
        [let, [V, '$tail0'], ['decons-atom', '$pairq'],
         [let, ['$inner', '$tailv'], ['decons-atom', '$tail0'],
          [let, [F, '$tail1'], ['decons-atom', '$inner'],
           [let, ['$list', '$tail2'], ['decons-atom', '$tail1'],
            ['map-atom', '$list', '$item', [Apply1, F, '$item']]]]]].

canonicalized_source_decl(
    [['=', ['map-flat', F, Nil], Nil],
     ['=', ['map-flat', F, [cons, X, Xs]],
      [cons, [F, X], ['map-flat', F, Xs]]]
     | Rest],
    ['=', ['map-flat', F, '$list'], ['map-atom', '$list', F]],
    Rest) :-
    source_nil(Nil).

canonicalized_source_decl(
    [['=', ['map-flat2', [Nil, F]], Nil],
     ['=', ['map-flat2', [[cons, X, Xs], F]],
      [cons, [F, X], ['map-flat2', [Xs, F]]]]
     | Rest],
    ['=', ['map-flat2', '$pair'],
     [let, ['$list', F], '$pair', ['map-atom', '$list', F]]],
    Rest) :-
    source_nil(Nil).

canonicalized_source_decl(
    [['=', ['map-flat3', [F, Nil]], Nil],
     ['=', ['map-flat3', [F, [cons, X, Xs]]],
      [cons, [F, X], ['map-flat3', [F, Xs]]]]
     | Rest],
    ['=', ['map-flat3', '$pair'],
     [let, [F, '$list'], '$pair', ['map-atom', '$list', F]]],
    Rest) :-
    source_nil(Nil).

canonicalized_source_decl(
    [['=', ['map-flat4', [V, [F, Nil]]], Nil],
     ['=', ['map-flat4', [V, [F, [cons, X, Xs]]]],
      [cons, [F, X], ['map-flat4', [V, [F, Xs]]]]]
     | Rest],
    ['=', ['map-flat4', '$pair'],
     [let, [V, [F, '$list']], '$pair', ['map-atom', '$list', F]]],
    Rest) :-
    source_nil(Nil).

canonicalized_source_decl(
    [['=', ['map-nested', F, Nil], Nil],
     ['=', ['map-nested', F, [cons, X, Xs]],
      [if, ['is-expr', X],
       [cons, ['map-nested', F, X], ['map-nested', F, Xs]],
       [cons, [F, X], ['map-nested', F, Xs]]]]
     | Rest],
    ['=', ['map-nested', F, '$list'],
     ['map-atom', '$list', '$item',
      [if, ['==', ['get-metatype', '$item'], 'Expression'],
       ['map-nested', F, '$item'],
       [F, '$item']]]],
    Rest) :-
    source_nil(Nil).

canonicalized_source_decl(
    [['=', ['fold-flat', F, Init, Nil], Init],
     ['=', ['fold-flat', F, Init, [cons, X, Xs]],
      ['fold-flat', F, [F, Init, X], Xs]]
     | Rest],
    ['=', ['fold-flat', F, Init, '$list'], ['foldl-atom', '$list', Init, F]],
    Rest) :-
    source_nil(Nil).

canonicalized_source_decl(
    [['=', ['fold-nested', F, Init, Nil], Init],
     ['=', ['fold-nested', F, Init, [cons, X, Xs]],
      [if, ['is-expr', X],
       ['fold-nested', F, ['fold-nested', F, Init, X], Xs],
       ['fold-nested', F, [F, Init, X], Xs]]]
     | Rest],
    ['=', ['fold-nested', F, Init, '$list'],
     ['foldl-atom', '$list', Init, '$acc', '$item',
      [if, ['==', ['get-metatype', '$item'], 'Expression'],
       ['fold-nested', F, '$acc', '$item'],
       [F, '$acc', '$item']]]],
    Rest) :-
    source_nil(Nil).

canonicalized_source_decl(
    [['=', ['/==\\', A, B], ['/?\\', '==', A, B]] | Rest],
    ['=', ['/==\\', A, B],
     [let, '$intersection', ['intersection-atom', A, B], '$intersection']],
    Rest).

canonicalized_source_decl(
    [['=', ['\\==', A, B], ['\\?', '==', A, B]] | Rest],
    ['=', ['\\==', A, B],
     [let, '$difference', ['subtraction-atom', A, B], '$difference']],
    Rest).

canonicalized_source_decl(
    [['=', ['\\==/', A, B], ['\\?/', '==', A, B]] | Rest],
    ['=', ['\\==/', A, B],
     [let, '$difference', ['subtraction-atom', A, B],
      ['union-atom', '$difference', B]]],
    Rest).

canonicalized_source_decl(
    [['=', ['.:', F1, F2, Arg1, Arg2], [F1, [F2, Arg1, Arg2]]] | Rest],
    ['=', ['.:', F1, F2, Arg1, Arg2], [F1, [F2, Arg1, Arg2]]],
    Rest).

rewrite_partial_builtin_value_terms(TermsIn, HelperDecls, TermsOut) :-
    term_atom_set(TermsIn, Used0),
    rewrite_partial_builtin_value_term_list(
        TermsIn, TermsOut,
        state(Used0, [], []),
        state(_, _, HelperDeclsRev)),
    reverse(HelperDeclsRev, HelperDecls).

rewrite_partial_builtin_value_term_list([], [], State, State).
rewrite_partial_builtin_value_term_list([Term|Rest], [Rewritten|RewrittenRest],
                                        State0, State) :-
    rewrite_partial_builtin_value_term(Term, Rewritten, State0, State1),
    rewrite_partial_builtin_value_term_list(Rest, RewrittenRest, State1, State).

rewrite_partial_builtin_value_term([QuoteFun, [quote, Expr]],
                                   [QuoteFun, [quote, Expr]],
                                   State, State) :-
    quoted_syntax_fun(QuoteFun),
    !.
rewrite_partial_builtin_value_term([quote, Expr], [quote, Expr], State, State) :-
    !.
rewrite_partial_builtin_value_term(Term, HelperName, State0, State) :-
    partial_helper_candidate(Term, Spec, Param),
    !,
    ensure_partial_builtin_helper(Spec, Param, HelperName, State0, State).
rewrite_partial_builtin_value_term(List, Rewritten, State0, State) :-
    is_list(List),
    !,
    rewrite_partial_builtin_value_term_list(List, Rewritten0, State0, State1),
    (   partial_helper_candidate(Rewritten0, Spec, Param)
    ->  ensure_partial_builtin_helper(Spec, Param, Rewritten, State1, State)
    ;   Rewritten = Rewritten0,
        State = State1
    ).
rewrite_partial_builtin_value_term(Term, Term, State, State).

normalize_callable_equality_program([], []).
normalize_callable_equality_program([Decl|Rest], [NormDecl|NormRest]) :-
    normalize_callable_equality_decl(Decl, NormDecl),
    normalize_callable_equality_program(Rest, NormRest).

normalize_callable_equality_decl(['=', LHS, RHS], ['=', LHS, NormRHS]) :-
    normalize_callable_equality_term(RHS, NormRHS),
    !.
normalize_callable_equality_decl(Decl, Decl).

normalize_callable_equality_term(
    [if, ['=', Call, Expected], Then, Else],
    [let, CallResult, NormCall,
     [if, ['==', CallResult, NormExpected], NormThen, CallResult]]) :-
    Else == Call,
    callable_bool_condition_term(Call),
    \+ term_contains_metta_variable(Expected),
    fresh_var(call_result, CallResult),
    normalize_callable_equality_term(Call, NormCall),
    normalize_callable_equality_term(Expected, NormExpected),
    normalize_callable_equality_term(Then, NormThen),
    !.
normalize_callable_equality_term(List, NormList) :-
    is_list(List),
    !,
    maplist(normalize_callable_equality_term, List, NormList).
normalize_callable_equality_term(Term, Term).

callable_bool_condition_term([Apply1Fun, _Fun, _Arg]) :-
    petta_apply1_fun(Apply1Fun).
callable_bool_condition_term([Apply2Fun, _Fun, _Arg1, _Arg2]) :-
    petta_apply2_fun(Apply2Fun).
callable_bool_condition_term([eval, ['atom-subst', _Fun, Binder, [Binder|_Args]]]) :-
    source_variable_atom(Binder).
callable_bool_condition_term([Head|Args]) :-
    source_variable_atom(Head),
    Args \= [].

partial_helper_candidate(Term, Spec, Param) :-
    partial_builtin_helper_candidate(Term, Spec, Param).
partial_helper_candidate(Term, Spec, Param) :-
    partial_composition_helper_candidate(Term, Spec, Param).

partial_builtin_helper_candidate([LambdaFun, Param, Body], Spec, Param) :-
    petta_lambda_fun(LambdaFun),
    unary_partial_builtin_body(Body, Spec, Param).

partial_composition_helper_candidate([LambdaFun, Param, Body], Spec, Param) :-
    petta_lambda_fun(LambdaFun),
    unary_partial_composition_body(Body, Spec, Param).

unary_partial_builtin_body([Fun|Args], partial_builtin(Fun, PrefixArgs), Param) :-
    atom(Fun),
    portable_partial_builtin_arity(Fun, Arity),
    append(PrefixArgs, [Param], Args),
    length(PrefixArgs, PrefixCount),
    PrefixCount =:= Arity - 1,
    \+ term_contains_metta_variable(PrefixArgs).

unary_partial_composition_body([Outer, [Inner, Param]],
                               partial_composition(Outer, Inner),
                               Param) :-
    atom(Outer),
    atom(Inner),
    \+ source_variable_atom(Outer),
    \+ source_variable_atom(Inner).

term_contains_metta_variable(Term) :-
    atom(Term),
    source_variable_atom(Term),
    !.
term_contains_metta_variable(Term) :-
    is_list(Term),
    member(Subterm, Term),
    term_contains_metta_variable(Subterm).

ensure_partial_builtin_helper(Spec, _Param, HelperName,
                              state(Used, Map, HelperDeclsRev),
                              state(Used, Map, HelperDeclsRev)) :-
    memberchk(Spec-HelperName, Map),
    !.
ensure_partial_builtin_helper(Spec, Param, HelperName,
                              state(Used0, Map0, HelperDeclsRev0),
                              state([HelperName|Used0],
                                    [Spec-HelperName|Map0],
                                    [HelperDecl|HelperDeclsRev0])) :-
    fresh_partial_helper_name(Used0, HelperName),
    partial_builtin_helper_decl(Spec, HelperName, Param, HelperDecl).

fresh_partial_helper_name(Used, HelperName) :-
    unique_generated_fun_name('petta-partial', Used, 1, HelperName).

unique_generated_fun_name(Base, Used, N, Name) :-
    atomic_list_concat([Base, N], '-', Candidate),
    (   memberchk(Candidate, Used)
    ->  N1 is N + 1,
        unique_generated_fun_name(Base, Used, N1, Name)
    ;   Name = Candidate
    ).

partial_builtin_helper_decl(partial_builtin(Fun, PrefixArgs), HelperName, Param,
                            ['=', [HelperName, Param], [Fun|CallArgs]]) :-
    append(PrefixArgs, [Param], CallArgs).
partial_builtin_helper_decl(partial_composition(Outer, Inner), HelperName, Param,
                            ['=', [HelperName, Param], [Outer, [Inner, Param]]]).

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

partial_application_body(Mode, [Head|PrefixArgs], Arg, TBody) :-
    partial_application_source_prefix(Head, PrefixArgs),
    append([Head|PrefixArgs], [Arg], Call),
    translate_term_mode(Mode, Call, TBody), !.
partial_application_body(_Mode, Fun, Arg, [Apply1Fun, Fun, Arg]) :-
    source_variable_atom(Fun),
    petta_apply1_fun(Apply1Fun), !.
partial_application_body(Mode, Fun, Arg, TBody) :-
    translate_term_mode(Mode, [Fun, Arg], TBody).

partial_application_quoted_body(Mode, [Head|PrefixArgs], Arg, TBody) :-
    partial_application_source_prefix(Head, PrefixArgs),
    append([Head|PrefixArgs], [Arg], Call),
    translate_quoted_term_mode(Mode, Call, TBody), !.
partial_application_quoted_body(_Mode, Fun, Arg, [Apply1Fun, Fun, Arg]) :-
    source_variable_atom(Fun),
    petta_apply1_fun(Apply1Fun), !.
partial_application_quoted_body(Mode, Fun, Arg, TBody) :-
    translate_quoted_term_mode(Mode, [Fun, Arg], TBody).

reducer_application_body(Agg, TAgg, AccVar, ItemVar,
                         [Apply2Fun, TAgg, AccVar, ItemVar]) :-
    source_variable_atom(Agg),
    petta_apply2_fun(Apply2Fun), !.
reducer_application_body(_Agg, TAgg, AccVar, ItemVar,
                         [eval, [TAgg, AccVar, ItemVar]]).

partial_call_repr([Fun|Args], ReprString) :-
    atom(Fun),
    callable_arity(Fun, Arity),
    length(Args, ArgCount),
    ArgCount < Arity,
    with_output_to(atom(ArgsText), metta_parser:print_sexpr(Args)),
    atomic_list_concat(['"(partial ', Fun, ' ', ArgsText, ')"'], ReprString).

partial_value_source_call([Head|PrefixArgs], Head, PrefixArgs, Arity) :-
    atom(Head),
    callable_arity(Head, Arity),
    length(PrefixArgs, PrefixCount),
    PrefixCount < Arity.

source_defined_partial_value_call([Head|PrefixArgs], Head, PrefixArgs, Arity) :-
    atom(Head),
    tr_source_fun_arity(Head, Arity),
    length(PrefixArgs, PrefixCount),
    PrefixCount < Arity.

partial_application_source_prefix(Head, PrefixArgs) :-
    atom(Head),
    callable_arity(Head, Arity),
    length(PrefixArgs, PrefixCount),
    PrefixCount < Arity.

callable_arity(Fun, Arity) :-
    tr_source_fun_arity(Fun, Arity),
    !.
callable_arity(Fun, Arity) :-
    portable_partial_builtin_arity(Fun, Arity).

portable_partial_builtin_arity('+', 2).
portable_partial_builtin_arity('-', 2).
portable_partial_builtin_arity('*', 2).
portable_partial_builtin_arity('/', 2).
portable_partial_builtin_arity('%', 2).
portable_partial_builtin_arity(mod, 2).
portable_partial_builtin_arity('==', 2).
portable_partial_builtin_arity('=', 2).
portable_partial_builtin_arity('<', 2).
portable_partial_builtin_arity('>', 2).
portable_partial_builtin_arity('<=', 2).
portable_partial_builtin_arity('>=', 2).
portable_partial_builtin_arity(and, 2).
portable_partial_builtin_arity(or, 2).
portable_partial_builtin_arity(xor, 2).
portable_partial_builtin_arity(cons, 2).
portable_partial_builtin_arity('cons-atom', 2).
portable_partial_builtin_arity(append, 2).
portable_partial_builtin_arity(id, 1).

translate_partial_value_mode(Mode, Head, PrefixArgs, Arity, TExpr) :-
    Head == '..',
    PrefixArgs = [F1, F2],
    Arity =:= 3,
    !,
    translate_term_mode(Mode, F1, TF1),
    translate_term_mode(Mode, F2, TF2),
    fresh_var(partial_arg, Param),
    apply_translated_callable(TF2, Param, Inner),
    apply_translated_callable(TF1, Inner, Body),
    petta_lambda_fun(LambdaFun),
    TExpr = [LambdaFun, Param, Body].
translate_partial_value_mode(Mode, Head, PrefixArgs, Arity, TExpr) :-
    translate_term_list_mode(Mode, PrefixArgs, TPrefixArgs),
    length(PrefixArgs, PrefixCount),
    Remaining is Arity - PrefixCount,
    build_partial_lambda_mode(Mode, [Head|TPrefixArgs], Remaining, TExpr).

translate_partial_value_quoted_mode(Mode, Head, PrefixArgs, Arity, TExpr) :-
    Head == '..',
    PrefixArgs = [F1, F2],
    Arity =:= 3,
    !,
    translate_quoted_term_mode(Mode, F1, TF1),
    translate_quoted_term_mode(Mode, F2, TF2),
    fresh_var(partial_arg, Param),
    apply_translated_callable(TF2, Param, Inner),
    apply_translated_callable(TF1, Inner, Body),
    petta_lambda_fun(LambdaFun),
    TExpr = [LambdaFun, Param, Body].
translate_partial_value_quoted_mode(Mode, Head, PrefixArgs, Arity, TExpr) :-
    translate_quoted_term_list_mode(Mode, PrefixArgs, TPrefixArgs),
    length(PrefixArgs, PrefixCount),
    Remaining is Arity - PrefixCount,
    build_partial_lambda_quoted_mode(Mode, [Head|TPrefixArgs], Remaining, TExpr).

apply_translated_callable(Fun, Arg, [Apply1Fun, Fun, Arg]) :-
    source_variable_atom(Fun),
    petta_apply1_fun(Apply1Fun),
    !.
apply_translated_callable(Fun, Arg, [Fun, Arg]).

build_partial_lambda_mode(Mode, CallPrefix, 0, TExpr) :-
    translate_term_mode(Mode, CallPrefix, TExpr), !.
build_partial_lambda_mode(Mode, CallPrefix, Remaining,
                          [LambdaFun, Param, Inner]) :-
    Remaining > 0,
    petta_lambda_fun(LambdaFun),
    fresh_var(partial_arg, Param),
    append(CallPrefix, [Param], NextPrefix),
    Remaining1 is Remaining - 1,
    build_partial_lambda_mode(Mode, NextPrefix, Remaining1, Inner).

build_partial_lambda_quoted_mode(Mode, CallPrefix, 0, TExpr) :-
    translate_quoted_term_mode(Mode, CallPrefix, TExpr), !.
build_partial_lambda_quoted_mode(Mode, CallPrefix, Remaining,
                                 [LambdaFun, Param, Inner]) :-
    Remaining > 0,
    petta_lambda_fun(LambdaFun),
    fresh_var(partial_arg, Param),
    append(CallPrefix, [Param], NextPrefix),
    Remaining1 is Remaining - 1,
    build_partial_lambda_quoted_mode(Mode, NextPrefix, Remaining1, Inner).

translate_nested_lambda_mode(Mode, Params, Body, TExpr) :-
    lambda_source_params(Params, ParamVars),
    pattern_bound_source_variables(Params, BoundVars),
    rawify_pattern_bound_body(BoundVars, Body, RawBody),
    translate_term_mode(Mode, RawBody, TRawBody),
    nest_petta_lambdas(ParamVars, TRawBody, TExpr).

lambda_source_params(Params, [Params]) :-
    source_variable_atom(Params), !.
lambda_source_params(Params, Params) :-
    is_list(Params),
    Params \= [],
    maplist(source_variable_atom, Params).

nest_petta_lambdas([], Body, Body).
nest_petta_lambdas([Param|Rest], Body, [LambdaFun, Param, Nested]) :-
    petta_lambda_fun(LambdaFun),
    nest_petta_lambdas(Rest, Body, Nested).

translate_term_list_mode(_Mode, [], []).
translate_term_list_mode(Mode, [Term|Rest], [TTerm|TRest]) :-
    translate_term_mode(Mode, Term, TTerm),
    translate_term_list_mode(Mode, Rest, TRest).

translate_args_with_quote_positions(Mode, Args, QuotePositions, TArgs) :-
    translate_args_with_quote_positions(Mode, Args, QuotePositions, 1, TArgs).

translate_args_with_quote_positions(_, [], _, _, []).
translate_args_with_quote_positions(Mode, [Arg|Rest], QuotePositions, Index,
                                    [TArg|TRest]) :-
    (   memberchk(Index, QuotePositions)
    ->  translate_term_mode(Mode, [quote, Arg], TArg)
    ;   translate_term_mode(Mode, Arg, TArg)
    ),
    Index1 is Index + 1,
    translate_args_with_quote_positions(Mode, Rest, QuotePositions, Index1, TRest).

translate_quoted_term_list_mode(_Mode, [], []).
translate_quoted_term_list_mode(Mode, [Term|Rest], [TTerm|TRest]) :-
    translate_quoted_term_mode(Mode, Term, TTerm),
    translate_quoted_term_list_mode(Mode, Rest, TRest).

translate_quoted_args_with_quote_positions(Mode, Args, QuotePositions, TArgs) :-
    translate_quoted_args_with_quote_positions(Mode, Args, QuotePositions, 1, TArgs).

translate_quoted_args_with_quote_positions(_, [], _, _, []).
translate_quoted_args_with_quote_positions(Mode, [Arg|Rest], QuotePositions, Index,
                                           [TArg|TRest]) :-
    (   memberchk(Index, QuotePositions)
    ->  translate_quoted_term_mode(Mode, [quote, Arg], TArg)
    ;   translate_quoted_term_mode(Mode, Arg, TArg)
    ),
    Index1 is Index + 1,
    translate_quoted_args_with_quote_positions(Mode, Rest, QuotePositions, Index1, TRest).

needs_curried_application(Head, Args) :-
    atom(Head),
    callable_arity(Head, Arity),
    length(Args, ArgCount),
    ArgCount > Arity.

expression_head_needs_curried_application(Head) :-
    is_list(Head),
    (   source_defined_partial_value_call(Head, _Fun, _PrefixArgs, _Arity)
    ;   Head = ['|->', Params, _Body],
        lambda_source_params(Params, _ParamVars)
    ;   Head = [lambda, Params, _Body],
        lambda_source_params(Params, _ParamVars)
    ).

translate_curried_application_mode(Mode, Head, Args, TExpr) :-
    atom(Head),
    callable_arity(Head, Arity),
    length(Args, ArgCount),
    ArgCount > Arity,
    !,
    length(DirectArgs, Arity),
    append(DirectArgs, ExtraArgs, Args),
    translate_term_mode(Mode, [Head|DirectArgs], TBase),
    left_associate_application_mode(Mode, TBase, ExtraArgs, TExpr).
translate_curried_application_mode(Mode, Head, Args, TExpr) :-
    translate_term_mode(Mode, Head, THead),
    left_associate_application_mode(Mode, THead, Args, TExpr).

translate_curried_application_quoted_mode(Mode, Head, Args, TExpr) :-
    atom(Head),
    callable_arity(Head, Arity),
    length(Args, ArgCount),
    ArgCount > Arity,
    !,
    length(DirectArgs, Arity),
    append(DirectArgs, ExtraArgs, Args),
    translate_quoted_term_mode(Mode, [Head|DirectArgs], TBase),
    left_associate_application_quoted_mode(Mode, TBase, ExtraArgs, TExpr).
translate_curried_application_quoted_mode(Mode, Head, Args, TExpr) :-
    translate_quoted_term_mode(Mode, Head, THead),
    left_associate_application_quoted_mode(Mode, THead, Args, TExpr).

left_associate_application_mode(_Mode, THead, [], THead).
left_associate_application_mode(Mode, THead, [Arg|Rest], TExpr) :-
    petta_apply1_fun(Apply1Fun),
    translate_term_mode(Mode, Arg, TArg),
    left_associate_application_mode(Mode, [Apply1Fun, THead, TArg], Rest, TExpr).

left_associate_application_quoted_mode(_Mode, THead, [], THead).
left_associate_application_quoted_mode(Mode, THead, [Arg|Rest], TExpr) :-
    petta_apply1_fun(Apply1Fun),
    translate_quoted_term_mode(Mode, Arg, TArg),
    left_associate_application_quoted_mode(Mode, [Apply1Fun, THead, TArg], Rest, TExpr).

translate_callable_source_var_application_mode(Mode, Head, Args, TExpr) :-
    translate_term_mode(Mode, Head, THead),
    translate_callable_application_mode(Mode, THead, Args, TExpr).

translate_callable_application_mode(Mode, THead, [Arg], [Apply1Fun, THead, TArg]) :-
    petta_apply1_fun(Apply1Fun),
    translate_term_mode(Mode, Arg, TArg).
translate_callable_application_mode(Mode, THead, [Arg1, Arg2], [Apply2Fun, THead, TArg1, TArg2]) :-
    petta_apply2_fun(Apply2Fun),
    translate_term_mode(Mode, Arg1, TArg1),
    translate_term_mode(Mode, Arg2, TArg2).
translate_callable_application_mode(Mode, THead, [Arg1, Arg2|Rest], TExpr) :-
    petta_apply2_fun(Apply2Fun),
    petta_apply1_fun(Apply1Fun),
    translate_term_mode(Mode, Arg1, TArg1),
    translate_term_mode(Mode, Arg2, TArg2),
    Base = [Apply2Fun, THead, TArg1, TArg2],
    translate_callable_application_tail_mode(Mode, Apply1Fun, Base, Rest, TExpr).

translate_callable_application_tail_mode(_Mode, _Apply1Fun, Base, [], Base).
translate_callable_application_tail_mode(Mode, Apply1Fun, Base, [Arg|Rest], TExpr) :-
    translate_term_mode(Mode, Arg, TArg),
    Next = [Apply1Fun, Base, TArg],
    translate_callable_application_tail_mode(Mode, Apply1Fun, Next, Rest, TExpr).

translate_quoted_callable_source_var_application_mode(Mode, Head, Args, TExpr) :-
    translate_quoted_term_mode(Mode, Head, THead),
    translate_quoted_callable_application_mode(Mode, THead, Args, TExpr).

translate_quoted_callable_application_mode(Mode, THead, [Arg], [Apply1Fun, THead, TArg]) :-
    petta_apply1_fun(Apply1Fun),
    translate_quoted_term_mode(Mode, Arg, TArg).
translate_quoted_callable_application_mode(Mode, THead, [Arg1, Arg2], [Apply2Fun, THead, TArg1, TArg2]) :-
    petta_apply2_fun(Apply2Fun),
    translate_quoted_term_mode(Mode, Arg1, TArg1),
    translate_quoted_term_mode(Mode, Arg2, TArg2).
translate_quoted_callable_application_mode(Mode, THead, [Arg1, Arg2|Rest], TExpr) :-
    petta_apply2_fun(Apply2Fun),
    petta_apply1_fun(Apply1Fun),
    translate_quoted_term_mode(Mode, Arg1, TArg1),
    translate_quoted_term_mode(Mode, Arg2, TArg2),
    Base = [Apply2Fun, THead, TArg1, TArg2],
    translate_quoted_callable_application_tail_mode(Mode, Apply1Fun, Base, Rest, TExpr).

translate_quoted_callable_application_tail_mode(_Mode, _Apply1Fun, Base, [], Base).
translate_quoted_callable_application_tail_mode(Mode, Apply1Fun, Base, [Arg|Rest], TExpr) :-
    translate_quoted_term_mode(Mode, Arg, TArg),
    Next = [Apply1Fun, Base, TArg],
    translate_quoted_callable_application_tail_mode(Mode, Apply1Fun, Next, Rest, TExpr).

foldall_collector_head(pure, collapse).
foldall_collector_head(hyperpose, collapse).
foldall_collector_head(ffi_tokens, collapse).
foldall_collector_head(petta_he, collapse).
foldall_collector_head(petta_he_hyperpose, collapse).
foldall_collector_head(extended, collect).
foldall_collector_head(extended_hyperpose, collect).
foldall_collector_head(trusted, collapse).
foldall_collector_head(trusted_extended, collect).

preserve_hyperpose_mode(hyperpose).
preserve_hyperpose_mode(petta_he_hyperpose).
preserve_hyperpose_mode(extended_hyperpose).

petta_he_profile_mode(petta_he).
petta_he_profile_mode(petta_he_hyperpose).

he_extended_mode(extended).
he_extended_mode(extended_hyperpose).
he_extended_mode(trusted_extended).

pure_once_surface_mode(Mode) :-
    \+ petta_he_profile_mode(Mode),
    \+ he_extended_mode(Mode).

native_quote_mode(pure).
native_quote_mode(hyperpose).
native_quote_mode(ffi_tokens).
native_quote_mode(petta_he).
native_quote_mode(petta_he_hyperpose).
native_quote_mode(extended).
native_quote_mode(extended_hyperpose).
native_quote_mode(trusted).
native_quote_mode(trusted_extended).

ffi_tokens_mode(ffi_tokens).

trusted_mode(trusted).
trusted_mode(trusted_extended).

source_variable_atom(Term) :-
    atom(Term),
    sub_atom(Term, 0, 1, _, '$').

expr_data_fun_positions(Fun, Positions) :-
    tr_expr_data_fun(Fun, Positions).

noncallable_data_head(Head, Args) :-
    atomic(Head),
    \+ callable_arity(Head, _),
    \+ intrinsic_noncallable_runtime_head(Head),
    contains_callable_syntax_data_arg(Args).

intrinsic_noncallable_runtime_head(chain).
intrinsic_noncallable_runtime_head(unify).
intrinsic_noncallable_runtime_head(only).
intrinsic_noncallable_runtime_head(function).
intrinsic_noncallable_runtime_head(return).
intrinsic_noncallable_runtime_head(nop).
intrinsic_noncallable_runtime_head('add-atom').
intrinsic_noncallable_runtime_head('remove-atom').
intrinsic_noncallable_runtime_head(match).
intrinsic_noncallable_runtime_head('get-atoms').
intrinsic_noncallable_runtime_head(superpose).
intrinsic_noncallable_runtime_head(hyperpose).
intrinsic_noncallable_runtime_head(collapse).
intrinsic_noncallable_runtime_head(unique).
intrinsic_noncallable_runtime_head(select).
intrinsic_noncallable_runtime_head('foldl-atom').
intrinsic_noncallable_runtime_head('map-atom').
intrinsic_noncallable_runtime_head('filter-atom').
intrinsic_noncallable_runtime_head('second-from-pair').
intrinsic_noncallable_runtime_head('size-atom').
intrinsic_noncallable_runtime_head('get-metatype').
intrinsic_noncallable_runtime_head(metta).
intrinsic_noncallable_runtime_head('intersection-atom').
intrinsic_noncallable_runtime_head('subtraction-atom').
intrinsic_noncallable_runtime_head('union-atom').
intrinsic_noncallable_runtime_head('decons-atom').
intrinsic_noncallable_runtime_head(cons).
intrinsic_noncallable_runtime_head('cons-atom').
intrinsic_noncallable_runtime_head('new-space').
intrinsic_noncallable_runtime_head('new-state').
intrinsic_noncallable_runtime_head('bind!').
intrinsic_noncallable_runtime_head('get-state').
intrinsic_noncallable_runtime_head('change-state!').
intrinsic_noncallable_runtime_head('import!').
intrinsic_noncallable_runtime_head('println!').
intrinsic_noncallable_runtime_head('format-args').
intrinsic_noncallable_runtime_head(Head) :-
    atom(Head),
    sub_atom(Head, 0, 6, _, 'petta-').

contains_callable_syntax_data_arg(Args) :-
    member(Arg, Args),
    callable_syntax_data_arg(Arg),
    !.

callable_syntax_data_arg(Arg) :-
    is_list(Arg),
    \+ preserves_nested_eval_surface(Arg).

translate_noncallable_data_args_mode(_Mode, [], []).
translate_noncallable_data_args_mode(Mode, [Arg|Rest], [TArg|TRest]) :-
    translate_noncallable_data_arg_mode(Mode, Arg, TArg),
    translate_noncallable_data_args_mode(Mode, Rest, TRest).

translate_noncallable_data_arg_mode(Mode, Arg, TArg) :-
    preserves_nested_eval_surface(Arg),
    !,
    translate_term_mode(Mode, Arg, TArg).
translate_noncallable_data_arg_mode(Mode, Arg, TArg) :-
    callable_syntax_data_arg(Arg),
    !,
    translate_term_mode(Mode, [quote, Arg], TArg).
translate_noncallable_data_arg_mode(Mode, Arg, TArg) :-
    translate_term_mode(Mode, Arg, TArg).

preserves_nested_eval_surface([quote, _]).
preserves_nested_eval_surface([call, _]).
preserves_nested_eval_surface([eval, _]).
preserves_nested_eval_surface([reduce, _]).

translate_data_tuple_element_mode(Mode, [Head|Args], [Head|TArgs]) :-
    !,
    translate_data_tuple_args_mode(Mode, Args, TArgs).
translate_data_tuple_element_mode(Mode, Term, TTerm) :-
    translate_term_mode(Mode, Term, TTerm).

translate_data_tuple_element_list_mode(_Mode, [], []).
translate_data_tuple_element_list_mode(Mode, [Arg|Rest], [TArg|TRest]) :-
    translate_data_tuple_element_mode(Mode, Arg, TArg),
    translate_data_tuple_element_list_mode(Mode, Rest, TRest).

translate_data_tuple_args_mode(_Mode, [], []).
translate_data_tuple_args_mode(Mode, [Arg|Rest], [TArg|TRest]) :-
    translate_data_tuple_arg_mode(Mode, Arg, TArg),
    translate_data_tuple_args_mode(Mode, Rest, TRest).

translate_data_tuple_arg_mode(Mode, Arg, TArg) :-
    preserves_nested_eval_surface(Arg),
    !,
    translate_term_mode(Mode, Arg, TArg).
translate_data_tuple_arg_mode(Mode, Arg, TArg) :-
    is_list(Arg),
    !,
    translate_term_mode(Mode, [quote, Arg], TArg).
translate_data_tuple_arg_mode(Mode, Arg, TArg) :-
    translate_term_mode(Mode, Arg, TArg).

raw_expr_data_quote_mode(pure).
raw_expr_data_quote_mode(hyperpose).
raw_expr_data_quote_mode(ffi_tokens).
raw_expr_data_quote_mode(extended).
raw_expr_data_quote_mode(extended_hyperpose).
raw_expr_data_quote_mode(trusted).
raw_expr_data_quote_mode(trusted_extended).

source_program_defines_fun(Fun) :-
    tr_source_fun_count(Fun, Count),
    Count > 0.

translate_alpha_equal_mode(Mode, Left, Right, [AlphaEqualFun, TLeft, TRight]) :-
    native_quote_mode(Mode),
    petta_alpha_equal_eval_fun(AlphaEqualFun),
    translate_quoted_term_mode(Mode, Left, TLeft),
    translate_quoted_term_mode(Mode, Right, TRight), !.

concrete_runtime_surface_source_expr(Expr) :-
    nonvar(Expr),
    \+ runtime_surface_mentions_source_variable(Expr).

runtime_surface_mentions_source_variable(Expr) :-
    source_variable_atom(Expr),
    !.
runtime_surface_mentions_source_variable(Expr) :-
    is_list(Expr),
    member(Subterm, Expr),
    runtime_surface_mentions_source_variable(Subterm),
    !.

runtime_eval_inline_target([quote, Inner], Inner) :-
    !.
runtime_eval_inline_target(TExpr, [unquote, [quote, TExpr]]).

runtime_call_inline_target([quote, _], [metta, [eval], '%Undefined%', '&self']) :-
    !.
runtime_call_inline_target(TExpr, [unquote, [quote, TExpr]]).

translate_call_like_mode(Mode, Expr, TExpr) :-
    native_quote_mode(Mode),
    concrete_runtime_surface_source_expr(Expr),
    translate_quoted_term_mode(Mode, Expr, TQuoted),
    runtime_call_inline_target(TQuoted, TExpr),
    !.
translate_call_like_mode(Mode, Expr, [CallFun, TExpr]) :-
    native_quote_mode(Mode),
    petta_runtime_call_fun(CallFun),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.

translate_eval_like_mode(Mode, Expr, TExpr) :-
    native_quote_mode(Mode),
    concrete_runtime_surface_source_expr(Expr),
    translate_quoted_term_mode(Mode, Expr, TQuoted),
    runtime_eval_inline_target(TQuoted, TExpr),
    !.
translate_eval_like_mode(Mode, Expr, [EvalFun, TExpr]) :-
    native_quote_mode(Mode),
    petta_runtime_eval_fun(EvalFun),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.

translate_reduce_like_mode(Mode, Expr, TExpr) :-
    native_quote_mode(Mode),
    concrete_runtime_surface_source_expr(Expr),
    translate_quoted_term_mode(Mode, Expr, TQuoted),
    runtime_eval_inline_target(TQuoted, TExpr),
    !.
translate_reduce_like_mode(Mode, Expr, [ReduceFun, TExpr]) :-
    native_quote_mode(Mode),
    petta_runtime_reduce_fun(ReduceFun),
    translate_quoted_term_mode(Mode, Expr, TExpr), !.

force_runtime_helper_value(Stem, HelperCall, [let, ValueVar, HelperCall, ValueVar]) :-
    fresh_var(Stem, ValueVar).

pure_once_lowering(TExpr, [let, TupleVar, [collapse, TExpr],
                          [case, TupleVar,
                           [['()', 'Empty'],
                            [NonemptyVar,
                             [let, [HeadVar, TailVar],
                              ['decons-atom', NonemptyVar],
                              HeadVar]]]]]) :-
    fresh_var(tuple, TupleVar),
    fresh_var(nonempty, NonemptyVar),
    fresh_var(head, HeadVar),
    fresh_var(tail, TailVar).

empty_tuple_surface('()').
empty_tuple_surface([]).

finite_exists_match_empty_surface(Left, Right, MatchExpr) :-
    empty_tuple_surface(Left),
    finite_exists_match_collapse_surface(Right, MatchExpr), !.
finite_exists_match_empty_surface(Left, Right, MatchExpr) :-
    empty_tuple_surface(Right),
    finite_exists_match_collapse_surface(Left, MatchExpr).

finite_exists_match_collapse_surface([collapse, [once, MatchExpr]], MatchExpr) :-
    nonvar(MatchExpr),
    MatchExpr = [match, _SpaceExpr, _Pattern, _Body].

finite_exists_match_empty_lowering(TOnce, ['==', '()', [collapse, TOnce]]).

%% Singleton visible witness detection
%%
%% This is narrower than general `once`: the search expression must expose at
%% most one visible witness independent of visible result order. Preserve that
%% fragment as a dedicated contract so the runtime can keep the witness
%% bindings intact without widening pure HE to ordered committed choice.
singleton_visible_witness_source_expr(Expr) :-
    singleton_visible_witness_source_expr(Expr, []).

singleton_visible_witness_source_expr(Expr, _) :-
    source_truth_atom(Expr),
    !.
singleton_visible_witness_source_expr(Expr, Seen) :-
    singleton_visible_witness_deterministic_term(Expr, Seen),
    !.
singleton_visible_witness_source_expr([once, Inner], Seen) :-
    singleton_visible_witness_source_expr(Inner, Seen),
    !.
singleton_visible_witness_source_expr([and, Left, Right], Seen) :-
    singleton_visible_witness_source_expr(Left, Seen),
    singleton_visible_witness_source_expr(Right, Seen),
    !.
singleton_visible_witness_source_expr([Head|Args], Seen) :-
    atom(Head),
    singleton_visible_witness_source_call(Head, Args, Seen).

normalize_singleton_visible_witness_term([quote, Expr], [quote, Expr]) :-
    !.
normalize_singleton_visible_witness_term([once, Inner], [once, NormInner]) :-
    !,
    normalize_singleton_visible_witness_term(Inner, NormInner).
normalize_singleton_visible_witness_term([and, Left, Right], [and, NormLeft, NormRight]) :-
    !,
    normalize_singleton_visible_witness_term(Left, NormLeft),
    normalize_singleton_visible_witness_term(Right, NormRight).
normalize_singleton_visible_witness_term(['=', Left, Right],
                                         [unify, NormLeft, NormRight, 'True', 'Empty']) :-
    singleton_visible_witness_binding_equality_surface(Left, Right),
    !,
    normalize_singleton_visible_witness_term(Left, NormLeft),
    normalize_singleton_visible_witness_term(Right, NormRight).
normalize_singleton_visible_witness_term([Head|Args], [Head|NormArgs]) :-
    !,
    maplist(normalize_singleton_visible_witness_term, Args, NormArgs).
normalize_singleton_visible_witness_term(Term, Term).

singleton_visible_witness_binding_equality_surface(Left, Right) :-
    source_variable_atom(Left),
    \+ term_mentions_atom(Right, Left),
    singleton_visible_witness_deterministic_term(Right, []),
    !.
singleton_visible_witness_binding_equality_surface(Left, Right) :-
    source_variable_atom(Right),
    \+ term_mentions_atom(Left, Right),
    singleton_visible_witness_deterministic_term(Left, []).

singleton_visible_witness_deterministic_term(Term, _) :-
    atomic(Term),
    !.
singleton_visible_witness_deterministic_term(Term, _) :-
    source_variable_atom(Term),
    !.
singleton_visible_witness_deterministic_term([once, Inner], Seen) :-
    singleton_visible_witness_source_expr(Inner, Seen),
    !.
singleton_visible_witness_deterministic_term(['=', Left, Right], Seen) :-
    singleton_visible_witness_deterministic_term(Left, Seen),
    singleton_visible_witness_deterministic_term(Right, Seen),
    !.
singleton_visible_witness_deterministic_term([if, Cond, Then, Else], Seen) :-
    singleton_visible_witness_source_expr(Cond, Seen),
    singleton_visible_witness_deterministic_term(Then, Seen),
    singleton_visible_witness_deterministic_term(Else, Seen),
    !.
singleton_visible_witness_deterministic_term([and, Left, Right], Seen) :-
    singleton_visible_witness_source_expr(Left, Seen),
    singleton_visible_witness_source_expr(Right, Seen),
    !.
singleton_visible_witness_deterministic_term([Head|Args], Seen) :-
    atom(Head),
    singleton_visible_witness_source_call(Head, Args, Seen),
    !.
singleton_visible_witness_deterministic_term([Head|Args], Seen) :-
    atom(Head),
    \+ source_program_defines_fun(Head),
    \+ singleton_visible_witness_explicit_nondet_head(Head),
    maplist(singleton_visible_witness_deterministic_term_with(Seen), Args),
    !.

singleton_visible_witness_deterministic_term_with(Seen, Term) :-
    singleton_visible_witness_deterministic_term(Term, Seen).

singleton_visible_witness_source_call(Functor, ActualArgs, Seen) :-
    CallKey = call(Functor, ActualArgs),
    \+ memberchk(CallKey, Seen),
    findall(FormalArgs-RSub,
            singleton_visible_witness_matched_clause_rhs(Functor, ActualArgs, FormalArgs, RSub),
            Matches),
    Matches = [_FormalArgs-RHS],
    singleton_visible_witness_source_expr(RHS, [CallKey|Seen]).

singleton_visible_witness_matched_clause_rhs(Functor, ActualArgs, FormalArgs, RSub) :-
    tr_source_fun_clause(Functor, FormalArgs, RHS),
    same_length(FormalArgs, ActualArgs),
    once(source_pattern_args_match(FormalArgs, ActualArgs, [], [], FormalSubsts, _ActualSubsts)),
    once(apply_source_substitutions(FormalSubsts, RHS, RSub)).

source_pattern_args_match([], [], FormalSubsts, ActualSubsts, FormalSubsts, ActualSubsts).
source_pattern_args_match([Formal|Formals], [Actual|Actuals], Formal0, Actual0,
                          FormalOut, ActualOut) :-
    source_pattern_term_match(Formal, Actual, Formal0, Formal1, Actual0, Actual1),
    source_pattern_args_match(Formals, Actuals, Formal1, Actual1, FormalOut, ActualOut).

source_pattern_term_match(Formal, Actual, Formal0, FormalOut, Actual0, Actual0) :-
    source_variable_atom(Formal),
    !,
    source_pattern_var_bind(Formal, Actual, Formal0, FormalOut).
source_pattern_term_match(Formal, Actual, Formal0, Formal0, Actual0, ActualOut) :-
    source_variable_atom(Actual),
    !,
    source_pattern_var_bind(Actual, Formal, Actual0, ActualOut).
source_pattern_term_match(Formal, Actual, Formal0, Formal0, Actual0, Actual0) :-
    atomic(Formal),
    atomic(Actual),
    Formal == Actual,
    !.
source_pattern_term_match(Formal, Actual, Formal0, FormalOut, Actual0, ActualOut) :-
    is_list(Formal),
    is_list(Actual),
    same_length(Formal, Actual),
    !,
    source_pattern_args_match(Formal, Actual, Formal0, Actual0, FormalOut, ActualOut).

source_pattern_var_bind(Var, Value, Substs0, Substs) :-
    (   memberchk(Var-Bound, Substs0)
    ->  Bound = Value,
        Substs = Substs0
    ;   Substs = [Var-Value|Substs0]
    ).

source_truth_atom(true).
source_truth_atom('True').

singleton_visible_witness_explicit_nondet_head(match).
singleton_visible_witness_explicit_nondet_head(superpose).
singleton_visible_witness_explicit_nondet_head(hyperpose).
singleton_visible_witness_explicit_nondet_head(collapse).
singleton_visible_witness_explicit_nondet_head(once).
singleton_visible_witness_explicit_nondet_head(select).
singleton_visible_witness_explicit_nondet_head(member).
singleton_visible_witness_explicit_nondet_head('get-atoms').
singleton_visible_witness_explicit_nondet_head('mork:match').
singleton_visible_witness_explicit_nondet_head('mork:get-atoms').
singleton_visible_witness_explicit_nondet_head(metta).
singleton_visible_witness_explicit_nondet_head(evalc).

term_mentions_atom(Term, Atom) :-
    Term == Atom,
    !.
term_mentions_atom(Term, Atom) :-
    is_list(Term),
    member(Subterm, Term),
    term_mentions_atom(Subterm, Atom).

throw_unsupported_cut_for_he_core(_Mode, Predicate) :-
    throw(error(
        domain_error(he_core_surface, cut),
        context(petta_to_he:Predicate,
                'PeTTa cut has no portable HE-core translation; use --petta-he for the PeTTa HE profile target'))).

throw_unsupported_arithmetic_inversion_for_he_core(_Mode, Predicate) :-
    throw(error(
        domain_error(he_core_surface, arithmetic_inversion),
        context(petta_to_he:Predicate,
                'PeTTa arithmetic inversion relies on CLP witness solving; use --petta-he or an explicit witness/oracle lane instead of pure HE-core translation'))).

throw_unsupported_petta_native_for_he_core(_Mode, Surface, Predicate) :-
    format(atom(Message),
           'PeTTa native surface ~w has no portable HE-core translation; define it in source or use --petta-he for the PeTTa HE profile target',
           [Surface]),
    throw(error(
        domain_error(he_core_surface, Surface),
        context(petta_to_he:Predicate, Message))).

prepend_petta_compat_program_decls(Mode, SourceDecls, TDecls0, TDecls) :-
    maybe_rewrite_builtin_test_calls(Mode, SourceDecls, TDecls0, TDecls1),
    maybe_prepend_petta_test_compat_decls(Mode, SourceDecls, TDecls1, TDecls2),
    maybe_prepend_append_compat_decls(SourceDecls, TDecls2, TDecls3),
    maybe_prepend_second_from_pair_compat_decls(SourceDecls, TDecls3, TDecls4),
    maybe_prepend_is_member_compat_decls(SourceDecls, TDecls4, TDecls5),
    maybe_prepend_reverse_compat_decls(SourceDecls, TDecls5, TDecls6),
    maybe_prepend_last_compat_decls(SourceDecls, TDecls6, TDecls7),
    maybe_prepend_foldl_compat_decls(SourceDecls, TDecls7, TDecls8),
    maybe_prepend_min_compat_decls(SourceDecls, TDecls8, TDecls9),
    maybe_prepend_max_compat_decls(SourceDecls, TDecls9, TDecls10),
    maybe_prepend_alpha_unique_atom_compat_decls(SourceDecls, TDecls10, TDecls11),
    maybe_prepend_petta_alpha_equal_eval_compat_decls(TDecls11, TDecls12),
    maybe_prepend_petta_runtime_call_compat_decls(TDecls12, TDecls13),
    maybe_prepend_petta_runtime_eval_compat_decls(TDecls13, TDecls14),
    maybe_prepend_petta_runtime_reduce_compat_decls(TDecls14, TDecls15),
    maybe_prepend_petta_bool_compat_decls(SourceDecls, TDecls15, TDecls16),
    maybe_prepend_petta_if2_compat_decls(SourceDecls, TDecls16, TDecls17),
    maybe_prepend_petta_member_compat_decls(SourceDecls, TDecls17, TDecls18),
    maybe_prepend_petta_lambda_compat_decls(SourceDecls, TDecls18, TDecls19),
    maybe_prepend_petta_apply_compat_decls(SourceDecls, TDecls19, TDecls20),
    maybe_prepend_petta_ffi_function_call_inversion_compat_decls(SourceDecls, TDecls20, TDecls21),
    maybe_prepend_petta_state_compat_decls(TDecls21, TDecls22),
    maybe_prepend_quote_compat_decls(TDecls22, TDecls23),
    maybe_prepend_length_compat_decls(Mode, SourceDecls, TDecls23, TDecls24),
    TDecls = TDecls24.

maybe_prepend_petta_test_compat_decls(Mode, _SourceDecls, TDecls0, TDecls) :-
    petta_he_profile_mode(Mode),
    !,
    TDecls = TDecls0.
maybe_prepend_petta_test_compat_decls(_Mode, _SourceDecls, TDecls0, TDecls) :-
    maybe_prepend_petta_test_public_compat_decls(TDecls0, TDecls1),
    maybe_prepend_petta_test_results_compat_decls(TDecls1, TDecls2),
    maybe_prepend_petta_test_results_data_compat_decls(TDecls2, TDecls3),
    maybe_prepend_petta_test_bag_compat_decls(TDecls3, TDecls4),
    maybe_prepend_petta_test_equal_compat_decls(TDecls4, TDecls5),
    maybe_prepend_petta_test_equal_data_compat_decls(TDecls5, TDecls6),
    maybe_prepend_petta_test_runtime_bool_compat_decls(TDecls6, TDecls).

maybe_prepend_petta_test_public_compat_decls(TDecls0, TDecls) :-
    (   (   program_uses_any_petta_test_helper(TDecls0)
        ;   program_uses_petta_test_public_term(TDecls0)
        ;   program_uses_petta_test_public_syntax(TDecls0)
        )
    ->  petta_test_public_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_test_equal_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_test_equal(TDecls0)
    ->  petta_test_equal_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_test_equal_data_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_test_equal_data(TDecls0)
    ->  petta_test_equal_data_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_test_runtime_bool_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_test_runtime_bool(TDecls0)
    ->  petta_test_runtime_bool_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_test_results_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_test_results(TDecls0)
    ->  petta_test_results_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_test_results_data_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_test_results_data(TDecls0)
    ->  petta_test_results_data_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_test_bag_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_test_bag(TDecls0)
    ->  petta_test_bag_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_alpha_equal_eval_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_alpha_equal_eval(TDecls0)
    ->  petta_alpha_equal_eval_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_runtime_call_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_runtime_call(TDecls0)
    ->  petta_runtime_call_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_runtime_eval_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_runtime_eval(TDecls0)
    ->  petta_runtime_eval_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_runtime_reduce_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_runtime_reduce(TDecls0)
    ->  petta_runtime_reduce_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_append_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_append(SourceDecls),
        \+ program_defines_append(SourceDecls)
    ->  petta_append_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_second_from_pair_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_second_from_pair(SourceDecls),
        \+ program_defines_second_from_pair(SourceDecls)
    ->  petta_second_from_pair_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_is_member_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_is_member(SourceDecls),
        \+ program_defines_is_member(SourceDecls)
    ->  petta_is_member_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_reverse_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_reverse(SourceDecls),
        \+ program_defines_reverse(SourceDecls)
    ->  petta_reverse_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_last_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_last(SourceDecls),
        \+ program_defines_last(SourceDecls)
    ->  petta_last_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_foldl_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_foldl(SourceDecls),
        \+ program_defines_foldl(SourceDecls)
    ->  petta_foldl_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_min_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_min(SourceDecls),
        \+ program_defines_min(SourceDecls)
    ->  petta_min_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_max_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_max(SourceDecls),
        \+ program_defines_max(SourceDecls)
    ->  petta_max_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_alpha_unique_atom_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_alpha_unique_atom(SourceDecls),
        \+ program_defines_alpha_unique_atom(SourceDecls)
    ->  petta_alpha_unique_atom_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_bool_compat_decls(SourceDecls, TDecls0, TDecls) :-
    maybe_prepend_petta_bool_or_compat_decls(SourceDecls, TDecls0, TDecls1),
    maybe_prepend_petta_bool_and_compat_decls(SourceDecls, TDecls1, TDecls).

maybe_prepend_petta_bool_and_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_petta_bool_and(TDecls0),
        \+ program_defines_petta_bool_and(SourceDecls)
    ->  petta_bool_and_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_bool_or_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_petta_bool_or(TDecls0),
        \+ program_defines_petta_bool_or(SourceDecls)
    ->  petta_bool_or_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_if2_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_petta_if2(TDecls0),
        \+ program_defines_petta_if2(SourceDecls)
    ->  petta_if2_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_member_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_petta_member(TDecls0),
        \+ program_defines_petta_member(SourceDecls)
    ->  petta_member_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_lambda_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_petta_lambda_helper(TDecls0),
        \+ program_defines_petta_lambda(SourceDecls)
    ->  petta_lambda_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_apply_compat_decls(SourceDecls, TDecls0, TDecls) :-
    maybe_prepend_petta_apply2_compat_decls(SourceDecls, TDecls0, TDecls1),
    maybe_prepend_petta_apply1_compat_decls(SourceDecls, TDecls1, TDecls).

maybe_prepend_petta_apply1_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_petta_apply1_helper(TDecls0),
        \+ program_defines_petta_apply1(SourceDecls)
    ->  petta_apply1_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_apply2_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_petta_apply2_helper(TDecls0),
        \+ program_defines_petta_apply2(SourceDecls)
    ->  petta_apply2_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_ffi_function_call_inversion_compat_decls(SourceDecls, TDecls0, TDecls) :-
    (   program_uses_petta_ffi_function_call_inversion_helper(TDecls0),
        \+ program_defines_petta_ffi_function_call_inversion(SourceDecls)
    ->  petta_ffi_function_call_inversion_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_petta_state_compat_decls(TDecls0, TDecls) :-
    (   program_uses_petta_state_helper(TDecls0),
        \+ program_defines_petta_state_helper(TDecls0)
    ->  petta_state_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_quote_compat_decls(TDecls0, TDecls) :-
    (   program_uses_quoted_syntax(TDecls0),
        \+ program_defines_quoted_syntax(TDecls0)
    ->  petta_quote_compat_decls(CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_prepend_length_compat_decls(Mode, SourceDecls, TDecls0, TDecls) :-
    (   program_uses_length(SourceDecls),
        \+ program_defines_length(SourceDecls)
    ->  petta_length_compat_decls(Mode, CompatDecls),
        append(CompatDecls, TDecls0, TDecls)
    ;   TDecls = TDecls0
    ).

maybe_rewrite_builtin_test_calls(Mode, _SourceDecls, TDecls0, TDecls) :-
    petta_he_profile_mode(Mode),
    !,
    TDecls = TDecls0.
maybe_rewrite_builtin_test_calls(_Mode, SourceDecls, TDecls0, TDecls) :-
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

program_uses_append(Term) :-
    is_list(Term),
    (   Term = [append, _, _]
    ;   member(Subterm, Term),
        program_uses_append(Subterm)
    ).

program_uses_append(_) :-
    fail.

program_uses_second_from_pair(Term) :-
    is_list(Term),
    (   Term = ['second-from-pair', _]
    ;   member(Subterm, Term),
        program_uses_second_from_pair(Subterm)
    ).

program_uses_second_from_pair(_) :-
    fail.

program_uses_is_member(Term) :-
    is_list(Term),
    (   Term = ['is-member', _, _]
    ;   member(Subterm, Term),
        program_uses_is_member(Subterm)
    ).

program_uses_is_member(_) :-
    fail.

program_uses_reverse(Term) :-
    is_list(Term),
    (   Term = [reverse, _]
    ;   member(Subterm, Term),
        program_uses_reverse(Subterm)
    ).

program_uses_reverse(_) :-
    fail.

program_uses_last(Term) :-
    is_list(Term),
    (   Term = [last, _]
    ;   member(Subterm, Term),
        program_uses_last(Subterm)
    ).

program_uses_last(_) :-
    fail.

program_uses_foldl(Term) :-
    is_list(Term),
    (   Term = [foldl, _, _, _]
    ;   member(Subterm, Term),
        program_uses_foldl(Subterm)
    ).

program_uses_foldl(_) :-
    fail.

program_uses_min(Term) :-
    is_list(Term),
    (   Term = [min, _, _]
    ;   member(Subterm, Term),
        program_uses_min(Subterm)
    ).

program_uses_min(_) :-
    fail.

program_uses_max(Term) :-
    is_list(Term),
    (   Term = [max, _, _]
    ;   member(Subterm, Term),
        program_uses_max(Subterm)
    ).

program_uses_max(_) :-
    fail.

program_uses_alpha_unique_atom(Term) :-
    is_list(Term),
    (   Term = ['alpha-unique-atom', _]
    ;   member(Subterm, Term),
        program_uses_alpha_unique_atom(Subterm)
    ).

program_uses_alpha_unique_atom(_) :-
    fail.

program_uses_quoted_syntax(Term) :-
    is_list(Term),
    quoted_syntax_fun(QuoteFun),
    (   Term = [QuoteFun|_]
    ;   member(Subterm, Term),
        program_uses_quoted_syntax(Subterm)
    ).

program_uses_quoted_syntax(_) :-
    fail.

program_uses_petta_state_helper(Term) :-
    is_list(Term),
    (   petta_state_helper_call(Term)
    ;   member(Subterm, Term),
        program_uses_petta_state_helper(Subterm)
    ).

program_uses_petta_state_helper(_) :-
    fail.

petta_state_helper_call([Head|_]) :-
    atom(Head),
    (   petta_state_clear_fun(Head)
    ;   petta_state_set_fun(Head)
    ;   petta_state_get_fun(Head)
    ).

program_uses_petta_test_equal(Term) :-
    is_list(Term),
    (   petta_test_equal_fun(TestEqual),
        Term = [TestEqual, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_test_equal(Subterm)
    ).

program_uses_petta_test_equal(_) :-
    fail.

program_uses_petta_test_equal_data(Term) :-
    is_list(Term),
    (   petta_test_equal_data_fun(TestEqualData),
        Term = [TestEqualData, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_test_equal_data(Subterm)
    ).

program_uses_petta_test_equal_data(_) :-
    fail.

program_uses_petta_test_runtime_bool(Term) :-
    is_list(Term),
    (   petta_test_runtime_bool_fun(TestRuntimeBool),
        Term = [TestRuntimeBool, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_test_runtime_bool(Subterm)
    ).

program_uses_petta_test_runtime_bool(_) :-
    fail.

program_uses_petta_test_results(Term) :-
    is_list(Term),
    (   petta_test_results_fun(TestResults),
        Term = [TestResults, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_test_results(Subterm)
    ).

program_uses_petta_test_results(_) :-
    fail.

program_uses_petta_test_results_data(Term) :-
    is_list(Term),
    (   petta_test_results_data_fun(TestResultsData),
        Term = [TestResultsData, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_test_results_data(Subterm)
    ).

program_uses_petta_test_results_data(_) :-
    fail.

program_uses_petta_test_bag(Term) :-
    is_list(Term),
    (   petta_test_bag_fun(TestBag),
        Term = [TestBag, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_test_bag(Subterm)
    ).

program_uses_petta_test_bag(_) :-
    fail.

program_uses_any_petta_test_helper(Term) :-
    program_uses_petta_test_equal(Term),
    !.
program_uses_any_petta_test_helper(Term) :-
    program_uses_petta_test_equal_data(Term),
    !.
program_uses_any_petta_test_helper(Term) :-
    program_uses_petta_test_results(Term),
    !.
program_uses_any_petta_test_helper(Term) :-
    program_uses_petta_test_results_data(Term),
    !.
program_uses_any_petta_test_helper(Term) :-
    program_uses_petta_test_bag(Term).

program_uses_petta_test_public_term(Term) :-
    is_list(Term),
    (   petta_test_public_term_fun(PublicTerm),
        Term = [PublicTerm, _]
    ;   member(Subterm, Term),
        program_uses_petta_test_public_term(Subterm)
    ).

program_uses_petta_test_public_term(_) :-
    fail.

program_uses_petta_test_public_syntax(Term) :-
    is_list(Term),
    (   petta_test_public_syntax_fun(PublicSyntax),
        Term = [PublicSyntax, _]
    ;   member(Subterm, Term),
        program_uses_petta_test_public_syntax(Subterm)
    ).

program_uses_petta_test_public_syntax(_) :-
    fail.

program_uses_petta_alpha_equal_eval(Term) :-
    is_list(Term),
    (   petta_alpha_equal_eval_fun(AlphaEqual),
        Term = [AlphaEqual, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_alpha_equal_eval(Subterm)
    ).

program_uses_petta_alpha_equal_eval(_) :-
    fail.

program_uses_petta_runtime_call(Term) :-
    is_list(Term),
    (   petta_runtime_call_fun(RuntimeCall),
        Term = [RuntimeCall, _]
    ;   member(Subterm, Term),
        program_uses_petta_runtime_call(Subterm)
    ).

program_uses_petta_runtime_call(_) :-
    fail.

program_uses_petta_runtime_eval(Term) :-
    is_list(Term),
    (   petta_runtime_eval_fun(RuntimeEval),
        Term = [RuntimeEval, _]
    ;   member(Subterm, Term),
        program_uses_petta_runtime_eval(Subterm)
    ).

program_uses_petta_runtime_eval(_) :-
    fail.

program_uses_petta_runtime_reduce(Term) :-
    is_list(Term),
    (   petta_runtime_reduce_fun(RuntimeReduce),
        Term = [RuntimeReduce, _]
    ;   member(Subterm, Term),
        program_uses_petta_runtime_reduce(Subterm)
    ).

program_uses_petta_runtime_reduce(_) :-
    fail.

program_uses_petta_lambda_helper(Term) :-
    is_list(Term),
    (   petta_lambda_fun(LambdaFun),
        Term = [LambdaFun, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_lambda_helper(Subterm)
    ).

program_uses_petta_lambda_helper(_) :-
    fail.

program_uses_petta_apply1_helper(Term) :-
    is_list(Term),
    (   petta_apply1_fun(Apply1),
        Term = [Apply1, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_apply1_helper(Subterm)
    ).

program_uses_petta_apply1_helper(_) :-
    fail.

program_uses_petta_apply2_helper(Term) :-
    is_list(Term),
    (   petta_apply2_fun(Apply2),
        Term = [Apply2, _, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_apply2_helper(Subterm)
    ).

program_uses_petta_apply2_helper(_) :-
    fail.

program_uses_petta_bool_and(Term) :-
    is_list(Term),
    (   petta_bool_and_fun(AndFun),
        Term = [AndFun, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_bool_and(Subterm)
    ).

program_uses_petta_bool_and(_) :-
    fail.

program_uses_petta_bool_or(Term) :-
    is_list(Term),
    (   petta_bool_or_fun(OrFun),
        Term = [OrFun, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_bool_or(Subterm)
    ).

program_uses_petta_bool_or(_) :-
    fail.

program_uses_petta_if2(Term) :-
    is_list(Term),
    (   petta_if2_fun(If2Fun),
        Term = [If2Fun, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_if2(Subterm)
    ).

program_uses_petta_if2(_) :-
    fail.

program_uses_petta_member(Term) :-
    is_list(Term),
    (   petta_member_fun(MemberFun),
        Term = [MemberFun, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_member(Subterm)
    ).

program_uses_petta_member(_) :-
    fail.

program_uses_petta_ffi_function_call_inversion_helper(Term) :-
    is_list(Term),
    (   petta_ffi_function_call_inversion_fun(FfiFun),
        Term = [FfiFun, _, _, _, _]
    ;   member(Subterm, Term),
        program_uses_petta_ffi_function_call_inversion_helper(Subterm)
    ).

program_uses_petta_ffi_function_call_inversion_helper(_) :-
    fail.

program_defines_length([['=', [length|_], _]|_]) :- !.
program_defines_length([_|Rest]) :-
    program_defines_length(Rest).

program_defines_append([['=', [append|_], _]|_]) :- !.
program_defines_append([_|Rest]) :-
    program_defines_append(Rest).

program_defines_second_from_pair([['=', ['second-from-pair'|_], _]|_]) :- !.
program_defines_second_from_pair([_|Rest]) :-
    program_defines_second_from_pair(Rest).

program_defines_is_member([['=', ['is-member'|_], _]|_]) :- !.
program_defines_is_member([_|Rest]) :-
    program_defines_is_member(Rest).

program_defines_reverse([['=', [reverse|_], _]|_]) :- !.
program_defines_reverse([_|Rest]) :-
    program_defines_reverse(Rest).

program_defines_last([['=', [last|_], _]|_]) :- !.
program_defines_last([_|Rest]) :-
    program_defines_last(Rest).

program_defines_foldl([['=', [foldl|_], _]|_]) :- !.
program_defines_foldl([_|Rest]) :-
    program_defines_foldl(Rest).

program_defines_min([['=', [min|_], _]|_]) :- !.
program_defines_min([_|Rest]) :-
    program_defines_min(Rest).

program_defines_max([['=', [max|_], _]|_]) :- !.
program_defines_max([_|Rest]) :-
    program_defines_max(Rest).

program_defines_alpha_unique_atom([['=', ['alpha-unique-atom'|_], _]|_]) :- !.
program_defines_alpha_unique_atom([_|Rest]) :-
    program_defines_alpha_unique_atom(Rest).

program_defines_petta_lambda([['=', [[Head|_], _], _]|_]) :-
    petta_lambda_fun(Head), !.
program_defines_petta_lambda([_|Rest]) :-
    program_defines_petta_lambda(Rest).

program_defines_petta_apply1([['=', [Head|_], _]|_]) :-
    petta_apply1_fun(Head), !.
program_defines_petta_apply1([_|Rest]) :-
    program_defines_petta_apply1(Rest).

program_defines_petta_apply2([['=', [Head|_], _]|_]) :-
    petta_apply2_fun(Head), !.
program_defines_petta_apply2([_|Rest]) :-
    program_defines_petta_apply2(Rest).

program_defines_petta_bool_and([['=', [Head|_], _]|_]) :-
    petta_bool_and_fun(Head), !.
program_defines_petta_bool_and([_|Rest]) :-
    program_defines_petta_bool_and(Rest).

program_defines_petta_bool_or([['=', [Head|_], _]|_]) :-
    petta_bool_or_fun(Head), !.
program_defines_petta_bool_or([_|Rest]) :-
    program_defines_petta_bool_or(Rest).

program_defines_petta_if2([['=', [Head|_], _]|_]) :-
    petta_if2_fun(Head), !.
program_defines_petta_if2([_|Rest]) :-
    program_defines_petta_if2(Rest).

program_defines_petta_member([['=', [Head|_], _]|_]) :-
    petta_member_fun(Head), !.
program_defines_petta_member([_|Rest]) :-
    program_defines_petta_member(Rest).

program_defines_petta_ffi_function_call_inversion([['=', [Head|_], _]|_]) :-
    petta_ffi_function_call_inversion_fun(Head), !.
program_defines_petta_ffi_function_call_inversion([_|Rest]) :-
    program_defines_petta_ffi_function_call_inversion(Rest).

program_defines_quoted_syntax([['=', [Head|_], _]|_]) :-
    quoted_syntax_fun(Head), !.
program_defines_quoted_syntax([_|Rest]) :-
    program_defines_quoted_syntax(Rest).

program_defines_petta_state_helper([['=', [Head|_], _]|_]) :-
    atom(Head),
    (   petta_state_clear_fun(Head)
    ;   petta_state_set_fun(Head)
    ;   petta_state_get_fun(Head)
    ), !.
program_defines_petta_state_helper([_|Rest]) :-
    program_defines_petta_state_helper(Rest).

program_defines_test([['=', [test|_], _]|_]) :- !.
program_defines_test([_|Rest]) :-
    program_defines_test(Rest).

petta_test_public_compat_decls([
    [':', PublicTerm, ['->', 'Atom', 'Atom']],
    [':', PublicSyntax, ['->', 'Atom', 'Atom']],
    ['=', [PublicTerm, '$expr'], PublicTermBody],
    ['=', [PublicSyntax, '$expr'], PublicSyntaxBody]
]) :-
    petta_test_public_term_fun(PublicTerm),
    petta_test_public_syntax_fun(PublicSyntax),
    PublicTermBody =
        [if, ['==', ['get-metatype', '$expr'], 'Expression'],
         [case, '$expr',
          [['()', '()'],
           [[quote, '$__tr_public_quoted'],
            [PublicSyntax, '$__tr_public_quoted']],
           ['$__tr_public_any',
            ['map-atom', '$expr', '$__tr_public_item',
             [eval, [PublicTerm, '$__tr_public_item']]]]]],
         '$expr'],
    PublicSyntaxBody =
        [if, ['==', ['get-metatype', '$expr'], 'Expression'],
         [case, '$expr',
          [['()', '()'],
           ['$__tr_public_any',
            ['map-atom', '$expr', '$__tr_public_item',
             [eval, [PublicSyntax, '$__tr_public_item']]]]]],
         '$expr'].

petta_if2_compat_decls([
    ['=', [If2Fun, 'True', '$then'], '$then']
]) :-
    petta_if2_fun(If2Fun).

petta_test_equal_compat_decls([
    [':', TestEqual, ['->', 'Atom', 'Atom', 'Bool']],
    ['=', [TestEqual, '$actual', '$expected'], TestBody]
]) :-
    petta_test_equal_fun(TestEqual),
    petta_test_public_term_fun(PublicTerm),
    petta_test_direct_body(PublicTerm, TestBody).

petta_test_equal_data_compat_decls([
    [':', TestEqualData, ['->', 'Atom', 'Atom', 'Bool']],
    ['=', [TestEqualData, '$actual', '$expected'], TestBody]
]) :-
    petta_test_equal_data_fun(TestEqualData),
    petta_test_public_term_fun(PublicTerm),
    petta_test_public_syntax_fun(PublicSyntax),
    petta_test_direct_data_body(PublicTerm, PublicSyntax, TestBody).

petta_test_runtime_bool_compat_decls([
    [':', TestRuntimeBool, ['->', 'Atom', 'Atom', 'Bool']],
    ['=', [TestRuntimeBool, '$actual', '$expected'], TestBody]
]) :-
    petta_test_runtime_bool_fun(TestRuntimeBool),
    petta_test_runtime_bool_body(TestBody).

petta_test_results_compat_decls([
    ['=', [NormalizeFun, '$tuple'],
     [PublicTerm,
      [case, '$tuple',
       [[['$single'], '$single'],
        ['$many', '$many']]]]],
    [':', TestResults, ['->', 'Atom', 'Atom', 'Bool']],
    ['=', [TestResults, '$actual', '$expected'], TestBody]
]) :-
    petta_test_normalize_fun(NormalizeFun),
    petta_test_public_term_fun(PublicTerm),
    petta_test_results_fun(TestResults),
    petta_test_collapse_body(NormalizeFun, TestBody).

petta_test_results_data_compat_decls([
    ['=', [NormalizeFun, '$tuple'],
     [PublicTerm,
      [case, '$tuple',
       [[['$single'], '$single'],
        ['$many', '$many']]]]],
    [':', TestResultsData, ['->', 'Atom', 'Atom', 'Bool']],
    ['=', [TestResultsData, '$actual', '$expected'], TestBody]
]) :-
    petta_test_normalize_fun(NormalizeFun),
    petta_test_public_term_fun(PublicTerm),
    petta_test_public_syntax_fun(PublicSyntax),
    petta_test_results_data_fun(TestResultsData),
    petta_test_collapse_data_body(NormalizeFun, PublicTerm, PublicSyntax, TestBody).

petta_test_bag_compat_decls([
    [':', TestBag, ['->', 'Atom', 'Atom', 'Bool']],
    ['=', [TestBag, '$actual', '$expected'], TestBody]
]) :-
    petta_test_bag_fun(TestBag),
    petta_test_public_term_fun(PublicTerm),
    petta_test_bag_body(PublicTerm, TestBody).

petta_test_direct_body(PublicTerm, Body) :-
    Success =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ✅"',
           ['$__tr_actual_public', '$__tr_expected_public']]],
         'True'],
    Failure =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ❌"',
           ['$__tr_actual_public', '$__tr_expected_public']]],
         'False'],
    Body =
        [let, '$__tr_actual_value', [eval, '$actual'],
         [let, '$__tr_expected_value', [eval, '$expected'],
          [let, '$__tr_actual_public_1', [eval, [PublicTerm, '$__tr_actual_value']],
           [let, '$__tr_expected_public_1', [eval, [PublicTerm, '$__tr_expected_value']],
            [let, '$__tr_actual_public', [eval, '$__tr_actual_public_1'],
             [let, '$__tr_expected_public', [eval, '$__tr_expected_public_1'],
              [if, ['==', '$__tr_actual_public', '$__tr_expected_public'],
               Success,
               [if, ['=alpha', '$__tr_actual_public', '$__tr_expected_public'],
                Success,
                Failure]]]]]]]].

petta_test_direct_data_body(PublicTerm, PublicSyntax, Body) :-
    RawExprSuccess =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ✅"',
           ['$actual', '$__tr_expected_any']]],
         'True'],
    RawSuccess =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ✅"',
           ['$__tr_actual_value', '$__tr_expected_any']]],
         'True'],
    Success =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ✅"',
           ['$__tr_actual_public', '$__tr_expected_public']]],
         'True'],
    Failure =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ❌"',
           ['$__tr_actual_public', '$__tr_expected_public']]],
         'False'],
    QuotedFallback =
        [let, '$__tr_actual_public_1', [eval, [PublicTerm, '$__tr_actual_value']],
         [let, '$__tr_expected_public_1', [eval, [PublicSyntax, '$__tr_expected_syntax']],
          [let, '$__tr_actual_public', [eval, '$__tr_actual_public_1'],
           [let, '$__tr_expected_public', [eval, '$__tr_expected_public_1'],
            [if, ['==', '$__tr_actual_public', '$__tr_expected_public'],
             Success,
             [if, ['=alpha', '$__tr_actual_public', '$__tr_expected_public'],
              Success,
              Failure]]]]]],
    AnyFallback =
        [let, '$__tr_actual_public_1', [eval, [PublicTerm, '$__tr_actual_value']],
         [let, '$__tr_expected_public_1', [eval, [PublicTerm, '$__tr_expected_any']],
          [let, '$__tr_actual_public', [eval, '$__tr_actual_public_1'],
           [let, '$__tr_expected_public', [eval, '$__tr_expected_public_1'],
            [if, ['==', '$__tr_actual_public', '$__tr_expected_public'],
             Success,
             [if, ['=alpha', '$__tr_actual_public', '$__tr_expected_public'],
              Success,
              Failure]]]]]],
    Body =
        [let, '$__tr_actual_value', [eval, '$actual'],
         [case, '$expected',
          [[[quote, '$__tr_expected_syntax'],
            QuotedFallback],
           ['$__tr_expected_any',
            [if, ['==', '$actual', '$__tr_expected_any'],
             RawExprSuccess,
             [if, ['=alpha', '$actual', '$__tr_expected_any'],
              RawExprSuccess,
              [if, ['==', '$__tr_actual_value', '$__tr_expected_any'],
               RawSuccess,
               [if, ['=alpha', '$__tr_actual_value', '$__tr_expected_any'],
                RawSuccess,
                AnyFallback]]]]]]]].

petta_test_runtime_bool_body(Body) :-
    Success =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ✅"',
           ['$actual', '$expected']]],
         'True'],
    Failure =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ❌"',
           ['$actual', '$expected']]],
         'False'],
    Body =
        [if, ['==', '$actual', '$expected'],
         Success,
         [if, ['=alpha', '$actual', '$expected'],
          Success,
          Failure]].

petta_test_collapse_body(NormalizeFun, Body) :-
    Success =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ✅"',
           ['$__tr_actual_results', '$__tr_expected_results']]],
         'True'],
    Failure =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ❌"',
           ['$__tr_actual_results', '$__tr_expected_results']]],
         'False'],
    Body =
        [let, '$__tr_actual_collapse',
         [collapse, [let, '$__tr_actual_item', '$actual', '$__tr_actual_item']],
         [let, '$__tr_expected_collapse',
          [collapse, [let, '$__tr_expected_item', '$expected', '$__tr_expected_item']],
          [let, '$__tr_actual_results_1',
           [eval, [NormalizeFun, '$__tr_actual_collapse']],
           [let, '$__tr_expected_results_1',
            [eval, [NormalizeFun, '$__tr_expected_collapse']],
          [let, '$__tr_actual_results', [eval, '$__tr_actual_results_1'],
           [let, '$__tr_expected_results', [eval, '$__tr_expected_results_1'],
            [if, ['==', '$__tr_actual_results', '$__tr_expected_results'],
             Success,
             Failure]]]]]]].

petta_test_collapse_data_body(NormalizeFun, PublicTerm, PublicSyntax, Body) :-
    RawSuccess =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ✅"',
           ['$__tr_actual_results_raw', '$__tr_expected_results_raw']]],
         'True'],
    RawBagCompare =
        [if, ['==', ['get-metatype', '$__tr_actual_results_raw'], 'Expression'],
         [if, ['==', ['get-metatype', '$__tr_expected_results_raw'], 'Expression'],
          [let, '$__tr_actual_only',
           ['subtraction-atom', '$__tr_actual_results_raw', '$__tr_expected_results_raw'],
           [let, '$__tr_expected_only',
            ['subtraction-atom', '$__tr_expected_results_raw', '$__tr_actual_results_raw'],
            [if, ['==', '$__tr_actual_only', '()'],
             [if, ['==', '$__tr_expected_only', '()'],
              RawSuccess,
              AnyFallback],
             AnyFallback]]],
          AnyFallback],
         AnyFallback],
    Success =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ✅"',
           ['$__tr_actual_results', '$__tr_expected_results']]],
         'True'],
    Failure =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ❌"',
           ['$__tr_actual_results', '$__tr_expected_results']]],
         'False'],
    QuotedFallback =
        [let, '$__tr_actual_results_1',
         [eval, [NormalizeFun, '$__tr_actual_collapse']],
         [let, '$__tr_expected_results_1',
          [eval, [PublicSyntax, '$__tr_expected_syntax']],
          [let, '$__tr_actual_results', [eval, '$__tr_actual_results_1'],
           [let, '$__tr_expected_results', [eval, '$__tr_expected_results_1'],
            [if, ['==', '$__tr_actual_results', '$__tr_expected_results'],
             Success,
             Failure]]]]],
    AnyFallback =
        [let, '$__tr_actual_results_1',
         [eval, [NormalizeFun, '$__tr_actual_collapse']],
         [let, '$__tr_expected_results_1',
          [eval, [PublicTerm, '$__tr_expected_any']],
          [let, '$__tr_actual_results', [eval, '$__tr_actual_results_1'],
           [let, '$__tr_expected_results', [eval, '$__tr_expected_results_1'],
            [if, ['==', '$__tr_actual_results', '$__tr_expected_results'],
             Success,
             Failure]]]]],
    Body =
        [let, '$__tr_actual_collapse',
         [collapse, [let, '$__tr_actual_item', '$actual', '$__tr_actual_item']],
         [let, '$__tr_actual_results_raw',
          '$__tr_actual_collapse',
          [case, '$expected',
           [[[quote, '$__tr_expected_syntax'],
             QuotedFallback],
            ['$__tr_expected_any',
             [let, '$__tr_expected_results_raw',
              '$__tr_expected_any',
              [if, ['==', '$__tr_actual_results_raw', '$__tr_expected_results_raw'],
               RawSuccess,
               [if, ['=alpha', '$__tr_actual_results_raw', '$__tr_expected_results_raw'],
                RawSuccess,
                RawBagCompare]]]]]]]].

petta_test_bag_body(PublicTerm, Body) :-
    Success =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ✅"',
           ['$__tr_actual_results', '$__tr_expected_results']]],
         'True'],
    Failure =
        [let, '$__tr_test_printed',
         ['println!',
          ['format-args', '"is {}, should {}. ❌"',
           ['$__tr_actual_results', '$__tr_expected_results']]],
         'False'],
    CompareBody =
        [let, '$__tr_actual_only',
         ['subtraction-atom', '$__tr_actual_results', '$__tr_expected_results'],
         [let, '$__tr_expected_only',
          ['subtraction-atom', '$__tr_expected_results', '$__tr_actual_results'],
          [if, ['==', '$__tr_actual_only', '()'],
           [if, ['==', '$__tr_expected_only', '()'],
            Success,
            Failure],
           Failure]]],
    Body =
        [let, '$__tr_actual_results_1',
         [eval,
          [PublicTerm,
           [collapse, [let, '$__tr_actual_item', '$actual', '$__tr_actual_item']]]],
         [let, '$__tr_expected_results_1', [eval, [PublicTerm, '$expected']],
          [let, '$__tr_actual_results', [eval, '$__tr_actual_results_1'],
           [let, '$__tr_expected_results', [eval, '$__tr_expected_results_1'],
            CompareBody]]]].

petta_append_compat_decls([
    ['=', [append, '()', '$ys'], '$ys'],
    ['=', [append, '$xs', '$ys'],
     [case, ['decons-atom', '$xs'],
      [[['$head', '$tail'],
        [let, '$__tr_append_rest',
         [append, '$tail', '$ys'],
         ['cons-atom', '$head', '$__tr_append_rest']]]]]]
]).

petta_second_from_pair_compat_decls([
    [':', 'second-from-pair', ['->', 'Atom', 'Atom']],
    ['=', ['second-from-pair', '$pair'],
     [function,
      [unify, '$pair', ['$first', '$second'],
       [return, '$second'],
       [return,
        ['Error', ['second-from-pair', '$pair'],
         '"incorrect pair format"']]]]]
]).

petta_is_member_compat_decls([
    ['=', ['is-member', '$item', '$tuple'],
     [not,
      ['==',
       [collapse,
        [let, '$x', [superpose, '$tuple'],
         [if, ['==', '$x', '$item'],
          'True',
          [empty]]]],
       '()']]]
]).

petta_reverse_compat_decls([
    [':', reverse, ['->', 'Atom', 'Expression']],
    ['=', [reverse, '$xs'], ['petta-reverse-acc', '$xs', '()']],
    ['=', ['petta-reverse-acc', '()', '$acc'], '$acc'],
    ['=', ['petta-reverse-acc', '$xs', '$acc'],
     [case, ['decons-atom', '$xs'],
      [[['$head', '$tail'],
        ['petta-reverse-acc', '$tail', ['cons-atom', '$head', '$acc']]]]]]
]).

petta_last_compat_decls([
    [':', last, ['->', 'Atom', 'Expression']],
    ['=', [last, '$xs'],
     [case, ['decons-atom', '$xs'],
      [[['$head', '()'], '$head'],
       [['$head', '$tail'], [last, '$tail']]]]]
]).

petta_foldl_compat_decls([
    [':', foldl, ['->', 'Atom', 'Atom', 'Atom', 'Expression']],
    ['=', [foldl, '$f', '$list', '$init'],
     ['foldl-atom', '$list', '$init', '$__tr_acc', '$__tr_item',
      [eval, ['$f', '$__tr_item', '$__tr_acc']]]]
]).

petta_min_compat_decls([
    [':', min, ['->', 'Number', 'Number', 'Number']],
    ['=', [min, '$a', '$b'],
     [if, ['<=', '$a', '$b'], '$a', '$b']]
]).

petta_max_compat_decls([
    [':', max, ['->', 'Number', 'Number', 'Number']],
    ['=', [max, '$a', '$b'],
     [if, ['<=', '$a', '$b'], '$b', '$a']]
]).

petta_alpha_equal_eval_compat_decls([
    [':', 'petta-alpha-equal-eval', ['->', 'Atom', 'Atom', 'Bool']],
    ['=', ['petta-alpha-equal-eval', '$left', '$right'],
     [let, '$__tr_alpha_left',
      [metta, '$left', '%Undefined%', '&self'],
      [let, '$__tr_alpha_right',
       [metta, '$right', '%Undefined%', '&self'],
       ['=alpha', '$__tr_alpha_left', '$__tr_alpha_right']]]]
]) :-
    petta_alpha_equal_eval_fun('petta-alpha-equal-eval').

petta_alpha_unique_atom_compat_decls([
    [':', 'alpha-unique-atom', ['->', 'Atom', 'Expression']],
    ['=', ['petta-is-alpha-member', '$item', '$tuple'],
     [not,
      ['==',
       [collapse,
        [let, '$x', [superpose, '$tuple'],
         [if, ['=alpha', '$x', '$item'],
          'True',
          [empty]]]],
       '()']]],
    ['=', ['alpha-unique-atom', '$tuple'],
     ['petta-alpha-unique-atom-loop', '$tuple', '()']],
    ['=', ['petta-alpha-unique-atom-loop', '()', '$seen'], '()'],
    ['=', ['petta-alpha-unique-atom-loop', '$tuple', '$seen'],
     [case, ['decons-atom', '$tuple'],
      [[['$head', '$tail'],
        [if, ['petta-is-alpha-member', '$head', '$seen'],
         ['petta-alpha-unique-atom-loop', '$tail', '$seen'],
         [let, '$rest',
          ['petta-alpha-unique-atom-loop', '$tail', ['cons-atom', '$head', '$seen']],
          ['cons-atom', '$head', '$rest']]]]]]]
]).

petta_runtime_call_compat_decls([
    [':', 'petta-runtime-call', ['->', 'Atom', 'Atom']],
    ['=', ['petta-runtime-call', '$expr'],
     [case, '$expr',
      [[[quote, '$inner'],
        [metta, [eval], '%Undefined%', '&self']],
       ['$other',
        [let, '$result', [unquote, [quote, '$other']],
         [if, ['==', '$result', '$other'],
          [metta, [eval], '%Undefined%', '&self'],
          '$result']]]]]]
]) :-
    petta_runtime_call_fun('petta-runtime-call').

petta_runtime_eval_compat_decls([
    [':', 'petta-runtime-eval', ['->', 'Atom', 'Atom']],
    ['=', ['petta-runtime-eval', '$expr'],
     [case, '$expr',
      [[[quote, '$inner'], '$inner'],
       ['$other', [unquote, [quote, '$other']]]]]]
]) :-
    petta_runtime_eval_fun('petta-runtime-eval').

petta_runtime_reduce_compat_decls([
    [':', 'petta-runtime-reduce', ['->', 'Atom', 'Atom']],
    ['=', ['petta-runtime-reduce', '$expr'],
     [case, '$expr',
      [[[quote, '$inner'], '$inner'],
       ['$other', [unquote, [quote, '$other']]]]]]
]) :-
    petta_runtime_reduce_fun('petta-runtime-reduce').

petta_bool_and_compat_decls([
    ['=', [AndFun, 'True', '$y'], '$y'],
    ['=', [AndFun, 'False', '$y'], 'False']
]) :-
    petta_bool_and_fun(AndFun).

petta_bool_or_compat_decls([
    ['=', [OrFun, 'True', '$y'], 'True'],
    ['=', [OrFun, 'False', '$y'], '$y']
]) :-
    petta_bool_or_fun(OrFun).

petta_member_compat_decls([
    ['=', [MemberFun, '$x', ['$x', '$tail']], 'True'],
    ['=', [MemberFun, '$x', ['$head', '$tail']], [MemberFun, '$x', '$tail']]
]) :-
    petta_member_fun(MemberFun).

petta_lambda_compat_decls([
    [':', LambdaFun, ['->', 'Atom', '$t', ['->', '$a', '$t']]],
    ['=', [[LambdaFun, '$var', '$body'], '$arg'],
     [unquote, [quote, [let, '$var', '$arg', '$body']]]]
]) :-
    petta_lambda_fun(LambdaFun).

petta_apply1_compat_decls([
    [':', Apply1Fun, ['->', 'Atom', 'Atom', 'Atom']],
    ['=', [Apply1Fun, [LambdaFun, '$var', '$body'], '$arg'],
     [unquote, [quote, [let, '$var', '$arg', '$body']]]],
    ['=', [Apply1Fun, '$f', '$arg'],
     [eval, ['$f', '$arg']]]
]) :-
    petta_apply1_fun(Apply1Fun),
    petta_lambda_fun(LambdaFun).

petta_apply2_compat_decls([
    [':', Apply2Fun, ['->', 'Atom', 'Atom', 'Atom', 'Atom']],
    ['=', [Apply2Fun, '$f', '$arg1', '$arg2'],
     [let, '$__tr_apply_mid',
      [Apply1Fun, '$f', '$arg1'],
      [Apply1Fun, '$__tr_apply_mid', '$arg2']]]
]) :-
    petta_apply2_fun(Apply2Fun),
    petta_apply1_fun(Apply1Fun).

petta_ffi_function_call_inversion_compat_decls([
    [':', FfiFun, ['->', 'Atom', 'Atom', 'Atom', 'Atom', 'Atom']],
    ['=', [FfiFun, '$lane', '$pattern', '$observed', '$continuation'],
     ['Error',
      [FfiFun, '$lane', '$pattern', '$observed', '$continuation'],
      "ffi token required for function-call inversion"]]
]) :-
    petta_ffi_function_call_inversion_fun(FfiFun).

petta_lib_petta_helper_decls(Keys, Decls) :-
    petta_lib_petta_helper_decls_acc(Keys, [], NestedDecls),
    append(NestedDecls, Decls).

petta_lib_petta_helper_decls_acc([], Acc, Decls) :-
    reverse(Acc, Decls).
petta_lib_petta_helper_decls_acc([Key|Rest], Acc, Decls) :-
    petta_lib_petta_helper_decl_block(Key, Block),
    petta_lib_petta_helper_decls_acc(Rest, [Block|Acc], Decls).

petta_lib_petta_helper_decl_block(test_equal, Decls) :-
    petta_test_equal_compat_decls(Decls).
petta_lib_petta_helper_decl_block(test_equal_data, Decls) :-
    petta_test_equal_data_compat_decls(Decls).
petta_lib_petta_helper_decl_block(test_runtime_bool, Decls) :-
    petta_test_runtime_bool_compat_decls(Decls).
petta_lib_petta_helper_decl_block(test_results, Decls) :-
    petta_test_results_compat_decls(Decls).
petta_lib_petta_helper_decl_block(test_results_data, Decls) :-
    petta_test_results_data_compat_decls(Decls).
petta_lib_petta_helper_decl_block(test_bag, Decls) :-
    petta_test_bag_compat_decls(Decls).
petta_lib_petta_helper_decl_block(test_public, Decls) :-
    petta_test_public_compat_decls(Decls).
petta_lib_petta_helper_decl_block(alpha_equal_eval, Decls) :-
    petta_alpha_equal_eval_compat_decls(Decls).
petta_lib_petta_helper_decl_block(runtime_call, Decls) :-
    petta_runtime_call_compat_decls(Decls).
petta_lib_petta_helper_decl_block(runtime_eval, Decls) :-
    petta_runtime_eval_compat_decls(Decls).
petta_lib_petta_helper_decl_block(runtime_reduce, Decls) :-
    petta_runtime_reduce_compat_decls(Decls).
petta_lib_petta_helper_decl_block(if2, Decls) :-
    petta_if2_compat_decls(Decls).
petta_lib_petta_helper_decl_block(lambda, Decls) :-
    petta_lambda_compat_decls(Decls).
petta_lib_petta_helper_decl_block(apply1, Decls) :-
    petta_apply1_compat_decls(Decls).
petta_lib_petta_helper_decl_block(apply2, Decls) :-
    petta_apply2_compat_decls(Decls).
petta_lib_petta_helper_decl_block(bool_and, Decls) :-
    petta_bool_and_compat_decls(Decls).
petta_lib_petta_helper_decl_block(bool_or, Decls) :-
    petta_bool_or_compat_decls(Decls).
petta_lib_petta_helper_decl_block(member, Decls) :-
    petta_member_compat_decls(Decls).
petta_lib_petta_helper_decl_block(ffi_function_call_inversion, Decls) :-
    petta_ffi_function_call_inversion_compat_decls(Decls).
petta_lib_petta_helper_decl_block(second_from_pair, Decls) :-
    petta_second_from_pair_compat_decls(Decls).
petta_lib_petta_helper_decl_block(is_member, Decls) :-
    petta_is_member_compat_decls(Decls).
petta_lib_petta_helper_decl_block(reverse, Decls) :-
    petta_reverse_compat_decls(Decls).
petta_lib_petta_helper_decl_block(last, Decls) :-
    petta_last_compat_decls(Decls).
petta_lib_petta_helper_decl_block(foldl, Decls) :-
    petta_foldl_compat_decls(Decls).
petta_lib_petta_helper_decl_block(min, Decls) :-
    petta_min_compat_decls(Decls).
petta_lib_petta_helper_decl_block(max, Decls) :-
    petta_max_compat_decls(Decls).
petta_lib_petta_helper_decl_block(alpha_unique_atom, Decls) :-
    petta_alpha_unique_atom_compat_decls(Decls).

petta_length_compat_decls(Mode, [
    ['=', [length, '$expr'],
     [let, '$tuple', [eval, '$expr'], ['size-atom', '$tuple']]]
]) :-
    petta_he_profile_mode(Mode), !.
petta_length_compat_decls(_, [
    ['=', [length, '$expr'],
     ['size-atom', '$expr']]
]).

petta_quote_compat_decls([
    ['=', [QuoteFun, [quote, '$expr']], '$expr']
]) :-
    quoted_syntax_fun(QuoteFun).

petta_state_compat_decls(Decls) :-
    petta_state_clear_fun(ClearFun),
    petta_state_set_fun(SetFun),
    petta_state_get_fun(GetFun),
    petta_state_cell_fun(CellFun),
    Decls = [
        ['=', [ClearFun, '$name'],
         [let, '$__tr_state_removed',
          [collapse,
           [match, '&self', [CellFun, '$name', '$old'],
            ['remove-atom', '&self', [CellFun, '$name', '$old']]]],
          'True']],
        ['=', [SetFun, '$name', '$value'],
         [let, '$__tr_state_cleared', [ClearFun, '$name'],
          [let, '$__tr_state_added',
           ['add-atom', '&self', [CellFun, '$name', '$value']],
           'True']]],
        ['=', [GetFun, '$name'],
         [match, '&self', [CellFun, '$name', '$value'], '$value']]
    ].

rewrite_builtin_test_decl(['=', LHS, RHS], ['=', RLHS, RRHS]) :-
    !,
    rewrite_builtin_test_term(LHS, RLHS),
    rewrite_builtin_test_term(RHS, RRHS).
rewrite_builtin_test_decl(Term, Rewritten) :-
    rewrite_builtin_test_term(Term, Rewritten).

rewrite_builtin_test_term([test, Actual, Expected],
                          Rewritten) :-
    !,
    rewrite_builtin_test_term(Actual, RActual),
    rewrite_builtin_test_term(Expected, RExpected),
    (   alpha_runtime_bool_test_actual(RActual, Expected),
        lift_alpha_runtime_bool_actual(RActual, Binder, Value)
    ->  petta_test_runtime_bool_fun(TestFun),
        Rewritten = [let, Binder, Value, [TestFun, Binder, RExpected]]
    ;   builtin_test_helper_head(Actual, Expected, TestFun),
        Rewritten = [TestFun, RActual, RExpected]
    ).
rewrite_builtin_test_term(List, Rewritten) :-
    is_list(List), !,
    maplist(rewrite_builtin_test_term, List, Rewritten).
rewrite_builtin_test_term(Term, Term).

builtin_test_helper_head(Actual, Expected, TestFun) :-
    (   alpha_runtime_bool_test_actual(Actual, Expected)
    ->  petta_test_runtime_bool_fun(TestFun)
    ;   test_call_needs_bag_equality(Actual)
    ->  petta_test_bag_fun(TestFun)
    ;   test_call_needs_collapse(Actual),
        test_expected_literal_data(Expected)
    ->  petta_test_results_data_fun(TestFun)
    ;   test_call_needs_collapse(Actual)
    ->  petta_test_results_fun(TestFun)
    ;   test_expected_literal_data(Expected)
    ->  petta_test_equal_data_fun(TestFun)
    ;   petta_test_equal_fun(TestFun)
    ).

alpha_runtime_bool_test_actual(Actual, Expected) :-
    test_expected_bool_literal(Expected),
    alpha_runtime_bool_actual(Actual).

alpha_runtime_bool_actual(['=alpha', _, _]).
alpha_runtime_bool_actual([let, Binder, Value, Body]) :-
    atom(Binder),
    Binder == Body,
    alpha_runtime_helper_call(Value).

alpha_runtime_helper_call([Head|_]) :-
    petta_alpha_equal_eval_fun(Head).

test_expected_bool_literal('True').
test_expected_bool_literal('False').

lift_alpha_runtime_bool_actual([let, Binder, Value, Body], Binder, Value) :-
    atom(Binder),
    Binder == Body,
    alpha_runtime_helper_call(Value).

test_expected_literal_data([quote, _]) :-
    !.
test_expected_literal_data(Term) :-
    atom(Term),
    \+ callable_arity(Term, 0),
    !.
test_expected_literal_data(Term) :-
    \+ is_list(Term),
    !.
test_expected_literal_data([Head|_]) :-
    is_list(Head),
    !.
test_expected_literal_data([Head|_]) :-
    atom(Head),
    \+ source_variable_atom(Head),
    \+ callable_arity(Head, _),
    \+ test_expected_eval_head(Head).

test_expected_eval_head(progn).
test_expected_eval_head(prog1).
test_expected_eval_head(if).
test_expected_eval_head(case).
test_expected_eval_head(let).
test_expected_eval_head('let*').
test_expected_eval_head(chain).
test_expected_eval_head(foldall).
test_expected_eval_head(forall).
test_expected_eval_head(match).
test_expected_eval_head(collapse).
test_expected_eval_head(superpose).
test_expected_eval_head(hyperpose).
test_expected_eval_head(call).
test_expected_eval_head(eval).
test_expected_eval_head(reduce).
test_expected_eval_head(once).
test_expected_eval_head(select).
test_expected_eval_head('map-atom').
test_expected_eval_head('filter-atom').
test_expected_eval_head('foldl-atom').
test_expected_eval_head(maplist).
test_expected_eval_head('add-atom').
test_expected_eval_head('remove-atom').
test_expected_eval_head(empty).

test_call_needs_bag_equality([collapse, Actual]) :-
    collapse_test_needs_bag_equality(Actual).

collapse_test_needs_bag_equality([Head|Args]) :-
    atom(Head),
    length(Args, Arity),
    tr_head_normalized_fun(Head, Arity),
    !.
collapse_test_needs_bag_equality(Term) :-
    is_list(Term),
    member(Subterm, Term),
    collapse_test_needs_bag_equality(Subterm).

test_call_needs_collapse(Actual) :-
    \+ explicit_collection_test_actual(Actual),
    \+ deterministic_runtime_helper_actual(Actual),
    (   contains_uncollected_nondet_surface(Actual)
    ;   calls_multi_clause_source_fun(Actual)
    ;   contains_free_source_variable_control_surface(Actual)
    ).

explicit_collection_test_actual([collapse, _]).

deterministic_runtime_helper_actual([let, Binder, Value, Body]) :-
    atom(Binder),
    Binder == Body,
    runtime_helper_call(Value),
    !.

runtime_helper_call([Head|_]) :-
    runtime_helper_head(Head).

runtime_helper_head(Head) :-
    petta_alpha_equal_eval_fun(Head),
    !.
runtime_helper_head(Head) :-
    petta_runtime_call_fun(Head),
    !.
runtime_helper_head(Head) :-
    petta_runtime_eval_fun(Head),
    !.
runtime_helper_head(Head) :-
    petta_runtime_reduce_fun(Head).

contains_free_source_variable_control_surface(Term) :-
    Term = [Head|_],
    control_surface_head(Head),
    term_has_free_source_variable(Term),
    !.
contains_free_source_variable_control_surface(Term) :-
    Term = [Head|_],
    petta_if2_fun(Head),
    term_has_free_source_variable(Term),
    !.
contains_free_source_variable_control_surface(Term) :-
    is_list(Term),
    member(Subterm, Term),
    contains_free_source_variable_control_surface(Subterm).

control_surface_head(if).
control_surface_head(case).
control_surface_head(let).
control_surface_head('let*').
control_surface_head(chain).
control_surface_head(foldall).
control_surface_head(forall).

term_has_free_source_variable(Term) :-
    term_has_free_source_variable(Term, []).

term_has_free_source_variable(Term, Bound) :-
    atom(Term),
    source_variable_atom(Term),
    \+ memberchk(Term, Bound),
    !.
term_has_free_source_variable([quote, _], _) :-
    !,
    fail.
term_has_free_source_variable([let, Binder, Value, Body], Bound) :-
    !,
    (   term_has_free_source_variable(Value, Bound)
    ;   pattern_bound_source_variables(Binder, BinderVars),
        append(BinderVars, Bound, BodyBound),
        term_has_free_source_variable(Body, BodyBound)
    ).
term_has_free_source_variable(['let*', Bindings, Body], Bound) :-
    !,
    term_has_free_source_variable_let_bindings(Bindings, Bound, Body).
term_has_free_source_variable([chain, Expr, Binder, Body], Bound) :-
    !,
    (   term_has_free_source_variable(Expr, Bound)
    ;   pattern_bound_source_variables(Binder, BinderVars),
        append(BinderVars, Bound, BodyBound),
        term_has_free_source_variable(Body, BodyBound)
    ).
term_has_free_source_variable(['|->', Params, Body], Bound) :-
    !,
    pattern_bound_source_variables(Params, ParamVars),
    append(ParamVars, Bound, BodyBound),
    term_has_free_source_variable(Body, BodyBound).
term_has_free_source_variable([case, Expr, Branches], Bound) :-
    !,
    (   term_has_free_source_variable(Expr, Bound)
    ;   case_branches_have_free_source_variable(Branches, Bound)
    ).
term_has_free_source_variable(Term, Bound) :-
    is_list(Term),
    member(Subterm, Term),
    term_has_free_source_variable(Subterm, Bound).

term_has_free_source_variable_let_bindings([], Bound, Body) :-
    term_has_free_source_variable(Body, Bound).
term_has_free_source_variable_let_bindings([[Binder, Value]|Rest], Bound, Body) :-
    (   term_has_free_source_variable(Value, Bound)
    ;   pattern_bound_source_variables(Binder, BinderVars),
        append(BinderVars, Bound, NextBound),
        term_has_free_source_variable_let_bindings(Rest, NextBound, Body)
    ).

case_branches_have_free_source_variable([], _) :-
    fail.
case_branches_have_free_source_variable([[Pattern, Result]|Rest], Bound) :-
    pattern_bound_source_variables(Pattern, PatternVars),
    append(PatternVars, Bound, ResultBound),
    (   term_has_free_source_variable(Result, ResultBound)
    ;   case_branches_have_free_source_variable(Rest, Bound)
    ).

pattern_bound_source_variables(Term, Vars) :-
    pattern_bound_source_variables_acc(Term, [], RawVars),
    sort(RawVars, Vars).

pattern_bound_source_variables_acc(Term, Acc, [Term|Acc]) :-
    source_variable_atom(Term),
    !.
pattern_bound_source_variables_acc(Term, Acc0, Acc) :-
    is_list(Term),
    !,
    pattern_bound_source_variables_list(Term, Acc0, Acc).
pattern_bound_source_variables_acc(_, Acc, Acc).

pattern_bound_source_variables_list([], Acc, Acc).
pattern_bound_source_variables_list([Term|Rest], Acc0, Acc) :-
    pattern_bound_source_variables_acc(Term, Acc0, Acc1),
    pattern_bound_source_variables_list(Rest, Acc1, Acc).

contains_uncollected_nondet_surface([if, _, _]) :-
    !.
contains_uncollected_nondet_surface([collapse, _]) :-
    !,
    fail.
contains_uncollected_nondet_surface([once, _]) :-
    !,
    fail.
contains_uncollected_nondet_surface([Head|_]) :-
    memberchk(Head, [match, superpose, hyperpose]),
    !.
contains_uncollected_nondet_surface(Term) :-
    is_list(Term),
    member(Subterm, Term),
    contains_uncollected_nondet_surface(Subterm).

calls_multi_clause_source_fun([Head|_]) :-
    atom(Head),
    tr_source_fun_count(Head, Count),
    Count > 1,
    !.
calls_multi_clause_source_fun(Term) :-
    is_list(Term),
    member(Subterm, Term),
    calls_multi_clause_source_fun(Subterm).
