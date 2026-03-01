%% pverify_ds.pl — Data structure bridge for PeTTa Metamath verifier
%% Thin wrappers around library(assoc) and library(ordsets) in function
%% convention (last arg = return value) for PeTTa FFI import.
%%
%% Usage from PeTTa:
%%   !(import_prolog_functions_from_file ".../pverify_ds.pl"
%%       (ds_empty_assoc ds_assoc_get ds_assoc_put ...))

:- use_module(library(assoc)).
:- use_module(library(ordsets)).

%% Load mm_primitives from same directory
:- prolog_load_context(directory, Dir),
   atom_concat(Dir, '/mm_primitives', ModPath),
   use_module(ModPath, [parse_mm_file_compounds/2,
                        tokenize_mm_file/2,
                        next_statement/2]).

%% FFI profiling: uses ffi_inc/1 from lib_zar.pl (loaded earlier in same process)

%% ========== Assoc (AVL tree) operations ==========

%% ds_empty_assoc(-Assoc)
ds_empty_assoc(A) :- ffi_inc(ds_empty_assoc), empty_assoc(A).

%% ds_assoc_get(+Key, +Assoc, -Value)
%% Returns value or atom 'not_found'
ds_assoc_get(Key, Assoc, Value) :-
    ffi_inc(ds_assoc_get),
    ( get_assoc(Key, Assoc, V) -> Value = V ; Value = not_found ).

%% ds_assoc_put(+Key, +Value, +Assoc, -NewAssoc)
ds_assoc_put(Key, Value, Assoc, NewAssoc) :-
    ffi_inc(ds_assoc_put),
    put_assoc(Key, Assoc, Value, NewAssoc).

%% ========== Ordset operations ==========

%% ds_empty_ordset(-Set)
ds_empty_ordset([]) :- ffi_inc(ds_empty_ordset).

%% ds_ord_add(+Elem, +Set, -NewSet)
ds_ord_add(Elem, Set, NewSet) :- ffi_inc(ds_ord_add), ord_add_element(Set, Elem, NewSet).

%% ds_ord_member(+Elem, +Set, -Result)
%% Returns true/false (Prolog atoms, works directly in PeTTa if)
ds_ord_member(Elem, Set, Result) :-
    ffi_inc(ds_ord_member),
    ( ord_memberchk(Elem, Set) -> Result = true ; Result = false ).

%% ds_ord_union(+S1, +S2, -Union)
ds_ord_union(S1, S2, Union) :- ffi_inc(ds_ord_union), ord_union(S1, S2, Union).

%% ds_ord_subtract(+S1, +S2, -Diff)
ds_ord_subtract(S1, S2, Diff) :- ffi_inc(ds_ord_subtract), ord_subtract(S1, S2, Diff).

%% ds_ord_from_list(+List, -Set)
ds_ord_from_list(List, Set) :- ffi_inc(ds_ord_from_list), sort(List, Set).

%% ========== Compound decomposition ==========
%% Help PeTTa decompose parser output compounds

%% ds_stmt_functor(+Compound, -Functor)
%% Returns functor name: c, v, f, e, a, p, d, open_frame, close_frame
ds_stmt_functor(Compound, Functor) :-
    ffi_inc(ds_stmt_functor),
    ( atom(Compound) -> Functor = Compound   % open_frame, close_frame
    ; functor(Compound, Functor, _)
    ).

%% ds_stmt_arg(+Compound, +N, -Arg)
%% Get Nth argument (1-based) of a compound
ds_stmt_arg(Compound, N, Arg) :- ffi_inc(ds_stmt_arg), arg(N, Compound, Arg).

%% ========== DV pair helpers ==========

%% ds_make_dv_pairs(+VarList, -Pairs)
%% Generate all oriented X-Y pairs (X @< Y) from variable list, as ordset
ds_make_dv_pairs(VarList, Pairs) :-
    ffi_inc(ds_make_dv_pairs),
    findall(X-Y,
        ( member(A, VarList), member(B, VarList),
          A @< B, X = A, Y = B ),
        PU),
    sort(PU, Pairs).

%% ds_dv_key(+X, +Y, -Key)
%% Orient a DV pair so first @< second
ds_dv_key(X, Y, Key) :-
    ffi_inc(ds_dv_key),
    ( X @< Y -> Key = X-Y ; Key = Y-X ).

%% ds_pair_fst(+Pair, -X)
ds_pair_fst(X-_, X) :- ffi_inc(ds_pair_fst).

%% ds_pair_snd(+Pair, -Y)
ds_pair_snd(_-Y, Y) :- ffi_inc(ds_pair_snd).

%% ds_filter_dvs_mandvars(+DVs, +MandVars, -Filtered)
%% Filter DV ordset to pairs where both vars are in MandVars ordset
ds_filter_dvs_mandvars(DVs, MV, Filtered) :-
    ffi_inc(ds_filter_dvs_mandvars),
    include(dv_both_mandatory(MV), DVs, Filtered).

dv_both_mandatory(MV, X-Y) :-
    ord_memberchk(X, MV), ord_memberchk(Y, MV).

%% ========== Statement (opaque Prolog list) operations ==========
%% Math strings must stay as Prolog lists because they contain literal
%% '(' and ')' tokens which PeTTa interprets as grouping if converted
%% to MeTTa expressions.

%% ds_stmt_cons(+Head, +Tail, -Result)
%% Prepend token to statement list: [Head | Tail]
ds_stmt_cons(Head, Tail, [Head|Tail]) :- ffi_inc(ds_stmt_cons).

%% ds_stmt_head(+Stmt, -Head)
ds_stmt_head([H|_], H) :- ffi_inc(ds_stmt_head).

%% ds_stmt_tail(+Stmt, -Tail)
ds_stmt_tail([_|T], T) :- ffi_inc(ds_stmt_tail).

%% ds_stmt_size(+Stmt, -N)
ds_stmt_size(List, N) :- ffi_inc(ds_stmt_size), length(List, N).

%% ds_stmt_eq(+S1, +S2, -Bool)
%% Compare two statement lists for equality
ds_stmt_eq(S1, S2, Result) :-
    ffi_inc(ds_stmt_eq),
    ( S1 == S2 -> Result = true ; Result = false ).

%% ds_stmt_concat(+S1, +S2, -Result)
%% Concatenate two statement lists
ds_stmt_concat(S1, S2, Result) :- ffi_inc(ds_stmt_concat), append(S1, S2, Result).

%% ds_stmt_empty(-EmptyStmt)
ds_stmt_empty([]) :- ffi_inc(ds_stmt_empty).

%% ds_stmt_from_args(+TC, +Math, -Stmt)
%% Build statement by prepending typecode to math token list
ds_stmt_from_args(TC, Math, [TC|Math]) :- ffi_inc(ds_stmt_from_args).

%% ========== List utilities ==========

ds_length(List, Len) :- ffi_inc(ds_length), length(List, Len).
ds_nth0(N, List, Elem) :- ffi_inc(ds_nth0), nth0(N, List, Elem).
ds_reverse(L, R) :- ffi_inc(ds_reverse), reverse(L, R).

%% ========== Batched operations ==========
%% These replace hot MeTTa loops with single Prolog calls, collapsing
%% N per-token FFI crossings into 1.

%% ds_apply_subst(+Stmt, +Subst, -Result)
%% Apply substitution assoc to statement list in one Prolog call.
%% Equivalent to the MeTTa apply-subst recursive loop.
ds_apply_subst(Stmt, Subst, Result) :-
    ffi_inc(ds_apply_subst),
    ds_apply_subst_(Stmt, Subst, Result).

ds_apply_subst_([], _Subst, []).
ds_apply_subst_([Tok|Rest], Subst, Result) :-
    ds_apply_subst_(Rest, Subst, RestResult),
    ( get_assoc(Tok, Subst, Replacement)
    -> append(Replacement, RestResult, Result)
    ;  Result = [Tok|RestResult]
    ).

%% ds_find_vars(+Stmt, +VarSet, -ResultVars)
%% Find all tokens in Stmt that appear in VarSet (ordset).
%% Returns ordset of matching tokens. Replaces find-vars-acc loop.
ds_find_vars(Stmt, VarSet, ResultVars) :-
    ffi_inc(ds_find_vars),
    ds_find_vars_(Stmt, VarSet, [], ResultVars).

ds_find_vars_([], _VarSet, Acc, Result) :-
    sort(Acc, Result).
ds_find_vars_([Tok|Rest], VarSet, Acc, Result) :-
    ( ord_memberchk(Tok, VarSet)
    -> ds_find_vars_(Rest, VarSet, [Tok|Acc], Result)
    ;  ds_find_vars_(Rest, VarSet, Acc, Result)
    ).

%% ========== Parsing ==========

%% ds_parse_mm(+Filename, -Stmts)
%% Parse .mm file, throw on failure
ds_parse_mm(Filename, Stmts) :-
    ffi_inc(ds_parse_mm),
    ( parse_mm_file_compounds(Filename, Stmts) -> true
    ; throw(mm_error(parse_failed(Filename)))
    ).

%% ========== Streaming parsing ==========
%% Token stream stays in Prolog memory (nb_setval/nb_getval) because
%% token lists contain literal '(' and ')' atoms that PeTTa FFI
%% destructively interprets as grouping.  Only parsed statements
%% (already opaque compounds) cross the FFI boundary.

%% ds_stream_init(+Filename, -Ok)
%% Validate file semantics (same checks as batch parser), then
%% tokenize and store token stream in Prolog global variable.
%% Returns 'ok' on success, throws on validation failure.
ds_stream_init(Filename, ok) :-
    %% First pass: full parse + validation (same as ds_parse_mm)
    %% This catches all semantic errors the batch parser catches.
    ( parse_mm_file_compounds(Filename, _) -> true
    ; throw(mm_error(parse_failed(Filename)))
    ),
    %% Second pass: tokenize for streaming
    tokenize_mm_file(Filename, Tokens),
    nb_setval(mm_token_stream, Tokens).

%% ds_stream_next(-Result)
%% Pull next parsed statement from the stored token stream.
%% Returns: end | error | ns(Statement)
%% On ns(Statement), advances the stream to remaining tokens.
ds_stream_next(Result) :-
    nb_getval(mm_token_stream, Tokens),
    next_statement(Tokens, NSResult),
    ( NSResult = [end]
      -> Result = end
    ; NSResult = [error]
      -> Result = error
    ; NSResult = [Stmt, Rest]
      -> nb_setval(mm_token_stream, Rest),
         Result = ns(Stmt)
    ).
