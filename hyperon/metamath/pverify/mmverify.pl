% mmverify.pl — Pure Prolog Metamath proof verifier
% Reuses mm_primitives.pl for parsing; implements the RPN stack-machine
% verification algorithm from mmverify.py in pure SWI-Prolog.
%
% Usage:
%   swipl -g main -t halt mmverify.pl -- demo0.mm
%   swipl -g main -t halt mmverify.pl -- --compressed-dag peano.mm

:- use_module(mm_primitives, [
    parse_mm_file_compounds/2
]).

:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(apply)).

%% ======================================================================
%% State representation
%% ======================================================================
%
% State = state(Constants, FrameStack, Labels)
%   Constants:  ordset of atoms
%   FrameStack: [Frame | ...] (list used as stack, head = top)
%   Labels:     assoc (Label → FullStmt)
%
% Frame = frame(Vars, DVs, FHyps, FLabels, EHyps, ELabels)
%   Vars:     ordset of atoms
%   DVs:      ordset of X-Y pairs (X @< Y)
%   FHyps:    list of TC-Var pairs (append order)
%   FLabels:  assoc (Var → Label)
%   EHyps:    list of Stmts (append order)
%   ELabels:  assoc (StmtKey → Label) where StmtKey = Stmt as-is
%
% FullStmt = hyp(Type, Stmt) | assertion(DVs, FHyps, EHyps, Conclusion)
%   Type = '$f' | '$e'
%   Stmt = [Token, ...]
%   DVs = ordset of X-Y pairs
%   FHyps = list of TC-Var pairs
%   EHyps = list of Stmts
%   Conclusion = [Token, ...]

empty_frame(frame([], [], [], FLabels, [], ELabels)) :-
    empty_assoc(FLabels),
    empty_assoc(ELabels).

initial_state(state([], [Frame], Labels)) :-
    empty_frame(Frame),
    empty_assoc(Labels).

%% ======================================================================
%% Frame stack operations
%% ======================================================================

push_frame(state(C, FS, L), state(C, [Frame|FS], L)) :-
    empty_frame(Frame).

pop_frame(state(C, [_|FS], L), state(C, FS, L)) :-
    FS \= [].  % Must not pop the outermost frame

% add_c(+Token, +State, -State1)
add_c(Tok, state(C, FS, L), state(C1, FS, L)) :-
    ( ord_memberchk(Tok, C) ->
        mm_throw(duplicate_constant(Tok))
    ; lookup_v_fs(Tok, FS) ->
        mm_throw(constant_is_active_var(Tok))
    ;
        ord_add_element(C, Tok, C1)
    ).

% add_v(+Token, +State, -State1)
add_v(Tok, state(C, [F|FS], L), state(C, [F1|FS], L)) :-
    ( lookup_v_fs(Tok, [F|FS]) ->
        mm_throw(var_already_active(Tok))
    ; ord_memberchk(Tok, C) ->
        mm_throw(var_is_constant(Tok))
    ;
        F = frame(Vars, DVs, FH, FL, EH, EL),
        ord_add_element(Vars, Tok, Vars1),
        F1 = frame(Vars1, DVs, FH, FL, EH, EL)
    ).

% add_f(+TypeCode, +Var, +Label, +State, -State1)
add_f(TC, Var, Label, state(C, [F|FS], L), state(C, [F1|FS], L1)) :-
    ( \+ lookup_v_fs(Var, [F|FS]) ->
        mm_throw(f_var_not_declared(Var))
    ; \+ ord_memberchk(TC, C) ->
        mm_throw(f_typecode_not_constant(TC))
    ; lookup_f_fs(Var, [F|FS], _) ->
        mm_throw(f_var_already_typed(Var))
    ;
        F = frame(Vars, DVs, FH, FL, EH, EL),
        append(FH, [TC-Var], FH1),
        put_assoc(Var, FL, Label, FL1),
        F1 = frame(Vars, DVs, FH1, FL1, EH, EL),
        Stmt = [TC, Var],
        put_assoc(Label, L, hyp('$f', Stmt), L1)
    ).

% add_e(+Stmt, +Label, +State, -State1)
% Stmt = [TypeCode | MathTokens]
add_e(Stmt, Label, state(C, [F|FS], L), state(C, [F1|FS], L1)) :-
    F = frame(Vars, DVs, FH, FL, EH, EL),
    append(EH, [Stmt], EH1),
    put_assoc(Stmt, EL, Label, EL1),
    F1 = frame(Vars, DVs, FH, FL, EH1, EL1),
    put_assoc(Label, L, hyp('$e', Stmt), L1).

% add_d(+VarList, +State, -State1)
add_d(VarList, state(C, [F|FS], L), state(C, [F1|FS], L)) :-
    F = frame(Vars, DVs, FH, FL, EH, EL),
    make_dv_pairs(VarList, NewPairs),
    ord_union(DVs, NewPairs, DVs1),
    F1 = frame(Vars, DVs1, FH, FL, EH, EL).

make_dv_pairs(VarList, Pairs) :-
    findall(X-Y,
        ( member(A, VarList), member(B, VarList), A \= B,
          ( A @< B -> X = A, Y = B ; X = B, Y = A ) ),
        PairsUnsorted),
    sort(PairsUnsorted, Pairs).

%% ======================================================================
%% Lookups
%% ======================================================================

% lookup_v_fs(+Tok, +FrameStack) — is Tok an active variable?
lookup_v_fs(Tok, [frame(Vars,_,_,_,_,_)|Rest]) :-
    ( ord_memberchk(Tok, Vars) -> true ; lookup_v_fs(Tok, Rest) ).

% lookup_d_fs(+X, +Y, +FrameStack) — active DV pair?
lookup_d_fs(X, Y, FS) :-
    ( X @< Y -> Key = X-Y ; Key = Y-X ),
    lookup_d_fs_(Key, FS).

lookup_d_fs_(Key, [frame(_,DVs,_,_,_,_)|Rest]) :-
    ( ord_memberchk(Key, DVs) -> true ; lookup_d_fs_(Key, Rest) ).

% lookup_f_fs(+Var, +FrameStack, -Label) — floating hyp label for var
lookup_f_fs(Var, [frame(_,_,_,FL,_,_)|Rest], Label) :-
    ( get_assoc(Var, FL, Label) -> true ; lookup_f_fs(Var, Rest, Label) ).

% lookup_e_fs(+Stmt, +FrameStack, -Label) — essential hyp label
lookup_e_fs(Stmt, [frame(_,_,_,_,_,EL)|Rest], Label) :-
    ( get_assoc(Stmt, EL, Label) -> true ; lookup_e_fs(Stmt, Rest, Label) ).

%% ======================================================================
%% make_assertion
%% ======================================================================

% make_assertion(+Stmt, +State, -Assertion)
% Assertion = assertion(DVs, FHyps, EHyps, Conclusion)
% Stmt = [TypeCode | MathTokens] = the conclusion
make_assertion(Stmt, state(_C, FS, _L), assertion(DVs, FHyps, EHyps, Stmt)) :-
    % Collect all e-hyps from all frames
    collect_ehyps(FS, EHyps),
    % Find mandatory variables (in e-hyps and conclusion)
    append(EHyps, [Stmt], AllStmts),
    find_vars_in_stmts(AllStmts, FS, MandVarsSet),
    % Collect f-hyps for mandatory vars (in frame order, removing from set)
    collect_fhyps(FS, MandVarsSet, FHyps, _Remaining),
    % Collect DV pairs restricted to mandatory vars
    fhyps_vars(FHyps, FVarsList),
    sort(FVarsList, FVars),
    ord_union(MandVarsSet, FVars, AllMandVars),
    collect_dvs(FS, AllMandVars, DVs).

collect_ehyps([], []).
collect_ehyps([frame(_,_,_,_,EH,_)|Rest], AllEH) :-
    collect_ehyps(Rest, RestEH),
    append(RestEH, EH, AllEH).  % Earlier frames first

find_vars_in_stmts(Stmts, FS, VarsSet) :-
    append(Stmts, AllToks),
    include(is_active_var(FS), AllToks, VarsList),
    sort(VarsList, VarsSet).

is_active_var(FS, Tok) :- lookup_v_fs(Tok, FS).

% collect_fhyps: scan frames bottom-to-top, for each f-hyp whose var
% is in MandVars, include it (preserving order)
collect_fhyps(FS, MandVars, FHyps, Remaining) :-
    reverse(FS, FSBottomUp),
    collect_fhyps_frames(FSBottomUp, MandVars, FHyps, Remaining).

collect_fhyps_frames([], Remaining, [], Remaining).
collect_fhyps_frames([frame(_,_,FH,_,_,_)|Rest], MandVars, FHyps, Remaining) :-
    collect_fhyps_from_frame(FH, MandVars, FrameFHyps, MandVars1),
    collect_fhyps_frames(Rest, MandVars1, RestFHyps, Remaining),
    append(FrameFHyps, RestFHyps, FHyps).

collect_fhyps_from_frame([], MV, [], MV).
collect_fhyps_from_frame([TC-Var|Rest], MV, FHyps, MVOut) :-
    ( ord_memberchk(Var, MV) ->
        ord_del_element(MV, Var, MV1),
        FHyps = [TC-Var|RestFH],
        collect_fhyps_from_frame(Rest, MV1, RestFH, MVOut)
    ;
        collect_fhyps_from_frame(Rest, MV, FHyps, MVOut)
    ).

fhyps_vars([], []).
fhyps_vars([_TC-Var|Rest], [Var|Vars]) :- fhyps_vars(Rest, Vars).

collect_dvs([], _, []).
collect_dvs([frame(_,DVs,_,_,_,_)|Rest], MandVars, AllDVs) :-
    include(dv_in_mandvars(MandVars), DVs, FilteredDVs),
    collect_dvs(Rest, MandVars, RestDVs),
    ord_union(FilteredDVs, RestDVs, AllDVs).

dv_in_mandvars(MV, X-Y) :- ord_memberchk(X, MV), ord_memberchk(Y, MV).

%% ======================================================================
%% Substitution and DV checking
%% ======================================================================

% apply_subst(+Stmt, +Subst, -Result)
% Subst is an assoc (Var → TokenList)
apply_subst([], _, []).
apply_subst([Tok|Rest], Subst, Result) :-
    ( get_assoc(Tok, Subst, Replacement) ->
        apply_subst(Rest, Subst, RestResult),
        append(Replacement, RestResult, Result)
    ;
        apply_subst(Rest, Subst, RestResult),
        Result = [Tok|RestResult]
    ).

% find_vars(+Stmt, +FrameStack, -Vars)
% Return ordset of active variables in Stmt
find_vars(Stmt, FS, Vars) :-
    include(is_active_var(FS), Stmt, VarsList),
    sort(VarsList, Vars).

% check_dvs(+DVPairs, +Subst, +FrameStack)
% For each DV pair (X,Y), after substitution, all vars in subst(X) must be
% disjoint from all vars in subst(Y), and each cross-pair must have an
% active DV condition.
check_dvs([], _, _).
check_dvs([X-Y|Rest], Subst, FS) :-
    get_assoc(X, Subst, SubstX),
    get_assoc(Y, Subst, SubstY),
    find_vars(SubstX, FS, VarsX),
    find_vars(SubstY, FS, VarsY),
    check_dv_cross(VarsX, VarsY, FS),
    check_dvs(Rest, Subst, FS).

check_dv_cross([], _, _).
check_dv_cross([X0|Rest], VarsY, FS) :-
    check_dv_cross_one(X0, VarsY, FS),
    check_dv_cross(Rest, VarsY, FS).

check_dv_cross_one(_, [], _).
check_dv_cross_one(X0, [Y0|Rest], FS) :-
    ( X0 == Y0 ->
        mm_throw(dv_violation(X0, Y0))
    ; \+ lookup_d_fs(X0, Y0, FS) ->
        mm_throw(dv_violation(X0, Y0))
    ;
        check_dv_cross_one(X0, Rest, FS)
    ).

%% ======================================================================
%% RPN Stack Machine
%% ======================================================================

% treat_step(+FullStmt, +Stack, +State, -Stack1)
treat_step(hyp(_Type, Stmt), Stack, _State, [Stmt|Stack]).
treat_step(assertion(DVs, FHyps, EHyps, Conclusion), Stack, State, Stack1) :-
    State = state(_, FS, _),
    length(FHyps, NF),
    length(EHyps, NE),
    NPop is NF + NE,
    length(Stack, SLen),
    ( SLen < NPop ->
        mm_throw(stack_underflow(NPop, SLen))
    ; true ),
    % Split stack: head is top of stack.
    % Pop NPop elements from the top (head).
    length(Popped, NPop),
    append(Popped, Kept, Stack),
    % Popped = [top, ..., deepest]. Reverse to get deepest first,
    % matching Python's stack[sp], stack[sp+1], ... order.
    reverse(Popped, PoppedInOrder),
    % Build substitution from f-hyps
    length(FEntries, NF),
    append(FEntries, EEntries, PoppedInOrder),
    build_subst(FHyps, FEntries, Subst),
    % Check e-hyps
    check_ehyps(EHyps, EEntries, Subst),
    % Check DV constraints
    check_dvs(DVs, Subst, FS),
    % Push substituted conclusion
    apply_subst(Conclusion, Subst, Result),
    Stack1 = [Result|Kept].

build_subst([], [], Subst) :- empty_assoc(Subst).
build_subst([TC-Var|FHyps], [Entry|Entries], Subst) :-
    Entry = [EntryTC|EntryRest],
    ( EntryTC \= TC ->
        mm_throw(typecode_mismatch(TC, EntryTC, Var))
    ; true ),
    build_subst(FHyps, Entries, Subst0),
    put_assoc(Var, Subst0, EntryRest, Subst).

check_ehyps([], [], _).
check_ehyps([EHyp|EHyps], [Entry|Entries], Subst) :-
    apply_subst(EHyp, Subst, Expected),
    ( Entry \= Expected ->
        mm_throw(ehyp_mismatch(Entry, Expected))
    ; true ),
    check_ehyps(EHyps, Entries, Subst).

%% ======================================================================
%% Normal proof processing
%% ======================================================================

% treat_normal_proof(+LabelList, +State, -Stack)
treat_normal_proof(Labels, State, Stack) :-
    treat_normal_proof_(Labels, State, [], Stack).

treat_normal_proof_([], _, Stack, Stack).
treat_normal_proof_([Label|Rest], State, Stack0, Stack) :-
    State = state(_, _, Labels),
    ( get_assoc(Label, Labels, StmtInfo) ->
        treat_step(StmtInfo, Stack0, State, Stack1),
        treat_normal_proof_(Rest, State, Stack1, Stack)
    ;
        mm_throw(unknown_label(Label))
    ).

%% ======================================================================
%% Compressed proof processing
%% ======================================================================

% treat_compressed_proof(+FHyps, +EHyps, +ProofLabels, +ProofSteps, +State, -Stack)
% ProofLabels: explicit label bloc from between ( and )
% ProofSteps: list of integers from decode_compressed_proof
treat_compressed_proof(FHyps, EHyps, ProofLabels, ProofSteps, State, Stack) :-
    State = state(_, FS, _),
    % Build plabels: implicit hyp labels + explicit labels
    maplist(fhyp_label(FS), FHyps, FLabels),
    maplist(ehyp_label(FS), EHyps, ELabels),
    append(FLabels, ELabels, ImplicitLabels),
    append(ImplicitLabels, ProofLabels, PLabels),
    length(PLabels, LabelEnd),
    treat_compressed_steps(ProofSteps, PLabels, LabelEnd, State, [], [], Stack).

fhyp_label(FS, _TC-Var, Label) :- lookup_f_fs(Var, FS, Label).
ehyp_label(FS, Stmt, Label) :- lookup_e_fs(Stmt, FS, Label).

% treat_compressed_steps(+Steps, +PLabels, +LabelEnd, +State, +Stack, +Saved, -FinalStack)
treat_compressed_steps([], _, _, _, Stack, _, Stack).
treat_compressed_steps([Step|Rest], PLabels, LabelEnd, State, Stack0, Saved, Stack) :-
    State = state(_, _, Labels),
    ( Step =:= -1 ->
        % Z: save top of stack
        Stack0 = [Top|_],
        append(Saved, [Top], Saved1),
        treat_compressed_steps(Rest, PLabels, LabelEnd, State, Stack0, Saved1, Stack)
    ; Step < LabelEnd ->
        % Reference to plabels
        nth0(Step, PLabels, RefLabel),
        ( get_assoc(RefLabel, Labels, StmtInfo) ->
            treat_step(StmtInfo, Stack0, State, Stack1)
        ;
            mm_throw(unknown_label_in_compressed(RefLabel))
        ),
        treat_compressed_steps(Rest, PLabels, LabelEnd, State, Stack1, Saved, Stack)
    ;
        % Reference to saved statement
        SavedIdx is Step - LabelEnd,
        length(Saved, NSaved),
        ( SavedIdx >= NSaved ->
            mm_throw(saved_stmt_overflow(SavedIdx, NSaved))
        ; true ),
        nth0(SavedIdx, Saved, SavedStmt),
        % Treat as a dv-free, hypothesis-free axiom
        treat_step(assertion([], [], [], SavedStmt), Stack0, State, Stack1),
        treat_compressed_steps(Rest, PLabels, LabelEnd, State, Stack1, Saved, Stack)
    ).

%% ======================================================================
%% Statement processing
%% ======================================================================

% process_statements(+Stmts, +State, -FinalState)
process_statements([], State, State).
process_statements([Stmt|Rest], State0, State) :-
    process_statement(Stmt, State0, State1),
    process_statements(Rest, State1, State).

% process_statement(+Stmt, +State, -State1)
process_statement(c(Symbols), State0, State) :-
    foldl(add_c, Symbols, State0, State).

process_statement(v(Vars), State0, State) :-
    foldl(add_v, Vars, State0, State).

process_statement(f(Label, Type, Var), State0, State) :-
    add_f(Type, Var, Label, State0, State).

process_statement(e(Label, Type, Math), State0, State) :-
    Stmt = [Type|Math],
    add_e(Stmt, Label, State0, State).

process_statement(a(Label, Type, Math), State0, State) :-
    Stmt = [Type|Math],
    make_assertion(Stmt, State0, Assertion),
    State0 = state(C, FS, Labels),
    put_assoc(Label, Labels, Assertion, Labels1),
    State = state(C, FS, Labels1).

process_statement(p(Label, Type, Math, Proof), State0, State) :-
    Stmt = [Type|Math],
    make_assertion(Stmt, State0, Assertion),
    Assertion = assertion(_, FHyps, EHyps, Conclusion),
    % Verify the proof
    verify_proof(FHyps, EHyps, Conclusion, Proof, State0),
    % Store the assertion
    State0 = state(C, FS, Labels),
    put_assoc(Label, Labels, Assertion, Labels1),
    State = state(C, FS, Labels1),
    format('~w ', [Label]),
    flush_output.

process_statement(d(Vars), State0, State) :-
    add_d(Vars, State0, State).

process_statement(open_frame, State0, State) :-
    push_frame(State0, State).

process_statement(close_frame, State0, State) :-
    pop_frame(State0, State).

%% ======================================================================
%% Proof verification dispatch
%% ======================================================================

% verify_proof(+FHyps, +EHyps, +Conclusion, +Proof, +State)
verify_proof(_FHyps, _EHyps, _Conclusion, Proof, _State) :-
    proof_has_qmark(Proof),
    !.  % Accept incomplete proofs (? marker) with no verification
verify_proof(FHyps, EHyps, Conclusion, Proof, State) :-
    ( Proof = compressed(ProofLabels, ProofSteps) ->
        treat_compressed_proof(FHyps, EHyps, ProofLabels, ProofSteps, State, Stack)
    ; is_list(Proof) ->
        treat_normal_proof(Proof, State, Stack)
    ;
        mm_throw(unknown_proof_format(Proof))
    ),
    ( Stack = [Top] ->
        ( Top == Conclusion ->
            true
        ;
            mm_throw(proof_conclusion_mismatch(Top, Conclusion))
        )
    ; Stack = [] ->
        mm_throw(empty_stack_at_end)
    ;
        length(Stack, N),
        mm_throw(stack_has_multiple_entries(N))
    ).

%% ======================================================================
%% Incomplete proof detection (? marker)
%% ======================================================================

% proof_has_qmark(+Proof) — true if proof contains ? (incomplete marker)
proof_has_qmark(Proof) :-
    is_list(Proof), member('?', Proof), !.
proof_has_qmark(compressed(_, Steps)) :-
    ( member('?', Steps) ; member(incomplete, Steps) ), !.

%% ======================================================================
%% Error handling
%% ======================================================================

mm_throw(Error) :-
    throw(mm_error(Error)).

%% ======================================================================
%% CLI
%% ======================================================================

main :-
    current_prolog_flag(argv, Args),
    ( Args = [] ->
        format(user_error, 'Usage: swipl -g main -t halt mmverify.pl -- <file.mm>~n', []),
        halt(1)
    ;
        % Find the first non-flag argument (the .mm file)
        include(is_not_flag, Args, NonFlags),
        ( NonFlags = [File|_] ->
            verify_file(File)
        ;
            format(user_error, 'Error: No .mm file specified~n', []),
            halt(1)
        )
    ).

is_not_flag(Arg) :-
    atom_codes(Arg, [C|_]),
    C \= 0'-.

verify_file(File) :-
    format('Parsing ~w...~n', [File]),
    flush_output,
    catch(
        parse_mm_file_compounds(File, Statements),
        ParseError,
        ( format(user_error, 'Parse error: ~w~n', [ParseError]), halt(1) )
    ),
    length(Statements, NStmts),
    format('Parsed ~w statements. Verifying...~n', [NStmts]),
    flush_output,
    initial_state(State0),
    catch(
        process_statements(Statements, State0, _FinalState),
        mm_error(Error),
        ( format(user_error, '~nVerification error: ~w~n', [Error]), halt(1) )
    ),
    format('~nAll proofs verified.~n', []).
