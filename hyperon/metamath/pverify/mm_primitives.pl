% mm_primitives.pl - Low-level parsing primitives for Metamath
% CDTools-inspired with DCG patterns internally
% All parsing LOGIC is in PeTTa - this provides only character-level operations

:- module(mm_primitives, [
    % File I/O
    read_mm_file/2,

    % Exit with error code
    halt_with_code/2,

    % High-level parsing (complete file -> structured statements)
    parse_mm_file/2,

    % Streaming interface (parse and yield statements one-by-one)
    next_statement/2,  % next_statement(+Tokens, -Result) where Result = [Stmt, Rest] | [end] | [error]

    % MeTTa generation (complete file -> .metta file)
    generate_petta_verifier/2,
    generate_petta_verifier/3,

    % High-level tokenization (complete file -> token list)
    tokenize_mm_file/2,

    % Low-level tokenization (function form for PeTTa)
    next_token/3,
    next_token_pair/2,
    skip_whitespace/2,
    skip_comment/2,

    % Character classification
    is_whitespace/1,
    is_mm_printable/1,
    is_dollar/1
]).

:- use_module(library(dcg/basics)).

%% ======================================================================
%% File I/O Primitives
%% ======================================================================

% Read entire file as character codes (NOT string)
% This matches CDTools pattern and is more efficient
read_mm_file(Filename, Codes) :-
    read_file_to_codes(Filename, Codes, []).

%% ======================================================================
%% Character Classification
%% ======================================================================

% Metamath whitespace: space, tab, LF, CR (ASCII 32, 9, 10, 13)
is_whitespace(32).  % Space
is_whitespace(9).   % Tab
is_whitespace(10).  % LF
is_whitespace(13).  % CR

% Metamath printable: ASCII 33-126 (printable non-whitespace)
is_mm_printable(C) :-
    C >= 33,
    C =< 126.

% is_valid_mm_char(+CharCode)
% Valid characters in Metamath: printable ASCII (33-126) or whitespace
is_valid_mm_char(C) :- is_mm_printable(C), !.
is_valid_mm_char(C) :- is_whitespace(C), !.
is_valid_mm_char(12).  % Form feed (allowed per spec)

% Dollar sign (for keyword detection)
is_dollar(0'$).

%% ======================================================================
%% Token Validation (Metamath spec Section 4)
%% ======================================================================

% is_label_char(+CharCode)
% Label tokens: letters, digits, hyphen (-), underscore (_), period (.)
is_label_char(C) :- C >= 0'a, C =< 0'z, !.  % a-z
is_label_char(C) :- C >= 0'A, C =< 0'Z, !.  % A-Z
is_label_char(C) :- C >= 0'0, C =< 0'9, !.  % 0-9
is_label_char(0'-).  % hyphen
is_label_char(0'_).  % underscore
is_label_char(0'.).  % period

% valid_label(+Atom)
% Check if atom is a valid Metamath label
valid_label(Label) :-
    atom(Label),
    atom_codes(Label, Codes),
    Codes \= [],
    forall(member(C, Codes), is_label_char(C)).

% valid_math_symbol(+Atom)
% Math symbols: any printable ASCII except space or $
valid_math_symbol(Symbol) :-
    atom(Symbol),
    atom_codes(Symbol, Codes),
    Codes \= [],
    forall(member(C, Codes), (is_mm_printable(C), C \= 0'$)).

% validate_label(+Label)
% Throws error if label is invalid
validate_label(Label) :-
    (   valid_label(Label)
    ->  true
    ;   format(user_error, 'Error: Invalid label "~w" - must contain only letters, digits, hyphen, underscore, or period~n', [Label]),
        throw(error(invalid_label(Label), _))
    ).

% validate_math_symbol(+Symbol)
% Throws error if math symbol contains $
validate_math_symbol(Symbol) :-
    (   valid_math_symbol(Symbol)
    ->  true
    ;   format(user_error, 'Error: Invalid math symbol "~w" - must not contain $~n', [Symbol]),
        throw(error(invalid_math_symbol(Symbol), _))
    ).

% validate_math_symbols(+SymbolList)
% Validate a list of math symbols
validate_math_symbols([]).
validate_math_symbols([S|Ss]) :-
    validate_math_symbol(S),
    validate_math_symbols(Ss).

%% ======================================================================
%% DCG Grammar (Internal - efficient parsing)
%% ======================================================================

% Skip whitespace (DCG pattern - tail recursive)
mm_whitespace --> [C], { is_whitespace(C) }, !, mm_whitespace.
mm_whitespace --> [].

% Skip comment: $( ... $)
mm_comment --> [0'$, 0'(], skip_until_close.

skip_until_close --> [0'$, 0')], !.
skip_until_close --> [_], skip_until_close.

% Skip whitespace and comments (recursive pattern from CDTools)
% Fixed to handle comments without leading whitespace
mm_ws_or_comment --> mm_whitespace, mm_comment, !, mm_ws_or_comment.
mm_ws_or_comment --> mm_comment, !, mm_ws_or_comment.
mm_ws_or_comment --> mm_whitespace.

% Extract a single token
mm_token(T) -->
    mm_ws_or_comment,
    mm_token_chars(T),
    { T \= [] }.

% Token characters (keywords or identifiers)
% Keywords ($c, $v, etc.) must be followed by whitespace or end
mm_token_chars([0'$, C]) -->
    [0'$, C],
    { mm_keyword_char(C) },
    !.
    % Keywords are single tokens - no continuation

mm_token_chars([C|Rest]) -->
    [C],
    { is_mm_printable(C), C \= 0'$ },
    !,
    mm_rest_of_token(Rest).

mm_token_chars([]) --> [].

% Rest of token (alphanumeric or special chars)
mm_rest_of_token([C|Rest]) -->
    [C],
    { mm_token_char(C) },
    !,
    mm_rest_of_token(Rest).
mm_rest_of_token([]) --> [].

% Valid characters in keywords
mm_keyword_char(0'c).  % $c
mm_keyword_char(0'v).  % $v
mm_keyword_char(0'f).  % $f
mm_keyword_char(0'e).  % $e
mm_keyword_char(0'a).  % $a
mm_keyword_char(0'p).  % $p
mm_keyword_char(0'd).  % $d
mm_keyword_char(0'{).  % ${
mm_keyword_char(0'}).  % $}
mm_keyword_char(0'=).  % $=
mm_keyword_char(0'.).  % $.

% Valid characters in tokens
mm_token_char(C) :-
    is_mm_printable(C),
    \+ is_whitespace(C).

%% ======================================================================
%% Function Form Interface (for PeTTa interop)
%% ======================================================================

% next_token(+Codes, -Token, -Rest)
% Extract next token, skip whitespace/comments
% Returns atom (not code list) for PeTTa convenience
next_token(Codes, Token, Rest) :-
    phrase(mm_token(TokenCodes), Codes, Rest),
    !,
    atom_codes(Token, TokenCodes).
next_token([], '', []).  % End of input

% next_token_pair(+Codes, -Pair)
% Same as next_token but returns (Token, Rest) as a compound term
% This is easier for PeTTa to destructure
% NOTE: Cut (!) is CRITICAL to prevent backtracking and non-determinism in PeTTa
next_token_pair(Codes, pair(Token, Rest)) :-
    next_token(Codes, Token, Rest),
    !.

% skip_whitespace(+Codes, -Result)
% Skip leading whitespace only (not comments)
skip_whitespace(Codes, Result) :-
    phrase(mm_whitespace, Codes, Result).

% skip_comment(+Codes, -Result)
% Skip leading comment if present
skip_comment(Codes, Result) :-
    phrase(mm_ws_or_comment, Codes, Result).

%% ======================================================================
%% High-Level Tokenization (Prolog does ALL the work)
%% ======================================================================

% tokenize_mm_file(+Filename, -Tokens)
% Read file and tokenize in one go - fully deterministic
% Also validates: no non-ASCII chars, no nested comments, no dangling $, whitespace after keywords
tokenize_mm_file(Filename, Tokens) :-
    read_mm_file(Filename, Codes),
    validate_mm_chars(Codes),
    validate_no_nested_comments(Codes),
    validate_no_dangling_dollar(Codes),
    validate_keyword_whitespace(Codes),
    tokenize_codes(Codes, Tokens).

% validate_mm_chars(+Codes)
% Verify all characters are valid Metamath chars (ASCII printable + whitespace)
validate_mm_chars([]).
validate_mm_chars([C|Cs]) :-
    (   is_valid_mm_char(C)
    ->  validate_mm_chars(Cs)
    ;   format(user_error, 'Error: Non-ASCII character code ~w found in file~n', [C]),
        throw(error(invalid_character(C), _))
    ).

% validate_no_nested_comments(+Codes)
% Check that $( does not appear inside a comment
validate_no_nested_comments(Codes) :-
    (   check_nested_comments(Codes, outside)
    ->  true
    ;   format(user_error, 'Error: Nested comment delimiter $( found inside comment~n', []),
        throw(error(nested_comment, _))
    ).

% check_nested_comments(+Codes, +State)
% State = outside | inside
check_nested_comments([], _) :- !.
check_nested_comments([0'$, 0'(|Rest], outside) :-
    !, check_nested_comments(Rest, inside).
check_nested_comments([0'$, 0')|Rest], inside) :-
    !, check_nested_comments(Rest, outside).
check_nested_comments([0'$, 0'(|_], inside) :-
    !, fail.  % Nested $( inside comment
check_nested_comments([_|Rest], State) :-
    check_nested_comments(Rest, State).

% validate_no_dangling_dollar(+Codes)
% Check that file doesn't end with a lone $
validate_no_dangling_dollar(Codes) :-
    (   check_dangling_dollar(Codes)
    ->  true
    ;   format(user_error, 'Error: Dangling $ at end of file~n', []),
        throw(error(dangling_dollar, _))
    ).

check_dangling_dollar(Codes) :-
    check_dangling_dollar(Codes, outside).

check_dangling_dollar([], _) :- !.
check_dangling_dollar([0'$], outside) :- !, fail.  % Single $ at end is invalid (only outside comments)
% Inside comment: skip until $)
check_dangling_dollar([0'$, 0')|Rest], inside) :-
    !,  % $) ends comment
    check_dangling_dollar(Rest, outside).
check_dangling_dollar([_|Rest], inside) :-
    !,  % Skip everything inside comments (including $ followed by anything)
    check_dangling_dollar(Rest, inside).
% Outside comment
check_dangling_dollar([0'$, 0'(|Rest], outside) :-
    !,  % $( starts comment
    check_dangling_dollar(Rest, inside).
check_dangling_dollar([0'$, C|Rest], outside) :-
    !,
    % $ must be followed by valid keyword char or comment closer
    (   mm_keyword_char(C)
    ;   C = 0')   % $) ends comment (shouldn't happen outside, but allow)
    ),
    check_dangling_dollar(Rest, outside).
check_dangling_dollar([_|Rest], outside) :-
    check_dangling_dollar(Rest, outside).

% validate_keyword_whitespace(+Codes)
% Check that $ keywords are followed by whitespace
validate_keyword_whitespace(Codes) :-
    (   check_keyword_whitespace(Codes, outside)
    ->  true
    ;   format(user_error, 'Error: Missing whitespace after $ keyword~n', []),
        throw(error(missing_whitespace, _))
    ).

% State = outside | inside_comment
check_keyword_whitespace([], _) :- !.
check_keyword_whitespace([0'$, 0'(|Rest], outside) :-
    !, check_keyword_whitespace(Rest, inside_comment).
check_keyword_whitespace([0'$, 0')|Rest], inside_comment) :-
    !,
    % Comment close $) must be followed by whitespace or EOF
    % Note: $)$ is NOT valid - tokens must be whitespace-separated
    (   Rest = []
    ->  true  % EOF is ok
    ;   Rest = [Next|_],
        is_whitespace(Next)  % Only whitespace allowed (not $)
    ->  check_keyword_whitespace(Rest, outside)
    ;   fail  % Not followed by whitespace - error per spec
    ).
check_keyword_whitespace([_|Rest], inside_comment) :-
    !, check_keyword_whitespace(Rest, inside_comment).
check_keyword_whitespace([0'$, C|Rest], outside) :-
    mm_keyword_char(C),
    !,
    % Must be followed by whitespace or EOF
    (   Rest = []
    ->  true  % EOF is ok
    ;   Rest = [Next|_],
        (is_whitespace(Next) ; Next = 0'$)  % $ for things like $. or $( comment
    ->  check_keyword_whitespace(Rest, outside)
    ;   fail  % Not followed by whitespace
    ).
check_keyword_whitespace([_|Rest], State) :-
    check_keyword_whitespace(Rest, State).

% tokenize_codes(+Codes, -Tokens)
% Extract all tokens from code list
tokenize_codes(Codes, Tokens) :-
    % Consume tokens until end of input; allow trailing whitespace/comments
    phrase(mm_tokens(Tokens), Codes, []).

%% Collect all tokens into a list of atoms
mm_tokens([Atom|Rest]) -->
    % Reuse the same "one token" rule that next_token/3 uses
    mm_token(TokenCodes),
    !,
    { atom_codes(Atom, TokenCodes) },
    mm_tokens(Rest).

mm_tokens([]) -->
    % At the end, allow any remaining whitespace/comments,
    % but no additional tokens.
    mm_ws_or_comment.

%% ======================================================================
%% Statement Parsing (CDTools-style structured output)
%% ======================================================================

% parse_mm_file(+Filename, -Statements)
% Read file, tokenize, and parse into structured statements
% Returns list of MeTTa-friendly lists (not compounds)
parse_mm_file(Filename, Statements) :-
    tokenize_mm_file(Filename, Tokens),
    phrase(mm_statements(CompoundStmts), Tokens, []),
    validate_frame_balance(CompoundStmts),  % Check with compound form
    validate_semantic_rules(CompoundStmts), % Check semantic rules
    maplist(compound_to_list, CompoundStmts, Statements).

% parse_mm_file_compounds(+Filename, -Statements)
% Same as parse_mm_file but returns Prolog compounds (for generate_petta_verifier)
parse_mm_file_compounds(Filename, Statements) :-
    tokenize_mm_file(Filename, Tokens),
    phrase(mm_statements(Statements), Tokens, []),
    validate_frame_balance(Statements),
    validate_semantic_rules(Statements).

% validate_frame_balance(+Statements)
% Check that ${ and $} are balanced
validate_frame_balance(Stmts) :-
    (   check_frame_balance(Stmts, 0, Final), Final = 0
    ->  true
    ;   format(user_error, 'Error: Unbalanced ${ and $} delimiters~n', []),
        throw(error(unbalanced_frames, _))
    ).

check_frame_balance([], N, N) :- !.
% Handle compound form (with cuts to prevent backtracking)
check_frame_balance([open_frame|Rest], N, Final) :-
    !,  % Commit: don't try catch-all for open_frame
    N1 is N + 1,
    check_frame_balance(Rest, N1, Final).
check_frame_balance([close_frame|Rest], N, Final) :-
    !,  % Commit: don't try catch-all for close_frame
    N > 0,
    N1 is N - 1,
    check_frame_balance(Rest, N1, Final).
% Handle list form (from compound_to_list)
check_frame_balance([[open_frame]|Rest], N, Final) :-
    !,  % Commit: don't try catch-all for [open_frame]
    N1 is N + 1,
    check_frame_balance(Rest, N1, Final).
check_frame_balance([[close_frame]|Rest], N, Final) :-
    !,  % Commit: don't try catch-all for [close_frame]
    N > 0,
    N1 is N - 1,
    check_frame_balance(Rest, N1, Final).
% Catch-all for other statements (after frame cases are committed)
check_frame_balance([_|Rest], N, Final) :-
    check_frame_balance(Rest, N, Final).

%% ======================================================================
%% Semantic Validation (Metamath spec compliance)
%% ======================================================================

% validate_semantic_rules(+Statements)
% Check all semantic rules: no duplicate labels, no label/symbol conflicts, etc.
validate_semantic_rules(Stmts) :-
    collect_symbols_and_labels(Stmts, [], [], [], Consts, Vars, Labels),
    validate_no_duplicate_labels(Labels),
    validate_no_label_symbol_conflicts(Labels, Consts, Vars),
    validate_no_constant_redeclaration(Stmts),
    validate_typecode_is_constant(Stmts, Consts),
    validate_d_contains_only_variables(Stmts, Vars),
    validate_compressed_proof_format(Stmts),
    validate_scoped_rules(Stmts).

% collect_symbols_and_labels(+Stmts, +AccConsts, +AccVars, +AccLabels, -Consts, -Vars, -Labels)
collect_symbols_and_labels([], C, V, L, C, V, L).
collect_symbols_and_labels([c(Syms)|Rest], C0, V, L, C, Vf, Lf) :-
    !,
    append(C0, Syms, C1),
    collect_symbols_and_labels(Rest, C1, V, L, C, Vf, Lf).
collect_symbols_and_labels([v(Syms)|Rest], C, V0, L, Cf, V, Lf) :-
    !,
    append(V0, Syms, V1),
    collect_symbols_and_labels(Rest, C, V1, L, Cf, V, Lf).
collect_symbols_and_labels([f(Label, _, _)|Rest], C, V, L0, Cf, Vf, L) :-
    !,
    collect_symbols_and_labels(Rest, C, V, [Label|L0], Cf, Vf, L).
collect_symbols_and_labels([e(Label, _, _)|Rest], C, V, L0, Cf, Vf, L) :-
    !,
    collect_symbols_and_labels(Rest, C, V, [Label|L0], Cf, Vf, L).
collect_symbols_and_labels([a(Label, _, _)|Rest], C, V, L0, Cf, Vf, L) :-
    !,
    collect_symbols_and_labels(Rest, C, V, [Label|L0], Cf, Vf, L).
collect_symbols_and_labels([p(Label, _, _, _)|Rest], C, V, L0, Cf, Vf, L) :-
    !,
    collect_symbols_and_labels(Rest, C, V, [Label|L0], Cf, Vf, L).
collect_symbols_and_labels([_|Rest], C, V, L, Cf, Vf, Lf) :-
    collect_symbols_and_labels(Rest, C, V, L, Cf, Vf, Lf).

% validate_no_duplicate_labels(+Labels)
% Spec: label tokens must be unique (L179-180)
validate_no_duplicate_labels(Labels) :-
    (   has_duplicates(Labels, Dup)
    ->  format(user_error, 'Error: Duplicate label "~w"~n', [Dup]),
        throw(error(duplicate_label(Dup), _))
    ;   true
    ).

has_duplicates([H|T], H) :- member(H, T), !.
has_duplicates([_|T], Dup) :- has_duplicates(T, Dup).

% validate_no_label_symbol_conflicts(+Labels, +Consts, +Vars)
% Spec: no label may match any math symbol (L179-180)
validate_no_label_symbol_conflicts(Labels, Consts, Vars) :-
    (   member(L, Labels), (member(L, Consts) ; member(L, Vars))
    ->  format(user_error, 'Error: Label "~w" conflicts with math symbol~n', [L]),
        throw(error(label_symbol_conflict(L), _))
    ;   true
    ).

% validate_no_constant_redeclaration(+Stmts)
% Spec: constants may not be redeclared (L161-163)
validate_no_constant_redeclaration(Stmts) :-
    collect_all_constants(Stmts, [], AllConsts),
    (   has_duplicates(AllConsts, Dup)
    ->  format(user_error, 'Error: Constant "~w" redeclared~n', [Dup]),
        throw(error(constant_redeclared(Dup), _))
    ;   true
    ).

collect_all_constants([], Acc, Acc).
collect_all_constants([c(Syms)|Rest], Acc, Result) :-
    !,
    append(Acc, Syms, NewAcc),
    collect_all_constants(Rest, NewAcc, Result).
collect_all_constants([_|Rest], Acc, Result) :-
    collect_all_constants(Rest, Acc, Result).

% validate_typecode_is_constant(+Stmts, +Consts)
% Spec: first symbol in $f must be a constant (L286-292)
validate_typecode_is_constant([], _).
validate_typecode_is_constant([f(_, Type, _)|Rest], Consts) :-
    !,
    (   member(Type, Consts)
    ->  validate_typecode_is_constant(Rest, Consts)
    ;   format(user_error, 'Error: Typecode "~w" in $f is not a declared constant~n', [Type]),
        throw(error(non_constant_typecode(Type), _))
    ).
validate_typecode_is_constant([e(_, Type, _)|Rest], Consts) :-
    !,
    (   member(Type, Consts)
    ->  validate_typecode_is_constant(Rest, Consts)
    ;   format(user_error, 'Error: Typecode "~w" in $e is not a declared constant~n', [Type]),
        throw(error(non_constant_typecode(Type), _))
    ).
validate_typecode_is_constant([a(_, Type, _)|Rest], Consts) :-
    !,
    (   member(Type, Consts)
    ->  validate_typecode_is_constant(Rest, Consts)
    ;   format(user_error, 'Error: Typecode "~w" in $a is not a declared constant~n', [Type]),
        throw(error(non_constant_typecode(Type), _))
    ).
validate_typecode_is_constant([p(_, Type, _, _)|Rest], Consts) :-
    !,
    (   member(Type, Consts)
    ->  validate_typecode_is_constant(Rest, Consts)
    ;   format(user_error, 'Error: Typecode "~w" in $p is not a declared constant~n', [Type]),
        throw(error(non_constant_typecode(Type), _))
    ).
validate_typecode_is_constant([_|Rest], Consts) :-
    validate_typecode_is_constant(Rest, Consts).

% validate_d_contains_only_variables(+Stmts, +Vars)
% Spec: $d must contain only variables (L547-549), and no duplicates (L553-558)
validate_d_contains_only_variables([], _).
validate_d_contains_only_variables([d(DVars)|Rest], Vars) :-
    !,
    % Check all are variables
    (   forall(member(V, DVars), member(V, Vars))
    ->  true
    ;   member(V, DVars), \+ member(V, Vars),
        format(user_error, 'Error: "$d" contains non-variable "~w"~n', [V]),
        throw(error(d_non_variable(V), _))
    ),
    % Check no duplicates in $d (L553-558: $d x x is error)
    (   has_duplicates(DVars, Dup)
    ->  format(user_error, 'Error: "$d" contains duplicate variable "~w"~n', [Dup]),
        throw(error(d_duplicate_var(Dup), _))
    ;   true
    ),
    validate_d_contains_only_variables(Rest, Vars).
validate_d_contains_only_variables([_|Rest], Vars) :-
    validate_d_contains_only_variables(Rest, Vars).

% validate_compressed_proof_format(+Stmts)
% Check compressed proof format: tokens after ) must only contain A-Z and ?
% Spec: AppB - compressed proofs use [A-Z?]+, no digits, no whitespace within token
validate_compressed_proof_format([]).
validate_compressed_proof_format([p(Label, _, _, Proof)|Rest]) :-
    !,
    (   is_compressed_proof(Proof, CompressedPart)
    ->  (   validate_compressed_tokens(CompressedPart)
        ->  true
        ;   format(user_error, 'Error: Invalid compressed proof format in "~w"~n', [Label]),
            throw(error(invalid_compressed_proof(Label), _))
        )
    ;   true  % Not compressed, skip
    ),
    validate_compressed_proof_format(Rest).
validate_compressed_proof_format([_|Rest]) :-
    validate_compressed_proof_format(Rest).

% is_compressed_proof(+Proof, -CompressedPart)
% Detect compressed proof format: [( ... ) COMPRESSED_TOKENS ...]
is_compressed_proof(Proof, Compressed) :-
    Proof = ['('|Rest],
    find_close_paren(Rest, Compressed).

find_close_paren([')'|Rest], Rest) :- !.
find_close_paren([_|T], Rest) :- find_close_paren(T, Rest).

% validate_compressed_tokens(+Tokens)
% Each token must match [A-Z?]+ (no digits, no lowercase)
validate_compressed_tokens([]).
validate_compressed_tokens([Token|Rest]) :-
    atom_codes(Token, Codes),
    forall(member(C, Codes), valid_compressed_char(C)),
    validate_compressed_tokens(Rest).

% valid_compressed_char(+Code)
% Valid chars: A-Z (65-90) and ? (63)
valid_compressed_char(C) :- C >= 65, C =< 90, !.  % A-Z
valid_compressed_char(63).  % ?

%% ======================================================================
%% Scoped Validation (tracks ${ / $} scopes)
%% ======================================================================

% validate_scoped_rules(+Statements)
% Check scope-dependent rules:
%   - Variables in $a/$e/$p must have active $f (test08, test14, test35)
%   - $f variable must be declared in active $v scope (test13)
%   - No two active $f may have same variable (test15, test16)
validate_scoped_rules(Stmts) :-
    % First collect ALL declared variables (global knowledge)
    collect_all_vars(Stmts, AllVars),
    % Then validate with scope tracking
    validate_scoped(Stmts, [], [], [], AllVars).

% collect_all_vars(+Stmts, -AllVars)
% Collect all variable declarations from entire file
collect_all_vars([], []).
collect_all_vars([v(NewVars)|Rest], AllVars) :-
    !,
    collect_all_vars(Rest, RestVars),
    append(NewVars, RestVars, AllVars).
collect_all_vars([_|Rest], AllVars) :-
    collect_all_vars(Rest, AllVars).

% validate_scoped(+Stmts, +ScopeVars, +ActiveFHyps, +ScopeStack, +AllVars)
% ScopeVars: variables declared in current and ancestor scopes (for $f checking)
% ActiveFHyps: list of Var-Type pairs for active $f hypotheses
% ScopeStack: list of [ScopeVars, FHyps] for outer scopes
% AllVars: ALL variables declared in the file (for distinguishing vars from consts)

validate_scoped([], _, _, _, _) :- !.

% ${ - push scope
validate_scoped([open_frame|Rest], ScopeVars, FHyps, Stack, AllVars) :-
    !,
    validate_scoped(Rest, ScopeVars, FHyps, [[ScopeVars, FHyps]|Stack], AllVars).

% $} - pop scope (restore outer scope's state)
validate_scoped([close_frame|Rest], _, _, [[OuterVars, OuterFHyps]|Stack], AllVars) :-
    !,
    validate_scoped(Rest, OuterVars, OuterFHyps, Stack, AllVars).

% $v - add variables to scope
validate_scoped([v(NewVars)|Rest], ScopeVars, FHyps, Stack, AllVars) :-
    !,
    append(ScopeVars, NewVars, UpdatedScopeVars),
    validate_scoped(Rest, UpdatedScopeVars, FHyps, Stack, AllVars).

% $f - add floating hypothesis (check no duplicate variable)
validate_scoped([f(Label, Type, Var)|Rest], ScopeVars, FHyps, Stack, AllVars) :-
    !,
    % Check variable is declared in current/ancestor scope
    (   member(Var, ScopeVars)
    ->  true
    ;   format(user_error, 'Error: $f "~w" uses undeclared variable "~w"~n', [Label, Var]),
        throw(error(f_undeclared_var(Label, Var), _))
    ),
    % Check no duplicate active $f for same variable
    (   member(Var-_, FHyps)
    ->  format(user_error, 'Error: Multiple active $f for variable "~w"~n', [Var]),
        throw(error(multiple_f_same_var(Var), _))
    ;   true
    ),
    validate_scoped(Rest, ScopeVars, [Var-Type|FHyps], Stack, AllVars).

% $e - check variables have active $f
validate_scoped([e(Label, Type, Math)|Rest], ScopeVars, FHyps, Stack, AllVars) :-
    !,
    check_vars_have_active_f(Label, [Type|Math], AllVars, FHyps, e),
    validate_scoped(Rest, ScopeVars, FHyps, Stack, AllVars).

% $a - check variables have active $f
validate_scoped([a(Label, Type, Math)|Rest], ScopeVars, FHyps, Stack, AllVars) :-
    !,
    check_vars_have_active_f(Label, [Type|Math], AllVars, FHyps, a),
    validate_scoped(Rest, ScopeVars, FHyps, Stack, AllVars).

% $p - check variables have active $f
validate_scoped([p(Label, Type, Math, _)|Rest], ScopeVars, FHyps, Stack, AllVars) :-
    !,
    check_vars_have_active_f(Label, [Type|Math], AllVars, FHyps, p),
    validate_scoped(Rest, ScopeVars, FHyps, Stack, AllVars).

% Other statements (c, d, etc.) - skip
validate_scoped([_|Rest], ScopeVars, FHyps, Stack, AllVars) :-
    validate_scoped(Rest, ScopeVars, FHyps, Stack, AllVars).

% check_vars_have_active_f(+Label, +Symbols, +AllVars, +ActiveFHyps, +StmtType)
% Check that every variable in Symbols has an active $f hypothesis
check_vars_have_active_f(_, [], _, _, _) :- !.
check_vars_have_active_f(Label, [Sym|Rest], AllVars, FHyps, StmtType) :-
    (   member(Sym, AllVars)  % Is this symbol a variable (globally)?
    ->  % Yes, check it has active $f
        (   member(Sym-_, FHyps)
        ->  true
        ;   format(user_error, 'Error: Variable "~w" in $~w "~w" has no active $f~n', [Sym, StmtType, Label]),
            throw(error(var_without_active_f(Sym, Label), _))
        )
    ;   true  % Not a variable (constant), skip
    ),
    check_vars_have_active_f(Label, Rest, AllVars, FHyps, StmtType).

% compound_to_list(+CompoundStmt, -ListStmt)
% Convert Prolog compound to list for MeTTa processing
% NOTE: Atoms are converted to strings because mmverify-utils expects strings
compound_to_list(c(Symbols), [c, SymbolsStr]) :- atoms_to_strings(Symbols, SymbolsStr).
compound_to_list(v(Vars), [v, VarsStr]) :- atoms_to_strings(Vars, VarsStr).
compound_to_list(f(Label, Type, Var), [f, LabelStr, TypeStr, VarStr]) :-
    atom_string(Label, LabelStr), atom_string(Type, TypeStr), atom_string(Var, VarStr).
compound_to_list(e(Label, Type, Math), [e, LabelStr, TypeStr, MathStr]) :-
    atom_string(Label, LabelStr), atom_string(Type, TypeStr), atoms_to_strings(Math, MathStr).
compound_to_list(a(Label, Type, Math), [a, LabelStr, TypeStr, MathStr]) :-
    atom_string(Label, LabelStr), atom_string(Type, TypeStr), atoms_to_strings(Math, MathStr).
compound_to_list(p(Label, Type, Math, Proof), [p, LabelStr, TypeStr, MathStr, ProofStr]) :-
    atom_string(Label, LabelStr), atom_string(Type, TypeStr),
    atoms_to_strings(Math, MathStr), atoms_to_strings(Proof, ProofStr).
compound_to_list(d(Vars), [d, VarsStr]) :- atoms_to_strings(Vars, VarsStr).
compound_to_list(open_frame, [open_frame]).
compound_to_list(close_frame, [close_frame]).

% atoms_to_strings(+AtomList, -StringList)
% Convert list of atoms to list of strings
atoms_to_strings([], []).
atoms_to_strings([H|T], [HS|TS]) :-
    atom_string(H, HS),
    atoms_to_strings(T, TS).

% Parse multiple statements
mm_statements([Stmt|Rest]) -->
    mm_statement(Stmt),
    !,
    mm_statements(Rest).
mm_statements([]) --> [].

% Parse individual statements
% $c statement: $c symbols* $.
mm_statement(c(Symbols)) -->
    ['$c'],
    mm_symbols_until_period(Symbols),
    { validate_math_symbols(Symbols) }.

% $v statement: $v vars* $.
mm_statement(v(Vars)) -->
    ['$v'],
    mm_symbols_until_period(Vars),
    { validate_math_symbols(Vars) }.

% $f statement: label $f typecode variable $.
mm_statement(f(Label, Type, Var)) -->
    [Label, '$f', Type, Var, '$.'],
    { Label \= '$c', Label \= '$v', Label \= '$f', Label \= '$e',
      Label \= '$a', Label \= '$p', Label \= '$d',
      Label \= '${', Label \= '$}', Label \= '$=', Label \= '$.',
      validate_label(Label),
      validate_math_symbol(Type),
      validate_math_symbol(Var) }.

% $e statement: label $e typecode math* $.
mm_statement(e(Label, Type, Math)) -->
    [Label, '$e', Type],
    mm_symbols_until_period(Math),
    { Label \= '$c', Label \= '$v', Label \= '$f', Label \= '$e',
      Label \= '$a', Label \= '$p', Label \= '$d',
      Label \= '${', Label \= '$}', Label \= '$=', Label \= '$.',
      validate_label(Label),
      validate_math_symbol(Type),
      validate_math_symbols(Math) }.

% $a statement: label $a typecode math* $.
mm_statement(a(Label, Type, Math)) -->
    [Label, '$a', Type],
    mm_symbols_until_period(Math),
    { Label \= '$c', Label \= '$v', Label \= '$f', Label \= '$e',
      Label \= '$a', Label \= '$p', Label \= '$d',
      Label \= '${', Label \= '$}', Label \= '$=', Label \= '$.',
      validate_label(Label),
      validate_math_symbol(Type),
      validate_math_symbols(Math) }.

% $p statement: label $p typecode math* $= proof $.
mm_statement(p(Label, Type, Math, Proof)) -->
    [Label, '$p', Type],
    mm_symbols_until_equals(Math),
    ['$='],
    mm_symbols_until_period(Proof),
    { Label \= '$c', Label \= '$v', Label \= '$f', Label \= '$e',
      Label \= '$a', Label \= '$p', Label \= '$d',
      Label \= '${', Label \= '$}', Label \= '$=', Label \= '$.',
      validate_label(Label),
      validate_math_symbol(Type),
      validate_math_symbols(Math) }.
      % Note: Proof labels are validated at verification time, not parse time

% $d statement: $d vars* $.
mm_statement(d(Vars)) -->
    ['$d'],
    mm_symbols_until_period(Vars),
    { validate_math_symbols(Vars) }.

% ${ statement: frame open
mm_statement(open_frame) -->
    ['${'].

% $} statement: frame close
mm_statement(close_frame) -->
    ['$}'].

% Helper: collect symbols until $.
mm_symbols_until_period([S|Ss]) -->
    [S],
    { S \= '$.' },
    !,
    mm_symbols_until_period(Ss).
mm_symbols_until_period([]) -->
    ['$.'].

% Helper: collect symbols until $=
mm_symbols_until_equals([S|Ss]) -->
    [S],
    { S \= '$=' },
    !,
    mm_symbols_until_equals(Ss).
mm_symbols_until_equals([]) --> [].

%% ======================================================================
%% Streaming Interface (for PeTTa pipeline)
%% ======================================================================

% next_statement(+Tokens, -Result)
% Parse one statement from token list
% Returns [Statement, RestTokens] for success, ['end'] for end, ['error'] for error
next_statement([], ['end']) :- !.
next_statement(Tokens, [Statement, Rest]) :-
    phrase(mm_statement(Statement), Tokens, Rest),
    !.
next_statement(_, ['error']).

%% ======================================================================
%% MeTTa Generation (mmverify.py-style output)
%% ======================================================================

% generate_petta_verifier(+InputFile, +OutputFile)
% Parse Metamath file and generate PeTTa MeTTa verification code
generate_petta_verifier(InputFile, OutputFile) :-
    generate_petta_verifier(InputFile, OutputFile, true).

% generate_petta_verifier(+InputFile, +OutputFile, +VerifyProofs)
generate_petta_verifier(InputFile, OutputFile, VerifyProofs) :-
    parse_mm_file_compounds(InputFile, Statements),
    open(OutputFile, write, Out),
    emit_header(Out, InputFile, VerifyProofs),
    forall(member(Stmt, Statements),
           emit_metta_stmt(Out, Stmt)),
    emit_footer(Out),
    close(Out).

% Emit MeTTa header with imports
emit_header(Out, InputFile, VerifyProofs) :-
    format(Out, ';;; Auto-generated PeTTa Metamath verifier~n', []),
    format(Out, ';;; Source: ~w~n', [InputFile]),
    format(Out, ';;; Generated by: mm_primitives.pl~n~n', []),
    format(Out, '!(bind! &sp (new-state 0))~n', []),
    format(Out, '!(bind! &fd (new-state 0))~n', []),
    format(Out, '!(import! &self /home/zar/claude/hyperon/PeTTa/lib/lib_he)~n', []),
    format(Out, '!(import! &self /home/zar/claude/hyperon/metamath/mmverify/mmverify-utils_petta)~n', []),
    format(Out, '!(push-frame &fd)~n', []).

% Emit MeTTa footer
emit_footer(Out) :-
    format(Out, '~n;;; Verification complete~n', []).

% Emit individual statements
emit_metta_stmt(Out, c(Symbols)) :-
    forall(member(S, Symbols),
           format(Out, '!(add_c &kb "~w")~n', [S])).

emit_metta_stmt(Out, v(Vars)) :-
    forall(member(V, Vars),
           format(Out, '!(add_v &kb "~w" 1)~n', [V])).

emit_metta_stmt(Out, f(Label, Type, Var)) :-
    format(Out, '!(add_f &kb "~w" "~w" "~w" 1)~n', [Label, Type, Var]).

emit_metta_stmt(Out, e(Label, Type, Math)) :-
    format_math_list(Math, MathStr),
    format(Out, '!(add_e &kb "~w" ("~w"~w) 2)~n', [Label, Type, MathStr]).

emit_metta_stmt(Out, a(Label, Type, Math)) :-
    format_math_list(Math, MathStr),
    format(Out, '!(add_a &kb "~w" ("~w"~w))~n', [Label, Type, MathStr]).

emit_metta_stmt(Out, p(Label, Type, Math, Proof)) :-
    format_math_list(Math, MathStr),
    format_proof_list(Proof, ProofStr),
    format(Out, '!(add_p &kb &stack &sp "~w" ("~w"~w) (~w) True)~n',
           [Label, Type, MathStr, ProofStr]).

emit_metta_stmt(Out, d(Vars)) :-
    format_var_list(Vars, VarStr),
    format(Out, '!(add_d &kb (~w) &fd)~n', [VarStr]).

emit_metta_stmt(Out, open_frame) :-
    format(Out, '!(push-frame &fd)~n', []).

emit_metta_stmt(Out, close_frame) :-
    format(Out, '!(pop-frame &kb &fd)~n', []).

% Format lists for MeTTa output (flat lists with quoted strings)
format_math_list([], '').
format_math_list([S], Str) :-
    format(atom(Str), ' "~w"', [S]).
format_math_list([S|Rest], Str) :-
    Rest \= [],
    format_math_list(Rest, RestStr),
    format(atom(Str), ' "~w"~w', [S, RestStr]).

format_proof_list([], '').
format_proof_list([S], Str) :-
    format(atom(Str), '"~w"', [S]).
format_proof_list([S|Rest], Str) :-
    Rest \= [],
    format_proof_list(Rest, RestStr),
    format(atom(Str), '"~w" ~w', [S, RestStr]).

format_var_list([], '').
format_var_list([V], Str) :-
    format(atom(Str), '"~w"', [V]).
format_var_list([V|Rest], Str) :-
    Rest \= [],
    format_var_list(Rest, RestStr),
    format(atom(Str), '"~w" ~w', [V, RestStr]).

%% ======================================================================
%% Helper Predicates
%% ======================================================================

% Check if code list starts with pattern
starts_with([], _).
starts_with([H|T], [H|PT]) :-
    starts_with(T, PT).

%% ======================================================================
%% Halt with exit code (for error handling from MeTTa)
%% ======================================================================

halt_with_code(Code, true) :- halt(Code).
