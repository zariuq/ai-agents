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
mm_token_chars([0'$, C|Rest]) -->
    [0'$, C],
    { mm_keyword_char(C) },
    !,
    mm_rest_of_token(Rest).

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
tokenize_mm_file(Filename, Tokens) :-
    read_mm_file(Filename, Codes),
    tokenize_codes(Codes, Tokens).

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
    maplist(compound_to_list, CompoundStmts, Statements).

% parse_mm_file_compounds(+Filename, -Statements)
% Same as parse_mm_file but returns Prolog compounds (for generate_petta_verifier)
parse_mm_file_compounds(Filename, Statements) :-
    tokenize_mm_file(Filename, Tokens),
    phrase(mm_statements(Statements), Tokens, []).

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
