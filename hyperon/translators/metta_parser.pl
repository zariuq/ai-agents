%% MeTTa S-Expression Parser (Prolog)
%%
%% Correct-by-construction: handles ALL MeTTa token types.
%% MeTTa lexer rule: tokens are delimited by whitespace, '(', ')' only.
%% Everything else (including $, %, +, -, <, >, =, !, @, etc.) is a symbol char.
%%
%% Council (Carneiro, Knuth): parser correctness is the foundation.
%% Council (Wadler, Pfenning): parse → translate → print, each testable.

:- module(metta_parser, [read_metta_file/2, read_metta_string/2,
                          print_sexpr/1, print_sexpr/2]).
:- use_module(library(readutil)).

%% ═══════════════════════════════════════════════════════════════
%% Public API
%% ═══════════════════════════════════════════════════════════════

%% Read a .metta file → list of Prolog terms
read_metta_file(Path, Atoms) :-
    read_file_to_string(Path, Text, []),
    read_metta_string(Text, Atoms).

%% Parse a MeTTa string → list of Prolog terms
read_metta_string(Text, Atoms) :-
    string_codes(Text, Codes),
    phrase(metta_toplevel(Atoms), Codes, _).

%% ═══════════════════════════════════════════════════════════════
%% Parser (DCG)
%% ═══════════════════════════════════════════════════════════════

%% Top-level: sequence of atoms separated by whitespace/comments
metta_toplevel([A|As]) --> ws, metta_atom(A), !, metta_toplevel(As).
metta_toplevel([]) --> ws.

%% ── Whitespace and comments ─────────────────────────────────────

ws --> [C], { C =< 32 }, !, ws.
ws --> [0';], !, line_comment, ws.    % ; line comment
ws --> [].

line_comment --> [0'\n], !.           % end at newline
line_comment --> [_], !, line_comment. % consume any char
line_comment --> [].                  % end at EOF (must be last)

%% ── Atoms ───────────────────────────────────────────────────────

%% S-expression: ( atom* )
metta_atom(Expr) -->
    [0'(], !, ws, metta_atom_list(Elems), ws, [0')],
    { Expr = Elems }.

%% String literal: "..."
metta_atom(Str) -->
    [0'"], !, string_body(Chars), [0'"],
    { append([0'"], Chars, Tmp),
      append(Tmp, [0'"], Codes),
      atom_codes(Str, Codes) }.

%% Symbol/number: anything that's not whitespace, (, ), ;, "
metta_atom(Atom) -->
    sym_codes([C|Cs]),
    { atom_codes(Atom, [C|Cs]) }.

%% ── Symbol characters ───────────────────────────────────────────
%% MeTTa lexer rule: a symbol is any sequence of non-delimiter characters.
%% Delimiters are: whitespace (<=32), '(', ')', ';', '"'

sym_codes([C|Cs]) --> [C], { is_sym_char(C) }, !, sym_codes(Cs).
sym_codes([]) --> [].

is_sym_char(C) :-
    C > 32,
    C \= 0'(,
    C \= 0'),
    C \= 0';,
    C \= 0'".

%% ── String body ─────────────────────────────────────────────────
%% Handles escaped quotes: \"

string_body([0'\\, 0'" | Cs]) --> [0'\\, 0'"], !, string_body(Cs).
string_body([C|Cs]) --> [C], { C \= 0'" }, !, string_body(Cs).
string_body([]) --> [].

%% ── Atom list (inside parentheses) ──────────────────────────────

metta_atom_list([A|As]) --> metta_atom(A), !, ws, metta_atom_list(As).
metta_atom_list([]) --> [].

%% ═══════════════════════════════════════════════════════════════
%% Printer (S-expression → MeTTa text)
%% ═══════════════════════════════════════════════════════════════

%% Print to current output
print_sexpr(X) :- print_sexpr(current_output, X).

%% Print to stream
print_sexpr(S, X) :- is_list(X), !,
    write(S, '('),
    print_sexpr_list(S, X),
    write(S, ')').
print_sexpr(S, X) :- write(S, X).

print_sexpr_list(_, []).
print_sexpr_list(S, [X]) :- !, print_sexpr(S, X).
print_sexpr_list(S, [X|Xs]) :-
    print_sexpr(S, X), write(S, ' '),
    print_sexpr_list(S, Xs).
