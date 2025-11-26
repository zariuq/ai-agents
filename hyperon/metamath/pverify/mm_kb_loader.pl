% mm_kb_loader.pl - Load Metamath directly into MeTTa knowledge base
:- module(mm_kb_loader, [load_mm_to_kb/2]).
:- use_module(mm_primitives).

%% load_mm_to_kb(+Filename, +Space) - Parse file and add atoms to MeTTa space
load_mm_to_kb(Filename, Space) :-
    parse_mm_file(Filename, Statements),
    add_statements_to_kb(Statements, Space).

%% add_statements_to_kb(+Statements, +Space)
add_statements_to_kb([], _Space).
add_statements_to_kb([Stmt|Rest], Space) :-
    add_statement_to_kb(Stmt, Space),
    add_statements_to_kb(Rest, Space).

%% add_statement_to_kb(+Statement, +Space) - Add one statement as atom
add_statement_to_kb(Stmt, Space) :-
    % Use MeTTa's add_atom to directly insert the statement
    % The statement structure (c(...), v(...), etc.) becomes a MeTTa atom
    add_atom(Space, Stmt).
