% file_utils.pl - Simple file I/O for PeTTa
:- module(file_utils, [read_file_to_string/2, read_file_to_atoms/2, read_file_to_cons/2]).

%% read_file_to_string(+Filename, -String)
%% Read entire file as a single string atom
read_file_to_string(Filename, String) :-
    open(Filename, read, Stream),
    read_string(Stream, _, String),
    close(Stream).

%% read_file_to_atoms(+Filename, -Atoms)
%% Read file and return list of whitespace-separated atoms
%% This is more useful for tokenization
read_file_to_atoms(Filename, Atoms) :-
    read_file_to_string(Filename, String),
    split_string(String, " \t\n\r", " \t\n\r", Strings),
    maplist(atom_string, Atoms, Strings).

%% read_file_to_cons(+Filename, -ConsStructure)
%% Read file and convert directly to Cons(...) structure for MeTTa
read_file_to_cons(Filename, ConsStruct) :-
    read_file_to_atoms(Filename, Atoms),
    list_to_cons(Atoms, ConsStruct).

%% list_to_cons(+List, -ConsStructure)
list_to_cons([], 'Empty').
list_to_cons([H|T], 'Cons'(H, ConsT)) :-
    list_to_cons(T, ConsT).
