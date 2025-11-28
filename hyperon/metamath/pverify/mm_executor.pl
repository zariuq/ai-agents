% mm_executor.pl - Call MeTTa processor for each statement
:- module(mm_executor, [process_mm_file/2]).
:- use_module(mm_primitives).

%% process_mm_file(+Filename, +Processor) - Parse and call MeTTa processor
%% Processor is a MeTTa function name (atom) that will be called for each statement
process_mm_file(Filename, Processor) :-
    parse_mm_file(Filename, Statements),
    process_statements(Statements, Processor).

%% process_statements(+Statements, +Processor)
process_statements([], _Processor).
process_statements([Stmt|Rest], Processor) :-
    % Call the MeTTa processor function with the statement
    % The statement Stmt is passed as a Prolog term/tuple to MeTTa
    call(Processor, Stmt),
    process_statements(Rest, Processor).
