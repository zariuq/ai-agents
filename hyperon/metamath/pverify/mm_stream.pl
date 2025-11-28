% mm_stream.pl - Stateful streaming parser for Metamath
% Prolog keeps the token stream; MeTTa just pulls one statement at a time.
:- module(mm_stream,
    [ open_mm_stream/2,   % open_mm_stream(+Filename, -StreamId)
      next_stmt/2,        % next_stmt(+StreamId, -Result)  (Result = end | error | Statement)
      reset_stream/1      % reset_stream(+StreamId)
    ]).

:- use_module(mm_primitives).

:- dynamic mm_stream_state/2.
:- dynamic mm_stream_counter/1.

%% ----------------------------------------------------------------------
%% Stream ID management
%% ----------------------------------------------------------------------

new_stream_id(Id) :-
    (   retract(mm_stream_counter(N))
    ->  N1 is N + 1
    ;   N1 = 1
    ),
    asserta(mm_stream_counter(N1)),
    Id = N1.

%% ----------------------------------------------------------------------
%% Public API
%% ----------------------------------------------------------------------

% open_mm_stream(+Filename, -StreamId)
% Tokenizes the file and stores the token list under a fresh StreamId.
open_mm_stream(Filename, StreamId) :-
    tokenize_mm_file(Filename, Tokens),
    new_stream_id(StreamId),
    asserta(mm_stream_state(StreamId, Tokens)).

% reset_stream(+StreamId)
% Forget any stored tokens for this stream (mainly for testing).
reset_stream(StreamId) :-
    retractall(mm_stream_state(StreamId, _)).

% next_stmt(+StreamId, -Result)
% Result is:
%   - end     : no more statements
%   - error   : parse error
%   - Statement term: c(Symbols) | v(Vars) | f(Label,Type,Var)
%                    | e(Label,Type,Math) | a(Label,Type,Math)
%                    | p(Label,Type,Math,Proof)
%                    | d(Vars) | open_frame | close_frame
next_stmt(StreamId, Result) :-
    (   mm_stream_state(StreamId, Tokens0)
    ->  true
    ;   % Unknown stream id – treat as error
        Result = error,
        !
    ),
    (   Tokens0 == []
    ->  % Nothing left
        Result = end,
        !
    ;   % Delegate to existing next_statement/2
        next_statement(Tokens0, NSResult),
        (   NSResult = ['end']
        ->  Result = end,
            retractall(mm_stream_state(StreamId, _))
        ;   NSResult = ['error']
        ->  Result = error
        ;   NSResult = [Statement, RestTokens]
        ->  retractall(mm_stream_state(StreamId, _)),
            asserta(mm_stream_state(StreamId, RestTokens)),
            Result = Statement
        ;   % Unexpected format
            Result = error
        )
    ).
