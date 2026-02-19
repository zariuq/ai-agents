% env_utils.pl - Environment variable access for PeTTa

% Provide module-export wrappers for mm_primitives so PeTTa can import
% parse/exit predicates via plain consult + import_prolog_function.
:- use_module(mm_primitives).

% get_env_var(+VarName, -Value)
% Get environment variable value
get_env_var(VarName, Value) :-
    getenv(VarName, Value).

% get_env_var_or_default(+VarName, +Default, -Value)
% Get environment variable or use default if not set
get_env_var_or_default(VarName, Default, Value) :-
    ( getenv(VarName, EnvValue)
    -> Value = EnvValue
    ;  Value = Default
    ).

% set_env_var(+VarName, +Value, -Result)
% Set environment variable value and return success
set_env_var(VarName, Value, ok) :-
    setenv(VarName, Value).

% is_flag_arg(+Arg, -Result)
% Check if an argument starts with "--"
% Returns true if it's a flag, false otherwise
is_flag_arg(Arg, true) :-
    atom(Arg),
    atom_codes(Arg, [0'-, 0'-|_]),
    !.
is_flag_arg(_, false).

% Wrappers (non-module namespace) used by pverify MeTTa scripts.
parse_mm_file(File, Statements) :-
    mm_primitives:parse_mm_file(File, Statements).

halt_with_code(Code, Out) :-
    mm_primitives:halt_with_code(Code, Out).
