% env_utils.pl - Environment variable access for PeTTa

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
