%------------------------------------------------------------------------------
% File     : knights_knaves.p
% Domain   : Puzzles (Logic)
% Problem  : Knights and Knaves - Island puzzle
% Version  : Propositional encoding
% English  : On an island, knights always tell the truth and knaves always lie.
%            You meet two inhabitants, A and B.
%            A says: "At least one of us is a knave"
%            B says nothing.
%            What are A and B?
%
%            Solution: A is a knight, B is a knave.
%
%            Encoding:
%            - knight_a: A is a knight
%            - knight_b: B is a knight
%            - knave_a: A is a knave
%            - knave_b: B is a knave
%            - statement_a: "At least one of us is a knave" = knave_a | knave_b
%
% Refs     : Classic Raymond Smullyan puzzle
% Status   : Theorem
%------------------------------------------------------------------------------

%----Basic constraints: Everyone is either a knight or a knave (but not both)

fof(a_is_knight_or_knave, axiom,
    knight_a | knave_a ).

fof(b_is_knight_or_knave, axiom,
    knight_b | knave_b ).

fof(a_not_both, axiom,
    ~ (knight_a & knave_a) ).

fof(b_not_both, axiom,
    ~ (knight_b & knave_b) ).

%----A's statement: "At least one of us is a knave"
%----This statement is: knave_a | knave_b

fof(statement_true_def, axiom,
    statement_a <=> (knave_a | knave_b) ).

%----Knights tell truth: If A is a knight, then A's statement is true

fof(a_knight_implies_truth, axiom,
    knight_a => statement_a ).

%----Knaves lie: If A is a knave, then A's statement is false

fof(a_knave_implies_false, axiom,
    knave_a => ~ statement_a ).

%----Goal: Prove A is a knight and B is a knave

fof(conclusion, conjecture,
    knight_a & knave_b ).

%------------------------------------------------------------------------------
