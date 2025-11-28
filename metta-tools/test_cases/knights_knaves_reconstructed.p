%-----------------------------------------------------------------------------
% File     : knights_knaves.p
% Domain   : Puzzles (Logic)
% Problem  : Knights and Knaves - Island puzzle
% English  : On an island, knights always tell the truth and knaves always lie.
%-----------------------------------------------------------------------------

fof(a_is_knight_or_knave,axiom,
    ( knight_a | knave_a ) ).

fof(b_is_knight_or_knave,axiom,
    ( knight_b | knave_b ) ).

fof(a_not_both,axiom,
    ~ (( knight_a & knave_a )) ).

fof(b_not_both,axiom,
    ~ (( knight_b & knave_b )) ).

fof(statement_true_def,axiom,
    ( statement_a <=> ( knave_a | knave_b ) ) ).

fof(a_knight_implies_truth,axiom,
    ( knight_a => statement_a ) ).

fof(a_knave_implies_false,axiom,
    ( knave_a => ~ statement_a ) ).

fof(conclusion,conjecture,
    ( knight_a & knave_b ) ).

%-----------------------------------------------------------------------------
