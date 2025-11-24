% Simple existential quantifier example
% Someone loves everyone. Therefore, everyone is loved by someone.

fof(someone_loves_all, axiom,
    ? [X] : ! [Y] : loves(X,Y)).

fof(all_loved, conjecture,
    ! [Y] : ? [X] : loves(X,Y)).
