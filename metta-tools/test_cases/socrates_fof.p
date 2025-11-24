% Classic FOF problem: Socrates is mortal
% All humans are mortal. Socrates is human. Therefore, Socrates is mortal.

fof(all_humans_mortal, axiom,
    ![X]: (human(X) => mortal(X))).

fof(socrates_human, axiom,
    human(socrates)).

fof(socrates_mortal, conjecture,
    mortal(socrates)).
