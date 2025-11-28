% Classic FOF: All Greeks are mortal (Aristotle's syllogism)
% All men are mortal. All Greeks are men. Therefore, all Greeks are mortal.

fof(all_men_mortal, axiom,
    ![X]: (man(X) => mortal(X))).

fof(all_greeks_men, axiom,
    ![X]: (greek(X) => man(X))).

fof(all_greeks_mortal, conjecture,
    ![X]: (greek(X) => mortal(X))).
