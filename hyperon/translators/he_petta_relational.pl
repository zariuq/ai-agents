:- module(he_petta_relational,
  [ he_to_petta/4,
    petta_to_he/4,
    fresh_name/4,
    roundtrip_he/5,
    roundtrip_petta/5
  ]).

/*
  A proof-friendly relational core for the HE <-> PeTTa translator.

  Key difference from the current modules:
  - no dynamic global counter
  - freshness is explicit state threading
  - translation is a relation over syntax plus supply, which is far easier to
    reason about in Lean or on paper than a side-effecting translator

  Signatures:
    he_to_petta(+HE, -PeTTa, +S0, -S1).
    petta_to_he(+PeTTa, -HE, +S0, -S1).

  The intended proof obligation is NOT literal syntactic inverse on all terms.
  The right theorem is roundtrip up to alpha/admin equivalence on the common
  fragment.
*/

fresh_name(Prefix, S0, S1, Var) :-
    S1 is S0 + 1,
    atomic_list_concat(['$__tr_', Prefix, '_', S1], Var).

/* ---------------- HE -> PeTTa ---------------- */

he_to_petta([chain, Expr, Var, Body], [let, Var, TExpr, TBody], S0, S2) :-
    he_to_petta(Expr, TExpr, S0, S1),
    he_to_petta(Body, TBody, S1, S2), !.

he_to_petta(['collapse-bind', Inner], [collapse, TInner], S0, S1) :-
    he_to_petta(Inner, TInner, S0, S1), !.

he_to_petta(['superpose-bind', Inner], [superpose, TInner], S0, S1) :-
    he_to_petta(Inner, TInner, S0, S1), !.

/*
  HE stdlib `unique` is generic. PeTTa only has a direct stream-op rewrite for
  unique(superpose ...), so the verified translator lowers any HE unique-term
  through collapse + unique-atom + superpose.
*/
he_to_petta([unique, Arg],
            [let, ListVar, [collapse, TArg],
             [let, UniqueVar, ['unique-atom', ListVar], [superpose, UniqueVar]]],
            S0, S3) :-
    he_to_petta(Arg, TArg, S0, S1),
    fresh_name(collapsed, S1, S2, ListVar),
    fresh_name(unique, S2, S3, UniqueVar), !.

/*
  HE-style conjunction of recursive deductions relies on shared variable
  bindings flowing from the left branch into the right branch. In PeTTa this
  needs to be made explicit with let* sequencing.
*/
he_to_petta(['And', ['deduce', A], ['deduce', B]],
            ['let*', [['T', TLeft], ['T', TRight]], 'T'], S0, S2) :-
    he_to_petta(['deduce', A], TLeft, S0, S1),
    he_to_petta(['deduce', B], TRight, S1, S2), !.

/*
  Branch translation is recursive here, unlike the current one-way module,
  because otherwise nested translated constructs inside branches are missed.
*/
he_to_petta([switch, Scrut, Branches], [case, TScrut, TBranches], S0, S2) :-
    he_to_petta(Scrut, TScrut, S0, S1),
    he_to_petta_branches(Branches, TBranches, S1, S2), !.

he_to_petta(['switch-minimal', Scrut, Branches], [case, TScrut, TBranches], S0, S2) :-
    he_to_petta(Scrut, TScrut, S0, S1),
    he_to_petta_branches(Branches, TBranches, S1, S2), !.

he_to_petta(['atom-subst', Atom, Var, Tmpl], [let, Var, TAtom, TTmpl], S0, S2) :-
    he_to_petta(Atom, TAtom, S0, S1),
    he_to_petta(Tmpl, TTmpl, S1, S2), !.

he_to_petta([nop, X], [let, Fresh, TX, '()'], S0, S2) :-
    fresh_name(discard, S0, S1, Fresh),
    he_to_petta(X, TX, S1, S2), !.

he_to_petta([function, [return, X]], TX, S0, S1) :-
    he_to_petta(X, TX, S0, S1), !.

he_to_petta(List, TList, S0, S1) :-
    is_list(List),
    he_to_petta_list(List, TList, S0, S1), !.

he_to_petta(X, X, S, S).

he_to_petta_list([], [], S, S).
he_to_petta_list([X|Xs], [Y|Ys], S0, S2) :-
    he_to_petta(X, Y, S0, S1),
    he_to_petta_list(Xs, Ys, S1, S2).

he_to_petta_branches([], [], S, S).
he_to_petta_branches([B|Bs], [TB|TBs], S0, S2) :-
    he_to_petta(B, TB, S0, S1),
    he_to_petta_branches(Bs, TBs, S1, S2).

/* ---------------- PeTTa -> HE ---------------- */

petta_to_he([progn|Args], TExpr, S0, S1) :-
    petta_to_he_progn_args(Args, TExpr, S0, S1), !.

petta_to_he([prog1|Args], TExpr, S0, S1) :-
    petta_to_he_prog1_args(Args, TExpr, S0, S1), !.

petta_to_he([foldall, Agg, Goal, Init],
            [let, ListVar, ['collapse', TGoal],
             ['foldl-atom', ListVar, TInit,
              AccVar, ItemVar,
              [eval, [TAgg, AccVar, ItemVar]]]], S0, S6) :-
    petta_to_he(Agg, TAgg, S0, S1),
    petta_to_he(Goal, TGoal, S1, S2),
    petta_to_he(Init, TInit, S2, S3),
    fresh_name(collapsed, S3, S4, ListVar),
    fresh_name(acc, S4, S5, AccVar),
    fresh_name(item, S5, S6, ItemVar), !.

petta_to_he(['unique-atom', [collapse, Arg]], [collapse, [unique, TArg]], S0, S1) :-
    petta_to_he(Arg, TArg, S0, S1), !.

petta_to_he(['@<', A, B], ['<s', TA, TB], S0, S2) :-
    petta_to_he(A, TA, S0, S1),
    petta_to_he(B, TB, S1, S2), !.

petta_to_he(['@>', A, B], [not, ['<s', TA, TB]], S0, S2) :-
    petta_to_he(A, TA, S0, S1),
    petta_to_he(B, TB, S1, S2), !.

petta_to_he(List, TList, S0, S1) :-
    is_list(List),
    petta_to_he_list(List, TList, S0, S1), !.

petta_to_he(X, X, S, S).

petta_to_he_list([], [], S, S).
petta_to_he_list([X|Xs], [Y|Ys], S0, S2) :-
    petta_to_he(X, Y, S0, S1),
    petta_to_he_list(Xs, Ys, S1, S2).

petta_to_he_progn_args([], '()', S, S).
petta_to_he_progn_args([Last], TLast, S0, S1) :-
    petta_to_he(Last, TLast, S0, S1).
petta_to_he_progn_args([Expr|Rest], [let, Fresh, TExpr, TRest], S0, S3) :-
    fresh_name(discard, S0, S1, Fresh),
    petta_to_he(Expr, TExpr, S1, S2),
    petta_to_he_progn_args(Rest, TRest, S2, S3).

petta_to_he_prog1_args([], '()', S, S).
petta_to_he_prog1_args([First], TFirst, S0, S1) :-
    petta_to_he(First, TFirst, S0, S1).
petta_to_he_prog1_args([First|Rest], [let, FreshR, TFirst, TRest], S0, S3) :-
    fresh_name(result, S0, S1, FreshR),
    petta_to_he(First, TFirst, S1, S2),
    petta_to_he_prog1_rest(Rest, FreshR, TRest, S2, S3).

petta_to_he_prog1_rest([], ResultVar, ResultVar, S, S).
petta_to_he_prog1_rest([Expr|Rest], ResultVar, [let, FreshD, TExpr, TRest], S0, S3) :-
    fresh_name(discard, S0, S1, FreshD),
    petta_to_he(Expr, TExpr, S1, S2),
    petta_to_he_prog1_rest(Rest, ResultVar, TRest, S2, S3).

/* ---------------- Roundtrip witnesses ---------------- */

roundtrip_he(HE, PeTTa, HE2, S0, S2) :-
    he_to_petta(HE, PeTTa, S0, S1),
    petta_to_he(PeTTa, HE2, S1, S2).

roundtrip_petta(PeTTa, HE, PeTTa2, S0, S2) :-
    petta_to_he(PeTTa, HE, S0, S1),
    he_to_petta(HE, PeTTa2, S1, S2).
