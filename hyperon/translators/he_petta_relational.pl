:- module(he_petta_relational,
  [ he_to_petta/4,
    petta_to_he/4,
    petta_finite_exists_match_empty_check/6,
    petta_singleton_visible_witness_surface/4,
    petta_append_suffix_head_extension/7,
    petta_append_suffix_let_extension/7,
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

he_to_petta(['singleton-visible-witness', Inner], [once, TInner], S0, S1) :-
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

petta_to_he(['foldl-atom', List, Init, Agg],
            ['foldl-atom', TList, TInit,
             AccVar, ItemVar,
             [eval, [TAgg, AccVar, ItemVar]]], S0, S5) :-
    petta_to_he(List, TList, S0, S1),
    petta_to_he(Init, TInit, S1, S2),
    petta_to_he(Agg, TAgg, S2, S3),
    fresh_name(acc, S3, S4, AccVar),
    fresh_name(item, S4, S5, ItemVar), !.

petta_to_he([quote, Expr], [quote, TExpr], S0, S1) :-
    petta_to_he(Expr, TExpr, S0, S1), !.

petta_to_he([call, Expr], TExpr, S0, S1) :-
    petta_to_he_eval_like(Expr, TExpr, S0, S1), !.

petta_to_he([eval, Expr], TExpr, S0, S1) :-
    petta_to_he_eval_like(Expr, TExpr, S0, S1), !.

petta_to_he([reduce, Expr], TExpr, S0, S1) :-
    petta_to_he_eval_like(Expr, TExpr, S0, S1), !.

petta_to_he([length, [collapse, Expr]],
            [let, TupleVar, [collapse, TExpr], ['size-atom', TupleVar]], S0, S3) :-
    petta_to_he(Expr, TExpr, S0, S1),
    fresh_name(tuple, S1, S3, TupleVar), !.

petta_to_he([length, Expr], [length, TExpr], S0, S1) :-
    petta_to_he(Expr, TExpr, S0, S1), !.

petta_to_he([test, Actual, Expected],
            [test, TActual, TExpected], S0, S2) :-
    petta_to_he(Actual, TActual, S0, S1),
    petta_to_he(Expected, TExpected, S1, S2), !.

petta_to_he([msort, _], _, _, _) :-
    !,
    fail.

petta_to_he([cut], _, _, _) :-
    !,
    fail.

petta_to_he([==, Left, Right], TExpr, S0, S1) :-
    petta_finite_exists_match_source(Left, Right, SpaceExpr, Pattern, Body), !,
    petta_finite_exists_match_empty_check(SpaceExpr, Pattern, Body, TExpr, S0, S1).

petta_to_he([once, Expr], TExpr, S0, S1) :-
    petta_singleton_visible_witness_surface(Expr, TExpr, S0, S1), !.

petta_to_he([once, Expr],
            [let, TupleVar, [collapse, TExpr],
             [case, TupleVar,
              [['()', 'Empty'],
               [NonemptyVar,
                [let, [HeadVar, TailVar],
                 ['decons-atom', NonemptyVar],
                 HeadVar]]]]], S0, S5) :-
    petta_to_he(Expr, TExpr, S0, S1),
    fresh_name(tuple, S1, S2, TupleVar),
    fresh_name(nonempty, S2, S3, NonemptyVar),
    fresh_name(head, S3, S4, HeadVar),
    fresh_name(tail, S4, S5, TailVar), !.

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

source_variable_atom(Term) :-
    atom(Term),
    sub_atom(Term, 0, 1, _, '$').

petta_to_he_eval_like(Expr, [unquote, TExpr], S0, S1) :-
    source_variable_atom(Expr),
    petta_to_he(Expr, TExpr, S0, S1), !.
petta_to_he_eval_like(Expr, [unquote, [quote, TExpr]], S0, S1) :-
    petta_to_he(Expr, TExpr, S0, S1).

petta_empty_tuple_surface('()').
petta_empty_tuple_surface([]).

petta_finite_exists_match_source(Left, Right, SpaceExpr, Pattern, Body) :-
    petta_empty_tuple_surface(Left),
    petta_finite_exists_match_collapse_surface(Right, SpaceExpr, Pattern, Body), !.
petta_finite_exists_match_source(Left, Right, SpaceExpr, Pattern, Body) :-
    petta_empty_tuple_surface(Right),
    petta_finite_exists_match_collapse_surface(Left, SpaceExpr, Pattern, Body).

petta_finite_exists_match_collapse_surface([collapse, [once, MatchExpr]],
                                           SpaceExpr, Pattern, Body) :-
    nonvar(MatchExpr),
    MatchExpr = [match, SpaceExpr, Pattern, Body].

petta_finite_exists_match_empty_check(SpaceExpr, Pattern, Body,
                                      [==, '()', [collapse, TOnce]], S0, S1) :-
    petta_to_he([once, [match, SpaceExpr, Pattern, Body]], TOnce, S0, S1).

/* ---------------- Explicit singleton-visible-witness surface ---------------- */

/*
  This is the proof-friendly explicit singleton-witness contract corresponding
  to the dedicated portable HE surface used by the executable translator.

  Positive example:
    (once (= $x 42))
  lowers to:
    (singleton-visible-witness (unify $x 42 True Empty))

  Negative example:
    order-sensitive first-witness selection such as
      (if (once (myf $M)) $M)
  remains outside this explicit relational fragment.  The relational core
  mirrors the dedicated portable surface itself rather than the executable
  translator's broader source-program-global witness detector.
*/
petta_singleton_visible_witness_surface(Expr,
                                        ['singleton-visible-witness', TExpr],
                                        S0, S1) :-
    petta_singleton_visible_witness_source_expr(Expr),
    petta_normalize_singleton_visible_witness_term(Expr, NormExpr),
    petta_to_he(NormExpr, TExpr, S0, S1).

petta_singleton_visible_witness_source_expr(Expr) :-
    petta_singleton_visible_witness_source_expr(Expr, []).

petta_singleton_visible_witness_source_expr(Expr, _) :-
    petta_source_truth_atom(Expr),
    !.
petta_singleton_visible_witness_source_expr(Expr, Seen) :-
    petta_singleton_visible_witness_deterministic_term(Expr, Seen),
    !.
petta_singleton_visible_witness_source_expr([once, Inner], Seen) :-
    petta_singleton_visible_witness_source_expr(Inner, Seen),
    !.
petta_singleton_visible_witness_source_expr([and, Left, Right], Seen) :-
    petta_singleton_visible_witness_source_expr(Left, Seen),
    petta_singleton_visible_witness_source_expr(Right, Seen),
    !.

petta_normalize_singleton_visible_witness_term([quote, Expr], [quote, Expr]) :-
    !.
petta_normalize_singleton_visible_witness_term([once, Inner], [once, NormInner]) :-
    !,
    petta_normalize_singleton_visible_witness_term(Inner, NormInner).
petta_normalize_singleton_visible_witness_term([and, Left, Right],
                                               [and, NormLeft, NormRight]) :-
    !,
    petta_normalize_singleton_visible_witness_term(Left, NormLeft),
    petta_normalize_singleton_visible_witness_term(Right, NormRight).
petta_normalize_singleton_visible_witness_term(['=', Left, Right],
                                               [unify, NormLeft, NormRight, 'True', 'Empty']) :-
    petta_singleton_visible_witness_binding_equality_surface(Left, Right),
    !,
    petta_normalize_singleton_visible_witness_term(Left, NormLeft),
    petta_normalize_singleton_visible_witness_term(Right, NormRight).
petta_normalize_singleton_visible_witness_term([Head|Args], [Head|NormArgs]) :-
    !,
    maplist(petta_normalize_singleton_visible_witness_term, Args, NormArgs).
petta_normalize_singleton_visible_witness_term(Term, Term).

petta_singleton_visible_witness_binding_equality_surface(Left, Right) :-
    source_variable_atom(Left),
    \+ petta_term_mentions_atom(Right, Left),
    petta_singleton_visible_witness_deterministic_term(Right, []),
    !.
petta_singleton_visible_witness_binding_equality_surface(Left, Right) :-
    source_variable_atom(Right),
    \+ petta_term_mentions_atom(Left, Right),
    petta_singleton_visible_witness_deterministic_term(Left, []).

petta_singleton_visible_witness_deterministic_term(Term, _) :-
    atomic(Term),
    !.
petta_singleton_visible_witness_deterministic_term(Term, _) :-
    source_variable_atom(Term),
    !.
petta_singleton_visible_witness_deterministic_term([once, Inner], Seen) :-
    petta_singleton_visible_witness_source_expr(Inner, Seen),
    !.
petta_singleton_visible_witness_deterministic_term(['=', Left, Right], Seen) :-
    petta_singleton_visible_witness_deterministic_term(Left, Seen),
    petta_singleton_visible_witness_deterministic_term(Right, Seen),
    !.
petta_singleton_visible_witness_deterministic_term([if, Cond, Then, Else], Seen) :-
    petta_singleton_visible_witness_source_expr(Cond, Seen),
    petta_singleton_visible_witness_deterministic_term(Then, Seen),
    petta_singleton_visible_witness_deterministic_term(Else, Seen),
    !.
petta_singleton_visible_witness_deterministic_term([and, Left, Right], Seen) :-
    petta_singleton_visible_witness_source_expr(Left, Seen),
    petta_singleton_visible_witness_source_expr(Right, Seen),
    !.
petta_singleton_visible_witness_deterministic_term([Head|Args], Seen) :-
    atom(Head),
    \+ petta_singleton_visible_witness_explicit_nondet_head(Head),
    maplist(petta_singleton_visible_witness_deterministic_term_with(Seen), Args),
    !.

petta_singleton_visible_witness_deterministic_term_with(Seen, Term) :-
    petta_singleton_visible_witness_deterministic_term(Term, Seen).

petta_source_truth_atom(true).
petta_source_truth_atom('True').

petta_singleton_visible_witness_explicit_nondet_head(match).
petta_singleton_visible_witness_explicit_nondet_head(superpose).
petta_singleton_visible_witness_explicit_nondet_head(hyperpose).
petta_singleton_visible_witness_explicit_nondet_head(collapse).
petta_singleton_visible_witness_explicit_nondet_head(once).
petta_singleton_visible_witness_explicit_nondet_head(select).
petta_singleton_visible_witness_explicit_nondet_head(member).
petta_singleton_visible_witness_explicit_nondet_head('get-atoms').
petta_singleton_visible_witness_explicit_nondet_head('mork:match').
petta_singleton_visible_witness_explicit_nondet_head('mork:get-atoms').
petta_singleton_visible_witness_explicit_nondet_head(metta).
petta_singleton_visible_witness_explicit_nondet_head(evalc).

petta_term_mentions_atom(Term, Atom) :-
    atomic(Term),
    !,
    Term == Atom.
petta_term_mentions_atom(Term, Atom) :-
    compound(Term),
    compound_name_arguments(Term, _Name, Args),
    member(Subterm, Args),
    petta_term_mentions_atom(Subterm, Atom).

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

/* ---------------- Explicit append-suffix head-pattern extension ---------------- */

/*
  This is the proof-friendly explicit extension corresponding to the narrow
  append-suffix function-head lowering used by the executable translator.

  Positive example:
    a recovered-tail head-pattern family like
      (h (myfunc (10) $B) $C) -> ($B $C)
    can be represented as repeated decons-atom/unify steps, finishing with the
    explicit helper surface (__tr-raw-apply1 $B $C).

  Negative example:
    this does NOT claim to handle equality-form inversion such as h_unify-style
    rules.  That boundary remains explicit.
*/
petta_append_suffix_head_extension(PrefixElems, Actual, TailVar, ApplyArg, HE, S0, S1) :-
    petta_to_he_list(PrefixElems, TPrefixElems, S0, S2),
    petta_to_he(ApplyArg, TApplyArg, S2, S3),
    build_append_suffix_head_extension(TPrefixElems, Actual, TailVar, TApplyArg, HE, S3, S1).

build_append_suffix_head_extension([], Actual, TailVar, ApplyArg,
                                   [let, TailVar, Actual, ['__tr-raw-apply1', TailVar, ApplyArg]],
                                   S, S).
build_append_suffix_head_extension([PrefixElem|Rest], Actual, TailVar, ApplyArg,
                                   [chain, ['decons-atom', Actual], PairVar,
                                    [let, HeadVar, ['first-from-pair', PairVar],
                                     [let, TailExpr, ['second-from-pair', PairVar],
                                      [unify, HeadVar, PrefixElem, Inner, 'Empty']]]],
                                   S0, S5) :-
    fresh_name(head_pair, S0, S1, PairVar),
    fresh_name(head_elem, S1, S2, HeadVar),
    fresh_name(head_tail, S2, S3, TailExpr),
    build_append_suffix_head_extension(Rest, TailExpr, TailVar, ApplyArg, Inner, S3, S5).

/* ---------------- Explicit append-suffix let-pattern extension ---------------- */

/*
  This is the proof-friendly explicit extension corresponding to the structural
  let-pattern function-call inversion lowering used by the executable
  translator.

  Positive example:
    a structural family like
      (let (f $Head $Tail) (1 2 3 4) ($Head $Tail))
    can be represented as repeated decons-atom/unify steps, finishing with the
    already-rawified body surface (__tr-raw-apply1 $Head $Tail).

  Negative example:
    this does NOT claim to handle arithmetic witness families such as
      (let (g $X $Y 35) (42 2 3) ($X $Y 40))
    because those depend on external solver behavior rather than structural
    prefix recovery.
*/
petta_append_suffix_let_extension(PrefixElems, Observed, TailVar, RawBody, HE, S0, S1) :-
    petta_to_he_list(PrefixElems, TPrefixElems, S0, S2),
    petta_to_he(RawBody, TRawBody, S2, S3),
    build_append_suffix_let_extension(TPrefixElems, Observed, TailVar, TRawBody, HE, S3, S1).

build_append_suffix_let_extension([], Observed, TailVar, TRawBody,
                                  [let, TailVar, Observed, TRawBody],
                                  S, S).
build_append_suffix_let_extension([PrefixElem|Rest], Observed, TailVar, TRawBody,
                                  [chain, ['decons-atom', Observed], PairVar,
                                   [let, HeadVar, ['first-from-pair', PairVar],
                                    [let, TailExpr, ['second-from-pair', PairVar],
                                     [unify, HeadVar, PrefixElem, Inner, 'Empty']]]],
                                  S0, S5) :-
    fresh_name(head_pair, S0, S1, PairVar),
    fresh_name(head_elem, S1, S2, HeadVar),
    fresh_name(head_tail, S2, S3, TailExpr),
    build_append_suffix_let_extension(Rest, TailExpr, TailVar, TRawBody, Inner, S3, S5).

/* ---------------- Roundtrip witnesses ---------------- */

roundtrip_he(HE, PeTTa, HE2, S0, S2) :-
    he_to_petta(HE, PeTTa, S0, S1),
    petta_to_he(PeTTa, HE2, S1, S2).

roundtrip_petta(PeTTa, HE, PeTTa2, S0, S2) :-
    petta_to_he(PeTTa, HE, S0, S1),
    he_to_petta(HE, PeTTa2, S1, S2).
