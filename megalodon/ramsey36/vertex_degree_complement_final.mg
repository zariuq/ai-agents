Section Egal.

Theorem nat_p_3 : nat_p 3.
exact nat_ordsucc 2 nat_2.
Qed.

Theorem nat_p_5 : nat_p 5.
exact nat_ordsucc 4 (nat_ordsucc 3 nat_p_3).
Qed.

Theorem nat_p_8 : nat_p 8.
exact nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5 nat_p_5)).
Qed.

Theorem three_plus_five_eq_eight : 3 + 5 = 8.
prove ordsucc 2 + ordsucc (ordsucc (ordsucc 2)) = ordsucc (ordsucc (ordsucc (ordsucc (ordsucc (ordsucc 2))))).
rewrite add_nat_SR 3 4 (nat_ordsucc 3 nat_p_3).
prove ordsucc (3 + 4) = 8.
rewrite add_nat_SR 3 3 nat_p_3.
prove ordsucc (ordsucc (3 + 3)) = 8.
rewrite add_nat_SR 3 2 nat_2.
prove ordsucc (ordsucc (ordsucc (3 + 2))) = 8.
rewrite add_nat_SR 3 1 nat_1.
prove ordsucc (ordsucc (ordsucc (ordsucc (3 + 1)))) = 8.
rewrite add_nat_SR 3 0 nat_0.
prove ordsucc (ordsucc (ordsucc (ordsucc (ordsucc (3 + 0))))) = 8.
rewrite add_nat_0R 3.
prove ordsucc (ordsucc (ordsucc (ordsucc (ordsucc 3)))) = 8.
reflexivity.
Qed.

Axiom disjoint_union_card_3_5 : forall N M:set,
  equip 3 N ->
  equip 5 M ->
  (N :/\: M = Empty) ->
  equip 8 (N :\/: M).

Theorem vertex_degree_from_complement : forall v :e 9,
  forall N M: set,
    N c= 9 -> M c= 9 ->
    (forall x :e 9, x <> v -> (x :e N \/ x :e M)) ->
    (forall x :e N, x <> v) ->
    (forall x :e M, x <> v) ->
    (N :/\: M = Empty) ->
    equip 3 N -> equip 5 M ->
    equip 8 (N :\/: M).
let v. assume Hv: v :e 9.
let N M.
assume HN9: N c= 9.
assume HM9: M c= 9.
assume Hpartition: forall x :e 9, x <> v -> (x :e N \/ x :e M).
assume HNv: forall x :e N, x <> v.
assume HMv: forall x :e M, x <> v.
assume Hdisjoint: N :/\: M = Empty.
assume HN3: equip 3 N.
assume HM5: equip 5 M.
prove equip 8 (N :\/: M).
exact disjoint_union_card_3_5 N M HN3 HM5 Hdisjoint.
Qed.

End Egal.
