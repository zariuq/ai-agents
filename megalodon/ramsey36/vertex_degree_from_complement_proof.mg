% Proof of vertex_degree_from_complement
% Based on Vampire proof structure

Theorem disjoint_from_inter_empty : forall N M:set,
  (N :/\: M = Empty) -> (forall x, x :e N -> x /:e M).
let N M.
assume Hempty: N :/\: M = Empty.
let x. assume HxN: x :e N.
prove x /:e M.
assume HxM: x :e M.
claim Hx_inter: x :e N :/\: M.
  exact binintersectI N M x HxN HxM.
rewrite Hempty in Hx_inter.
exact EmptyE x Hx_inter.
Qed.

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

% Key: Apply disjoint_union_card with 3 and 5
% This requires proving N and M are disjoint

claim Hdisjoint_no_common: forall x, x :e N -> x /:e M.
  exact disjoint_from_inter_empty N M Hdisjoint.

% We need: disjoint_union_card : forall n m A B:set,
%   nat_p n -> nat_p m -> equip n A -> equip m B ->
%   (forall x, x :e A -> x /:e B) ->
%   exists p:set, nat_p p /\ equip p (A :\/: B).

% But we need the specific p=8
% The missing piece: 3 + 5 = 8 and the bijection

Admitted.
