Theorem equip_adjoin_sing : forall n:set, forall X y:set,
  nat_p n ->
  equip n X ->
  y /:e X ->
  equip (ordsucc n) (X :\/: {y}).
let n X y.
assume Hn: nat_p n.
assume HX: equip n X.
assume Hy: y /:e X.
prove equip (ordsucc n) (X :\/: {y}).
apply HX.
let f. assume Hf: bij n X f.
apply bijE n X f Hf.
assume Hf1: forall i :e n, f i :e X.
assume Hf2: forall i j :e n, f i = f j -> i = j.
assume Hf3: forall x :e X, exists i :e n, f i = x.
apply equip_sym.
prove exists g:set -> set, bij (ordsucc n) (X :\/: {y}) g.
set g : set -> set := fun i : set => if i :e n then f i else y.
witness g.
apply bijI.
- prove forall i :e ordsucc n, g i :e X :\/: {y}.
  let i. assume Hi. apply ordsuccE n i Hi.
  + assume H1: i :e n.
    apply binunionI1.
    prove g i :e X.
    rewrite If_i_1 (i :e n) (f i) y H1.
    exact Hf1 i H1.
  + assume H1: i = n.
    apply binunionI2.
    rewrite H1.
    prove g n :e {y}.
    rewrite If_i_0 (n :e n) (f n) y (In_irref n).
    exact SingI y.
- prove forall i j :e ordsucc n, g i = g j -> i = j.
  let i. assume Hi. let j. assume Hj.
  apply ordsuccE n i Hi.
  + assume H1: i :e n.
    rewrite If_i_1 (i :e n) (f i) y H1.
    apply ordsuccE n j Hj.
    * assume H2: j :e n.
      rewrite If_i_1 (j :e n) (f j) y H2.
      exact Hf2 i H1 j H2.
    * assume H2: j = n.
      rewrite H2.
      rewrite If_i_0 (n :e n) (f n) y (In_irref n).
      assume H3: f i = y.
      prove False.
      apply Hy.
      prove y :e X.
      rewrite <- H3.
      exact Hf1 i H1.
  + assume H1: i = n.
    rewrite H1.
    rewrite If_i_0 (n :e n) (f n) y (In_irref n).
    apply ordsuccE n j Hj.
    * assume H2: j :e n.
      rewrite If_i_1 (j :e n) (f j) y H2.
      assume H3: y = f j.
      prove False.
      apply Hy.
      prove y :e X.
      rewrite H3.
      exact Hf1 j H2.
    * assume H2: j = n.
      rewrite H2.
      assume _.
      prove n = n.
      reflexivity.
- prove forall x :e X :\/: {y}, exists i :e ordsucc n, g i = x.
  let x. assume Hx.
  apply binunionE X {y} x Hx.
  + assume H1: x :e X.
    apply Hf3 x H1.
    let i. assume H. apply H.
    assume Hi: i :e n.
    assume H2: f i = x.
    witness i.
    apply andI.
    * apply ordsuccI1. exact Hi.
    * prove g i = x.
      rewrite If_i_1 (i :e n) (f i) y Hi.
      exact H2.
  + assume H1: x :e {y}.
    witness n.
    apply andI.
    * apply ordsuccI2.
    * prove g n = x.
      rewrite SingE y x H1.
      exact If_i_0 (n :e n) (f n) y (In_irref n).
Qed.

Theorem disjoint_binunion_sing : forall A B y:set,
  (forall x, x :e A -> x /:e B) ->
  y /:e A ->
  (forall x, x :e A -> x /:e (B :\/: {y})).
let A B y.
assume Hdisj: forall x, x :e A -> x /:e B.
assume Hy: y /:e A.
let x. assume Hx: x :e A.
prove x /:e (B :\/: {y}).
assume H1: x :e (B :\/: {y}).
apply binunionE B {y} x H1.
- assume H2: x :e B.
  exact Hdisj x Hx H2.
- assume H2: x :e {y}.
  claim Hxy: x = y.
    exact SingE y x H2.
  apply Hy.
  prove y :e A.
  rewrite <- Hxy.
  exact Hx.
Qed.

Theorem disjoint_union_card : forall m n:set, forall A B:set,
  nat_p m ->
  nat_p n ->
  equip m A ->
  equip n B ->
  (forall x, x :e A -> x /:e B) ->
  equip (m + n) (A :\/: B).
let m.
assume Hm: nat_p m.
let n.
apply nat_ind.
- assume HA HB.
  assume _: nat_p 0.
  assume H3: equip 0 B.
  assume Hdisj: forall x, x :e A -> x /:e B.
  prove equip (m + 0) (A :\/: B).
  claim L1: B = Empty.
    exact equip_0_Empty B H3.
  rewrite L1.
  rewrite binunion_idr A.
  rewrite add_nat_0R m.
  assume HA: equip m A.
  exact HA.
- let n.
  assume Hn: nat_p n.
  assume IH: forall A B, equip m A -> equip n B -> (forall x, x :e A -> x /:e B) -> equip (m + n) (A :\/: B).
  let A B.
  assume HA: equip m A.
  assume HB: equip (ordsucc n) B.
  assume Hdisj: forall x, x :e A -> x /:e B.
  prove equip (m + ordsucc n) (A :\/: B).
  rewrite add_nat_SR m n Hn.
  prove equip (ordsucc (m + n)) (A :\/: B).
  apply equip_sym (ordsucc n) B HB.
  let f. assume Hf: bij (ordsucc n) B f.
  apply bijE (ordsucc n) B f Hf.
  assume Hf1: forall i :e ordsucc n, f i :e B.
  assume Hf2: forall i j :e ordsucc n, f i = f j -> i = j.
  assume Hf3: forall x :e B, exists i :e ordsucc n, f i = x.
  set B' : set := {f i | i :e n}.
  claim LB': equip n B'.
    apply equip_sym.
    prove exists g:set -> set, bij n B' g.
    witness f.
    apply bijI.
    + let i. assume Hi: i :e n.
      prove f i :e B'.
      exact ReplI n f i Hi.
    + let i j. assume Hi: i :e n. assume Hj: j :e n.
      exact Hf2 i (ordsuccI1 n i Hi) j (ordsuccI1 n j Hj).
    + let y. assume Hy: y :e B'.
      apply ReplE_impred n f y Hy.
      let i. assume Hi: i :e n. assume H1: y = f i.
      witness i. apply andI.
      * exact Hi.
      * exact H1.
  claim Lfn: f n /:e B'.
    assume H1: f n :e B'.
    apply ReplE_impred n f (f n) H1.
    let i. assume Hi: i :e n. assume H2: f n = f i.
    claim L2: n = i.
      exact Hf2 n (ordsuccI2 n) i (ordsuccI1 n i Hi) H2.
    apply In_no_succ n.
    prove n :e ordsucc n.
    rewrite L2 at 1.
    exact ordsuccI1 n i Hi.
  claim LB: B = B' :\/: {f n}.
    apply set_ext.
    + let x. assume Hx: x :e B.
      apply Hf3 x Hx.
      let i. assume H. apply H.
      assume Hi: i :e ordsucc n.
      assume H1: f i = x.
      apply ordsuccE n i Hi.
      * assume H2: i :e n.
        apply binunionI1.
        prove x :e B'.
        rewrite <- H1.
        exact ReplI n f i H2.
      * assume H2: i = n.
        apply binunionI2.
        rewrite <- H1.
        rewrite H2.
        exact SingI (f n).
    + let x. assume Hx: x :e B' :\/: {f n}.
      apply binunionE B' {f n} x Hx.
      * assume H1: x :e B'.
        apply ReplE_impred n f x H1.
        let i. assume Hi: i :e n. assume H2: x = f i.
        rewrite H2.
        exact Hf1 i (ordsuccI1 n i Hi).
      * assume H1: x :e {f n}.
        rewrite SingE (f n) x H1.
        exact Hf1 n (ordsuccI2 n).
  rewrite LB.
  claim Ldisj': forall x, x :e A -> x /:e B'.
    let x. assume Hx: x :e A.
    assume H1: x :e B'.
    apply ReplE_impred n f x H1.
    let i. assume Hi: i :e n. assume H2: x = f i.
    apply Hdisj x Hx.
    prove x :e B.
    rewrite H2.
    exact Hf1 i (ordsuccI1 n i Hi).
  claim Lfn_notA: f n /:e A.
    assume H1: f n :e A.
    apply Hdisj (f n) H1.
    exact Hf1 n (ordsuccI2 n).
  claim LAB': equip (m + n) (A :\/: B').
    exact IH A B' HA LB' Ldisj'.
  prove equip (ordsucc (m + n)) (A :\/: (B' :\/: {f n})).
  rewrite binunion_asso A B' {f n}.
  prove equip (ordsucc (m + n)) ((A :\/: B') :\/: {f n}).
  exact equip_adjoin_sing (m + n) (A :\/: B') (f n) (add_nat_p m Hm n Hn) LAB'
    (disjoint_binunion_sing A B' (f n) Ldisj' Lfn_notA (f n) Lfn_notA).
Qed.
