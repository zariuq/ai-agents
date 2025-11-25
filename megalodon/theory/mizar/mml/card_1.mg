Definition cardinal : set -> prop :=
  fun X => exists B:set, X = B /\ (forall A:set, equip A B -> B c= A).

Theorem eq_symm_set : forall x y:set, x = y -> y = x.
let x. let y.
assume Hxy: x = y.
prove y = x.
let Q:set -> set -> prop.
assume HQ: Q y x.
exact Hxy (fun u v => Q v u) HQ.
Qed.

Theorem equip_sym_card : forall X Y:set, equip X Y -> equip Y X.
let X. let Y.
assume Hex: equip X Y.
exact equip_sym X Y Hex.
Qed.

Theorem cardinal_empty : cardinal Empty.
prove exists B:set, Empty = B /\ (forall A:set, equip A B -> B c= A).
witness Empty.
apply andI (Empty = Empty) (forall A:set, equip A Empty -> Empty c= A).
- reflexivity.
- let A.
  assume _ : equip A Empty.
  exact Subq_Empty A.
Qed.

Theorem cardinal_existence : exists X:set, cardinal X.
witness Empty.
exact cardinal_empty.
Qed.

Theorem cardinal_min : forall X A:set, cardinal X -> equip A X -> X c= A.
let X. let A.
assume Hcard: cardinal X.
assume Heq: equip A X.
apply Hcard.
let B. assume HB: X = B /\ (forall A:set, equip A B -> B c= A).
claim HX: X = B.
  exact andEL (X = B) (forall A:set, equip A B -> B c= A) HB.
claim HBprop: forall A:set, equip A B -> B c= A.
  exact andER (X = B) (forall A:set, equip A B -> B c= A) HB.
claim HeqAB: equip A B.
  rewrite <- HX.
  exact Heq.
claim HBsub: B c= A.
  exact HBprop A HeqAB.
rewrite HX.
exact HBsub.
Qed.

Theorem cardinal_intro : forall X:set,
  (forall A:set, equip A X -> X c= A) -> cardinal X.
let X.
assume Hmin: forall A:set, equip A X -> X c= A.
prove exists B:set, X = B /\ (forall A:set, equip A B -> B c= A).
witness X.
apply andI (X = X) (forall A:set, equip A X -> X c= A).
- reflexivity.
- exact Hmin.
Qed.

Theorem cardinal_eq_of_equip : forall M N:set,
  cardinal M -> cardinal N -> equip M N -> M = N.
let M. let N.
assume HM: cardinal M.
assume HN: cardinal N.
assume Heq: equip M N.
claim Heq_sym: equip N M.
  exact equip_sym_card M N Heq.
claim Hsub1: M c= N.
  exact cardinal_min M N HM Heq_sym.
claim Hsub2: N c= M.
  exact cardinal_min N M HN Heq.
exact set_ext M N Hsub1 Hsub2.
Qed.

Theorem equip_empty_eq : forall A:set, equip A Empty -> A = Empty.
let A.
assume Heq: equip A Empty.
apply Heq.
let f:set -> set.
assume Hbij: bij A Empty f.
prove A = Empty.
apply Empty_Subq_eq A.
prove A c= Empty.
let x. assume HxA: x :e A.
claim Hmap: forall u :e A, f u :e Empty.
  apply and3E (forall u :e A, f u :e Empty) (forall u v :e A, f u = f v -> u = v) (forall w :e Empty, exists u :e A, f u = w) Hbij.
  assume H1: forall u :e A, f u :e Empty.
  assume H2: forall u v :e A, f u = f v -> u = v.
  assume H3: forall w :e Empty, exists u :e A, f u = w.
  exact H1.
claim Hfx: f x :e Empty.
  exact Hmap x HxA.
apply FalseE.
apply EmptyAx.
witness (f x).
exact Hfx.
Qed.

Theorem equip_nonempty : forall X Y:set, forall x:set,
  x :e X -> equip X Y -> exists y:set, y :e Y.
let X. let Y. let x.
assume Hx: x :e X.
assume Heq: equip X Y.
apply Heq.
let f:set -> set.
assume Hbij: bij X Y f.
claim Hmap: forall u :e X, f u :e Y.
  apply and3E (forall u :e X, f u :e Y) (forall u v :e X, f u = f v -> u = v) (forall w :e Y, exists u :e X, f u = w) Hbij.
  assume H1: forall u :e X, f u :e Y.
  assume H2: forall u v :e X, f u = f v -> u = v.
  assume H3: forall w :e Y, exists u :e X, f u = w.
  exact H1.
prove exists y:set, y :e Y.
witness (f x).
exact Hmap x Hx.
Qed.

Theorem equip_nonempty_ne : forall X Y:set, forall x:set,
  x :e X -> equip X Y -> Y <> Empty.
let X. let Y. let x.
assume Hx: x :e X.
assume Heq: equip X Y.
claim Hex: exists y:set, y :e Y.
  exact equip_nonempty X Y x Hx Heq.
assume HY: Y = Empty.
claim HeqE: equip X Empty.
  rewrite <- HY.
  exact Heq.
claim HexE: exists y:set, y :e Empty.
  exact equip_nonempty X Empty x Hx HeqE.
apply EmptyAx.
exact HexE.
Qed.

Theorem equip_ordsucc_has_elem : forall X n:set, equip X (ordsucc n) -> exists x:set, x :e X.
let X. let n.
assume Heq: equip X (ordsucc n).
apply equip_nonempty (ordsucc n) X n.
- exact ordsuccI2 n.
- exact equip_sym_card X (ordsucc n) Heq.
Qed.

Theorem equip_singleton_shape : forall X a:set, equip X {a} -> exists x:set, X = {x}.
let X. let a.
assume Heq: equip X {a}.
apply Heq.
let f:set -> set.
assume Hbij: bij X {a} f.
claim Hmap: forall u :e X, f u :e {a}.
  apply and3E (forall u :e X, f u :e {a}) (forall u v :e X, f u = f v -> u = v) (forall w :e {a}, exists u :e X, f u = w) Hbij.
  assume H1: forall u :e X, f u :e {a}.
  assume H2: forall u v :e X, f u = f v -> u = v.
  assume H3: forall w :e {a}, exists u :e X, f u = w.
  exact H1.
claim Hex: exists u :e X, f u = a.
  apply and3E (forall u :e X, f u :e {a}) (forall u v :e X, f u = f v -> u = v) (forall w :e {a}, exists u :e X, f u = w) Hbij.
  assume H1: forall u :e X, f u :e {a}.
  assume H2: forall u v :e X, f u = f v -> u = v.
  assume H3: forall w :e {a}, exists u :e X, f u = w.
  claim H3a: exists u :e X, f u = a.
    exact H3 a (SingI a).
  exact H3a.
apply Hex.
let x0. assume Hx0: x0 :e X /\ f x0 = a.
claim Hx0_in: x0 :e X.
  exact andEL (x0 :e X) (f x0 = a) Hx0.
claim Hx0_val: f x0 = a.
  exact andER (x0 :e X) (f x0 = a) Hx0.
prove exists x:set, X = {x}.
witness x0.
apply set_ext X {x0}.
- prove X c= {x0}.
  let y. assume Hy: y :e X.
  claim Hy_img: f y :e {a}.
    exact Hmap y Hy.
  claim Hy_eq: f y = a.
    exact SingE a (f y) Hy_img.
  claim Hy_eqx: y = x0.
    apply and3E (forall u :e X, f u :e {a}) (forall u v :e X, f u = f v -> u = v) (forall w :e {a}, exists u :e X, f u = w) Hbij.
    assume H1: forall u :e X, f u :e {a}.
    assume H2: forall u v :e X, f u = f v -> u = v.
    assume H3: forall w :e {a}, exists u :e X, f u = w.
    exact H2 y Hy x0 Hx0_in (eq_i_tra (f y) a (f x0) Hy_eq (eq_symm_set (f x0) a Hx0_val)).
  rewrite Hy_eqx.
  exact SingI x0.
- prove {x0} c= X.
  let y. assume Hy: y :e {x0}.
  rewrite (SingE x0 y Hy).
  exact Hx0_in.
Qed.
