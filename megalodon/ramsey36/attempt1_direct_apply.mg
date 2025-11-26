Theorem even_nat_not_odd_nat : forall n:set, even_nat n -> odd_nat n -> False.
let n.
assume Heven: even_nat n.
assume Hodd: odd_nat n.
apply Heven.
assume Hn1: n :e omega.
assume Hex: exists m :e omega, n = 2 * m.
apply Hex.
let m.
assume Hm: m :e omega /\ n = 2 * m.
apply Hodd.
assume Hn2: n :e omega.
assume Hall: forall k :e omega, n <> 2 * k.
apply Hm.
assume Hm_omega: m :e omega.
assume Heq: n = 2 * m.
exact Hall m Hm_omega Heq.
Qed.
