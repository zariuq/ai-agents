Theorem even_nat_not_odd_nat : forall n:set, even_nat n -> odd_nat n -> False.
let n.
assume Heven: even_nat n.
assume Hodd: odd_nat n.
claim C1: n :e omega.
  apply Heven.
  assume H1: n :e omega.
  assume H2: exists m :e omega, n = 2 * m.
  exact H1.
claim C2: exists m :e omega, n = 2 * m.
  apply Heven.
  assume H1: n :e omega.
  assume H2: exists m :e omega, n = 2 * m.
  exact H2.
claim C3: forall m :e omega, n <> 2 * m.
  apply Hodd.
  assume H1: n :e omega.
  assume H2: forall m :e omega, n <> 2 * m.
  exact H2.
apply C2.
let m.
assume Hm: m :e omega /\ n = 2 * m.
apply Hm.
assume Hm_omega: m :e omega.
assume Heq: n = 2 * m.
exact C3 m Hm_omega Heq.
Qed.
