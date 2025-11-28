Theorem even_nat_not_odd_nat : forall n:set, even_nat n -> odd_nat n -> False.
let n.
assume Heven: even_nat n.
assume Hodd: odd_nat n.
apply Heven.
assume Hn_in_omega: n :e omega.
assume Hexists: exists m :e omega, n = 2 * m.
apply Hexists.
let m0.
assume Hm0_conj: m0 :e omega /\ n = 2 * m0.
claim Hm0_omega: m0 :e omega.
  exact andEL (m0 :e omega) (n = 2 * m0) Hm0_conj.
claim Heq: n = 2 * m0.
  exact andER (m0 :e omega) (n = 2 * m0) Hm0_conj.
apply Hodd.
assume Hn_in_omega2: n :e omega.
assume Hforall: forall k :e omega, n <> 2 * k.
claim Hneq: n <> 2 * m0.
  exact Hforall m0 Hm0_omega.
exact Hneq Heq.
Qed.
