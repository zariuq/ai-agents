Theorem even_nat_not_odd_nat_vampire : forall n:set, even_nat n -> odd_nat n -> False.
let n.
assume Heven: even_nat n.
assume Hodd: odd_nat n.
claim Ln_omega: n :e omega.
  apply Heven.
  assume H1: n :e omega.
  assume H2: exists m :e omega, n = 2 * m.
  exact H1.
claim Hexists: exists m :e omega, n = 2 * m.
  apply Heven.
  assume H1: n :e omega.
  assume H2: exists m :e omega, n = 2 * m.
  exact H2.
apply Hexists.
let m.
assume Hm_conj: m :e omega /\ n = 2 * m.
claim Hm_omega: m :e omega.
  apply Hm_conj.
  assume H1: m :e omega.
  assume H2: n = 2 * m.
  exact H1.
claim Heq: n = 2 * m.
  apply Hm_conj.
  assume H1: m :e omega.
  assume H2: n = 2 * m.
  exact H2.
claim Hforall: forall k :e omega, n <> 2 * k.
  apply Hodd.
  assume H1: n :e omega.
  assume H2: forall k :e omega, n <> 2 * k.
  exact H2.
claim Hneq: n <> 2 * m.
  exact Hforall m Hm_omega.
exact Hneq Heq.
Qed.
