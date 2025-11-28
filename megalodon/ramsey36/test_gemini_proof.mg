Theorem even_nat_not_odd_nat : forall n:set, even_nat n -> odd_nat n -> False.
let n.
assume Heven: even_nat n.
assume Hodd: odd_nat n.

claim H_forall: forall m :e omega, n <> 2 * m.
  exact andER (n :e omega) (forall m :e omega, n <> 2 * m) Hodd.

claim H_exists: exists m :e omega, n = 2 * m.
  exact andER (n :e omega) (exists m :e omega, n = 2 * m) Heven.

apply H_exists.
let m.
assume Hm_omega: m :e omega.
assume Heq: n = 2 * m.

claim Hneq: n <> 2 * m.
  exact H_forall m Hm_omega.

exact Hneq Heq.
Qed.
