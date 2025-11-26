Theorem even_nat_not_odd_nat : forall n, even_nat n -> ~odd_nat n.
let n.
assume Heven: even_nat n.
assume Hodd: odd_nat n.
prove False.
apply andEL (n :e omega) (exists m :e omega, n = 2 * m) Heven.
assume Hn_omega: n :e omega.
apply andER (n :e omega) (exists m :e omega, n = 2 * m) Heven.
assume Hexists: exists m :e omega, n = 2 * m.
apply Hexists.
let m.
assume Hm: m :e omega /\ n = 2 * m.
apply andEL (m :e omega) (n = 2 * m) Hm.
assume Hm_omega: m :e omega.
apply andER (m :e omega) (n = 2 * m) Hm.
assume Heq: n = 2 * m.
apply andER (n :e omega) (forall m :e omega, n <> 2 * m) Hodd.
assume Hforall: forall m :e omega, n <> 2 * m.
exact Hforall m Hm_omega Heq.
Qed.
