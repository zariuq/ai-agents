Theorem even_nat_not_odd_nat : forall n, even_nat n -> ~odd_nat n.
let n.
assume Heven: even_nat n.
assume Hodd: odd_nat n.
prove False.
apply Heven.
assume Hn_omega: n :e omega.
assume Hexists: exists m :e omega, n = 2 * m.
apply Hexists.
let m.
assume Hm_omega: m :e omega.
assume Heq: n = 2 * m.
apply Hodd.
assume Hn_omega2: n :e omega.
assume Hforall: forall k :e omega, n <> 2 * k.
exact Hforall m Hm_omega Heq.
Qed.
