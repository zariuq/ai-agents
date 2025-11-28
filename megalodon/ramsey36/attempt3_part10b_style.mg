Theorem even_nat_not_odd_nat : forall n:set, even_nat n -> odd_nat n -> False.
let n.
assume Heven: even_nat n.
assume Hodd: odd_nat n.
exact (Heven False (fun Hn1: n :e omega =>(fun Hex: exists m :e omega, n = 2 * m =>(Hex False (fun m =>(fun Hm_conj: m :e omega /\ n = 2 * m =>(Hm_conj False (fun Hm_omega: m :e omega =>(fun Heq: n = 2 * m =>(Hodd False (fun Hn2: n :e omega =>(fun Hforall: forall k :e omega, n <> 2 * k =>Hforall m Hm_omega Heq))))))))))))))).
Qed.
