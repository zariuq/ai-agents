Theorem even_nat_not_odd_nat_direct : forall n, even_nat n -> ~odd_nat n.
let n.
assume Heven: even_nat n.
prove ~odd_nat n.
prove ~(n :e omega /\ forall m :e omega, n <> 2 * m).
assume Hodd: n :e omega /\ forall m :e omega, n <> 2 * m.
prove False.
prove n :e omega /\ exists m :e omega, n = 2 * m.
exact Heven.
Qed.
