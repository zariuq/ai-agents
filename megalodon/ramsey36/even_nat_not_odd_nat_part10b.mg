Theorem even_nat_not_odd_nat : forall x0, even_nat x0 -> not (odd_nat x0).
let x0: set.
assume H0: even_nat x0.
exact (H0 (not (odd_nat x0)) (fun H1: x0 :e omega =>(fun H2: (exists x1, and (x1 :e omega) (x0 = mul_nat 2 x1)) =>(H2 (not (odd_nat x0)) (fun x1: set => (fun H3: (fun x2 : set => and (x2 :e omega) (x0 = mul_nat 2 x2)) x1 =>(H3 (not (odd_nat x0)) (fun H4: x1 :e omega =>(fun H5: x0 = mul_nat 2 x1 =>(fun H6: odd_nat x0 =>(H6 False (fun H7: x0 :e omega =>(fun H8: (forall x2, x2 :e omega -> x0 = mul_nat 2 x2 -> (forall x3 : prop, x3)) =>(H8 x1 H4 H5)))))))))))))).
Qed.
