Theorem rewrite_test : forall x y:set, x = y -> y = x.
let x y.
assume H: x = y.
rewrite H.
reflexivity.
Qed.

Theorem rewrite_rev : forall x y:set, x = y -> x = y.
let x y.
assume H: x = y.
rewrite <- H.
rewrite <- H at 1.
reflexivity.
Qed.
