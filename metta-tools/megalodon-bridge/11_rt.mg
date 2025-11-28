Theorem rewrite_test : forall (x:set) (y:set), (x =) y -> (y =) x.
(let ? := ? in ?) y.
assume ((((H :) x) =) y).
rewrite H.
reflexivity.
Qed.

Theorem rewrite_rev : forall (x:set) (y:set), (x =) y -> (x =) y.
(let ? := ? in ?) y.
assume ((((H :) x) =) y).
rewrite <- H.
rewrite <- H at 1.
reflexivity.
Qed.

