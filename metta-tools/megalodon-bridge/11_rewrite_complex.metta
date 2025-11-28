(Theorem rewrite_test (forall ((x set) (y set)) (-> ((x =) y) ((y =) x))) (((let x) y) (assume ((((H :) x) =) y)) (rewrite H) reflexivity))
(Theorem rewrite_rev (forall ((x set) (y set)) (-> ((x =) y) ((x =) y))) (((let x) y) (assume ((((H :) x) =) y)) (rewrite H (dir <-)) (rewrite H (dir <-) (at 1)) reflexivity))
