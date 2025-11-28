Theorem induction_test : forall (n:e nat), (n =) n.
let ? := ? in ?.
assume (((((Hn :) n) :) e) nat).
apply (nat_ind (fun n => (n =) n)).
(((- prove) 0) =) 0.
reflexivity.
(- let) n.
assume (((((Hn :) n) :) e) nat).
assume ((((IH :) n) =) n).
((((prove S) n) =) S) n.
reflexivity.
Qed.

Theorem cases_test : forall (n:e nat), (((((n =) 0) \/) n) <>) 0.
let ? := ? in ?.
assume (((((Hn :) n) :) e) nat).
apply (xm ((n =) 0)).
(((((- assume) H) :) n) =) 0.
apply orIL.
exact H.
(((((- assume) H) :) n) <>) 0.
apply orIR.
exact H.
Qed.

