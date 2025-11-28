Definition let_simple : set := let x := Empty in x.
Definition let_typed : set := let x : set := Empty in x.
Definition let_nested : set := let x := Empty in let y := x in y.
