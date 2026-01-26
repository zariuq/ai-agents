Definition is_random_variable : set -> set -> set -> set -> (set -> set) -> prop :=
  fun Omega F X G f => is_measurable Omega F X G f.

Definition distribution : set -> set -> (set -> set) -> (set -> set) -> set -> set :=
  fun Omega F mu f A => mu (preimage Omega f A).

Definition expectation_simple : set -> set -> (set -> set) -> (set -> set) -> set :=
  fun Omega F mu f => lebesgue_integral_simple Omega F mu f.

Definition variance_simple : set -> set -> (set -> set) -> (set -> set) -> set :=
  fun Omega F mu f =>
    let m := expectation_simple Omega F mu f in
    expectation_simple Omega F mu (fun x => (f x + - m) * (f x + - m)).
