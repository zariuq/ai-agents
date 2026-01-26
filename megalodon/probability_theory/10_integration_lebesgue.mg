Definition is_nonneg_fun : set -> (set -> set) -> prop :=
  fun Omega f => forall x :e Omega, 0 <= f x.

Definition is_upper_bound_set : set -> set -> prop :=
  fun S s => forall x :e S, x <= s.

Definition is_least_upper_bound_set : set -> set -> prop :=
  fun S s =>
    is_upper_bound_set S s
    /\ (forall t :e real, is_upper_bound_set S t -> s <= t).

Definition simple_integral_set : set -> set -> (set -> set) -> (set -> set) -> set :=
  fun Omega F mu f =>
    {s :e real | exists v : set -> set, exists A : set -> set, exists n :e omega,
      simple_function_repr Omega F f v A n /\
      s = simple_integral_rep Omega mu v A n}.

Definition lebesgue_integral_simple : set -> set -> (set -> set) -> (set -> set) -> set :=
  fun Omega F mu f =>
    Eps_i (fun s => s :e real /\ is_least_upper_bound_set (simple_integral_set Omega F mu f) s).
