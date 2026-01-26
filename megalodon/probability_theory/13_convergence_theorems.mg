Definition null_set : set -> (set -> set) -> set -> prop :=
  fun Omega mu A => A c= Omega /\ mu A = 0.

Definition holds_ae : set -> (set -> set) -> (set -> prop) -> prop :=
  fun Omega mu P =>
    exists N, null_set Omega mu N /\
      (forall x :e Omega, x /:e N -> P x).

Definition converges_ae : set -> (set -> set) -> (set -> set -> set) -> (set -> set) -> prop :=
  fun Omega mu F f =>
    holds_ae Omega mu (fun x => converges_to (fun n => F n x) (f x)).

Definition converges_in_probability : set -> (set -> set) -> (set -> set -> set) -> (set -> set) -> prop :=
  fun Omega mu F f =>
    forall k :e omega,
      converges_to
        (fun n => mu {x :e Omega | abs_SNo (F n x + - f x) < eps_ k})
        0.

Definition L1_distance : set -> set -> (set -> set) -> (set -> set) -> (set -> set) -> set :=
  fun Omega F mu f g =>
    lebesgue_integral_simple Omega F mu (fun x => abs_SNo (f x + - g x)).

Definition converges_L1 : set -> set -> (set -> set) -> (set -> set -> set) -> (set -> set) -> prop :=
  fun Omega F mu Fseq f =>
    converges_to (fun n => L1_distance Omega F mu (Fseq n) f) 0.
