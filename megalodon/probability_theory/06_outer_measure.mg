Definition outer_measure_rest : set -> (set -> set) -> prop :=
  fun Omega mu =>
    (forall A, A c= Omega -> mu A :e real /\ 0 <= mu A)
    /\ (forall f : set -> set,
          (forall n :e omega, f n c= Omega) ->
          mu (bigcup_nat f) <= series_sum (fun n => mu (f n))).

Definition is_outer_measure : set -> (set -> set) -> prop :=
  fun Omega mu =>
    mu Empty = 0
    /\ outer_measure_rest Omega mu.

Definition caratheodory_measurable : set -> (set -> set) -> set -> prop :=
  fun Omega mu A =>
    A c= Omega /\
    (forall E, E c= Omega ->
      mu E = mu (E :/\: A) + mu (E :\: A)).

Definition measurable_set : set -> (set -> set) -> set -> prop :=
  fun Omega mu A => caratheodory_measurable Omega mu A.

Definition measurable_family : set -> (set -> set) -> set :=
  fun Omega mu => {A :e Power Omega | measurable_set Omega mu A}.

Theorem outer_measure_empty :
  forall Omega, forall mu : set -> set, is_outer_measure Omega mu -> mu Empty = 0.
let Omega. let mu : set -> set.
assume H.
exact andEL (mu Empty = 0) (outer_measure_rest Omega mu) H.
Qed.

Theorem outer_measure_value_real :
  forall Omega, forall mu : set -> set, is_outer_measure Omega mu ->
  forall A, A c= Omega -> mu A :e real.
let Omega. let mu : set -> set.
assume H.
claim Hrest: outer_measure_rest Omega mu.
  exact andER (mu Empty = 0) (outer_measure_rest Omega mu) H.
claim Hbounds: forall A, A c= Omega -> mu A :e real /\ 0 <= mu A.
  exact andEL (forall A, A c= Omega -> mu A :e real /\ 0 <= mu A)
              (forall f : set -> set,
                (forall n :e omega, f n c= Omega) ->
                mu (bigcup_nat f) <= series_sum (fun n => mu (f n))) Hrest.
let A.
assume HA: A c= Omega.
exact andEL (mu A :e real) (0 <= mu A) (Hbounds A HA).
Qed.

Theorem outer_measure_nonneg :
  forall Omega, forall mu : set -> set, is_outer_measure Omega mu ->
  forall A, A c= Omega -> 0 <= mu A.
let Omega. let mu : set -> set.
assume H.
claim Hrest: outer_measure_rest Omega mu.
  exact andER (mu Empty = 0) (outer_measure_rest Omega mu) H.
claim Hbounds: forall A, A c= Omega -> mu A :e real /\ 0 <= mu A.
  exact andEL (forall A, A c= Omega -> mu A :e real /\ 0 <= mu A)
              (forall f : set -> set,
                (forall n :e omega, f n c= Omega) ->
                mu (bigcup_nat f) <= series_sum (fun n => mu (f n))) Hrest.
let A.
assume HA: A c= Omega.
exact andER (mu A :e real) (0 <= mu A) (Hbounds A HA).
Qed.

Theorem outer_measure_subadditivity :
  forall Omega, forall mu : set -> set, is_outer_measure Omega mu ->
  forall f : set -> set,
    (forall n :e omega, f n c= Omega) ->
    mu (bigcup_nat f) <= series_sum (fun n => mu (f n)).
let Omega. let mu : set -> set.
assume H.
claim Hrest: outer_measure_rest Omega mu.
  exact andER (mu Empty = 0) (outer_measure_rest Omega mu) H.
claim Hsub: forall f : set -> set,
    (forall n :e omega, f n c= Omega) ->
    mu (bigcup_nat f) <= series_sum (fun n => mu (f n)).
  exact andER (forall A, A c= Omega -> mu A :e real /\ 0 <= mu A)
              (forall f : set -> set,
                (forall n :e omega, f n c= Omega) ->
                mu (bigcup_nat f) <= series_sum (fun n => mu (f n))) Hrest.
let f.
assume Hf.
exact Hsub f Hf.
Qed.

Theorem caratheodory_measurable_subset :
  forall Omega, forall mu : set -> set, forall A, caratheodory_measurable Omega mu A -> A c= Omega.
let Omega. let mu : set -> set. let A.
assume H.
exact andEL (A c= Omega)
            (forall E, E c= Omega -> mu E = mu (E :/\: A) + mu (E :\: A))
            H.
Qed.

Theorem measurable_set_subset :
  forall Omega, forall mu : set -> set, forall A, measurable_set Omega mu A -> A c= Omega.
let Omega. let mu : set -> set. let A.
assume H.
exact caratheodory_measurable_subset Omega mu A H.
Qed.
