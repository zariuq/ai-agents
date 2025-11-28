(* Tactic Test 01: Basic Apply *)
Definition True : prop := forall p:prop, p -> p.
Theorem id : forall A:prop, A -> A.
exact (fun A x => x).
Qed.
