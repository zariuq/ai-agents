Theorem claim_test : forall A:prop, A -> A.
let A.
assume H: A.
claim L1: A.
{
  exact H.
}
exact L1.
Qed.
