Theorem intros_test : forall A B:prop, A -> B -> A /\ B.
intros A B HA HB.
apply andI.
exact HA.
exact HB.
Qed.
