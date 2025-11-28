Parameter A : prop.

Definition conj_left : prop -> prop -> prop := fun X Y => X.
Infix /\ 700 left := conj_left.

Theorem proj_left : A /\ A -> A.
exact (fun h => h).
Qed.
