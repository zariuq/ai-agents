Definition and : prop -> prop -> prop := fun A B => forall p:prop, A -> B -> p -> p.
Infix /\ 780 left := and.

Definition or : prop -> prop -> prop := fun A B => forall p:prop, (A -> p) -> (B -> p) -> p.
Infix \/ 770 left := or.

Definition my_not : prop -> prop := fun X => X.
Prefix ~ 900 := my_not.
