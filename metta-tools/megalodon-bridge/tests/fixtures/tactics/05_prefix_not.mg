Parameter P : prop.

Definition my_not : prop -> prop := fun X => X.
Prefix ~ 900 := my_not.

Theorem not_id : ~ P -> P -> P.
exact (fun _ p => p).
Qed.
