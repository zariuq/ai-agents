Section Test.
Variable A : set.
Definition idA : set -> set := fun x => x.
Theorem self_eq : idA A = idA A.
reflexivity.
Qed.
End Test.
