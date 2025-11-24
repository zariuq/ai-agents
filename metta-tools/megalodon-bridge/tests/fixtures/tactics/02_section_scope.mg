Section LocalScope.
Variable A : prop.

Definition id : A -> A := fun x => x.

Theorem section_goal : A -> A.
exact (fun x => id x).
Qed.

End LocalScope.
