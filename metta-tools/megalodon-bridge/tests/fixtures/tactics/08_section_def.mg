Section S.

Definition tru : prop := forall p:prop, p -> p.

Theorem tru_ok : tru.
exact (fun p => fun x => x).
Qed.

End S.
