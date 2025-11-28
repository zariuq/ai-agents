Definition tru : prop := forall p:prop, p -> p.

Theorem if_then_else : tru.
exact (fun p => fun hp => if tru then hp else hp).
Qed.

Theorem let_expr : tru.
exact (fun p => fun hp => let x := hp in x).
Qed.

Theorem match_bool : tru.
exact (fun p => fun hp => match tru with | tru => hp).
Qed.
