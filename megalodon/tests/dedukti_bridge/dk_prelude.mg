Theorem eqI : forall x:set, x = x.
exact (fun (x:set) (Q:set->set->prop) (H: Q x x) => H).
Qed.

Theorem comm : forall x y : set, x = y -> forall P:set->prop, P y -> P x.
exact (fun (x:set) (y:set) (H: x = y) (P:set->prop) (py:P y) =>
  H (fun (_:set) (v:set) => P v) py).
Qed.

Theorem comm2 : forall x y : set, x = y -> forall Q:set->set->prop, Q x y -> Q y x.
exact (fun (x:set) (y:set) (H: x = y) (Q:set->set->prop) (q: Q x y) => H Q q).
Qed.

Theorem comm_sym : forall x y : set, x = y -> y = x.
exact (fun (x:set) (y:set) (H: x = y) =>
    H (fun (z:set) (_:set) => z = x) (eqI x)).
Qed.

Theorem comml : forall x y : set, (x = y -> False) -> (y = x -> False).
exact (fun (x:set) (y:set) (H1: x = y -> False) (H2: y = x) =>
  H1 (comm_sym y x H2)).
Qed.

Definition dk_ec : prop := False.
Definition dk_cons : prop -> prop -> prop := fun p:prop => fun c:prop => (p -> False) -> c.
Definition dk_cl : prop -> prop := fun c:prop => c.
Definition dk_acl : prop -> prop := fun c:prop => c.

Definition Prf_prop_clause : prop -> prop := fun c:prop => c.
Definition Prf_clause : prop -> prop := fun c:prop => c.
Definition Prf_av_clause : prop -> prop := fun c:prop => c.

Definition av_if := fun sp:prop => fun c:prop => (~sp -> False) -> c.

Section DKBind.
Variable A:SType.
Definition bind : (A->prop) -> prop := fun f => forall x:A, f x.
End DKBind.

Definition bind_poly : (set->prop) -> prop := fun f => forall x:set, f x.
Definition dk_prop_clause : prop -> prop := fun c:prop => c.
Definition dk_clause : prop -> prop := fun c:prop => c.
Definition dk_av_clause : prop -> prop := fun c:prop => c.
Definition dk_cPrf : prop -> prop := fun c:prop => not (not c).
