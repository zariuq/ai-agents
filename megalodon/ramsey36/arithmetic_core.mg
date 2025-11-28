Infix + 360 right := add_nat.

Theorem nat_p_4 : nat_p 4.
exact nat_ordsucc 3 (nat_ordsucc 2 nat_2).
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 (nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8
      (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 nat_p_4)))))))).
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13 nat_p_13))).
Qed.

Theorem add_nat_cancel_L : forall a b c:set,
  nat_p a -> nat_p b -> nat_p c ->
  a + b = a + c ->
  b = c.
Admitted.

Theorem add_nat_cancel_R : forall a b c:set,
  nat_p a -> nat_p b -> nat_p c ->
  b + a = c + a ->
  b = c.
Admitted.

Theorem nat_le_exists_add : forall m n:set,
  nat_p m -> nat_p n ->
  m c= n ->
  exists k:set, nat_p k /\ n = m + k.
Admitted.

Theorem nat_le_from_add : forall m n k:set,
  nat_p m -> nat_p n -> nat_p k ->
  n = m + k ->
  m c= n.
Admitted.

Theorem add_4_13_is_17 : 4 + 13 = 17.
Admitted.

Theorem nat_sum_17_bound : forall d g:set,
  nat_p d ->
  nat_p g ->
  d + g = 17 ->
  g c= 13 ->
  4 c= d.
Admitted.

Theorem infrastructure_compiles : True.
exact TrueI.
Qed.
