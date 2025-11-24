Theorem equip_setsum_add : forall n m: set,
  nat_p n -> nat_p m ->
  equip (n + m) (n :+: m).
let n m.
assume Hn: nat_p n.
assume Hm: nat_p m.
prove equip (n + m) (n :+: m).
apply nat_ind (fun m => equip (n + m) (n :+: m)).
- prove equip (n + 0) (n :+: 0).
  claim H1: n + 0 = n. exact add_nat_0R n.
  claim H2: n :+: 0 = Inj0 n. exact Inj0_setsum_0L n.
  prove equip (n + 0) (n :+: 0).
  claim Heq1: equip n n. exact equip_ref n.
  Admitted.
- let m'. assume Hm': nat_p m'.
  assume IH: equip (n + m') (n :+: m').
  prove equip (n + ordsucc m') (n :+: ordsucc m').
  Admitted.
- exact Hm.
Qed.
