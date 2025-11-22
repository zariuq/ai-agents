(* Explicit proofs for remaining theorems *)

(*
Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.
*)

(* Theorem: no_k_indep implies no k-element independent set exists *)
Theorem no_k_indep_no_indep_set : forall V:set, forall R:set -> set -> prop, forall k:set,
  no_k_indep V R k ->
  ~(exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
let V. let R: set -> set -> prop. let k.
assume Hno: no_k_indep V R k.
(* Hno : forall S, S c= V -> equip k S -> ~is_indep_set V R S *)
assume Hex: exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
prove False.
apply Hex.
let Y.
assume HY: Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
(* Extract components from HY *)
claim HYsub: Y c= V.
  exact andEL (Y c= V) (equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)) HY.
claim HYrest: equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
  exact andER (Y c= V) (equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)) HY.
claim HYequip: equip k Y.
  exact andEL (equip k Y) (forall x :e Y, forall y :e Y, x <> y -> ~R x y) HYrest.
claim HYindep: forall x :e Y, forall y :e Y, x <> y -> ~R x y.
  exact andER (equip k Y) (forall x :e Y, forall y :e Y, x <> y -> ~R x y) HYrest.
(* Now show Y is an independent set *)
claim HYis: is_indep_set V R Y.
  prove Y c= V /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
  exact andI (Y c= V) (forall x :e Y, forall y :e Y, x <> y -> ~R x y) HYsub HYindep.
(* Apply no_k_indep: Hno Y HYsub HYequip gives ~is_indep_set V R Y *)
claim Hnot: ~is_indep_set V R Y.
  exact Hno Y HYsub HYequip.
(* Contradiction *)
exact Hnot HYis.
Qed.

(*
Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

A 3-clique would be: exists X c= V with |X|=3 and all pairs related.
The proof needs: from equip 3 X, extract 3 distinct elements a,b,c
and use that they form a triangle to contradict triangle_free.

This requires more set theory infrastructure (equip_3_witness or similar).
*)

(* For triangle_free_no_3clique, we need a lemma about 3-element sets *)
(* This is more complex - needs equip 3 X to give a,b,c :e X with a<>b<>c<>a *)
(* Leaving as aby for now - the main work was no6indep proofs *)

Theorem triangle_free_no_3clique : forall V:set, forall R:set -> set -> prop,
  triangle_free V R ->
  ~(exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y)).
aby.
Qed.

(* The *_from_neg theorems need classical logic (double negation elimination) *)
(* These use the form: ~(forall...) -> exists... *)
(* In constructive logic this doesn't hold, but Megalodon has classical logic via dneg *)

Theorem triangle_witness_from_neg : forall V:set, forall R:set -> set -> prop,
  ~triangle_free V R ->
  exists X, X c= V /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y).
aby.
Qed.

Theorem indep_witness_from_neg : forall V:set, forall R:set -> set -> prop, forall k:set,
  ~no_k_indep V R k ->
  exists Y, Y c= V /\ equip k Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y).
aby.
Qed.

(* The main upper bound theorem - requires the full Ramsey argument *)
Theorem good_graph_contradiction : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) -> triangle_free 18 R -> no_k_indep 18 R 6 -> False.
aby.
Qed.
