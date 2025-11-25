Theorem Schemat0 : forall P:set -> prop, (forall a:set, P a) -> exists a:set, P a.
let P.
assume Hforall: forall a:set, P a.
prove exists a:set, P a.
set a := Empty.
witness a.
exact Hforall a.
Qed.

Theorem Schemat3 : forall S:set -> set -> prop,
  (exists a:set, forall b:set, S a b) -> forall b:set, exists a:set, S a b.
let S.
assume Hex: exists a:set, forall b:set, S a b.
prove forall b:set, exists a:set, S a b.
apply Hex.
let a. assume Ha: forall b:set, S a b.
let b.
witness a.
exact Ha b.
Qed.

Theorem Schemat8 : forall P Q:set -> prop,
  (forall a:set, P a -> Q a) -> (forall a:set, P a) -> forall a:set, Q a.
let P Q.
assume Himpl: forall a:set, P a -> Q a.
assume Hforall: forall a:set, P a.
let a.
exact Himpl a (Hforall a).
Qed.

Theorem Schemat9 : forall P Q:set -> prop,
  (forall a:set, P a <-> Q a) ->
  ((forall a:set, P a) <-> (forall a:set, Q a)).
let P Q.
assume Hiff: forall a:set, P a <-> Q a.
apply iffI.
- assume HforallP: forall a:set, P a.
  let a.
  exact iffEL (P a) (Q a) (Hiff a) (HforallP a).
- assume HforallQ: forall a:set, Q a.
  let a.
  exact iffER (P a) (Q a) (Hiff a) (HforallQ a).
Qed.

Theorem Schemat17 : forall P:set -> prop, forall T:prop,
  (forall a:set, P a -> T) -> (forall a:set, P a) -> T.
let P T.
assume Himpl: forall a:set, P a -> T.
assume Hforall: forall a:set, P a.
set a := Empty.
exact Himpl a (Hforall a).
Qed.

Theorem Schemat18a : forall P Q:set -> prop,
  ((exists a:set, P a) \/ (forall b:set, Q b)) ->
  exists a:set, forall b:set, P a \/ Q b.
let P Q.
assume Hor: (exists a:set, P a) \/ (forall b:set, Q b).
apply Hor.
- assume Hex: exists a:set, P a.
  apply Hex.
  let a. assume HPa: P a.
  witness a.
  let b.
  apply orIL.
  exact HPa.
- assume Hforall: forall b:set, Q b.
  set a := Empty.
  witness a.
  let b.
  apply orIR.
  exact Hforall b.
Qed.

Theorem Schemat18b : forall P Q:set -> prop,
  (exists a:set, forall b:set, P a \/ Q b) ->
  (exists a:set, P a) \/ (forall b:set, Q b).
let P Q.
assume Hex: exists a:set, forall b:set, P a \/ Q b.
apply Hex.
let a. assume Ha: forall b:set, P a \/ Q b.
apply xm (P a).
- assume HPa: P a.
  apply orIL.
  witness a.
  exact HPa.
- assume HnPa: ~P a.
  apply orIR.
  let b.
  apply Ha b.
  + assume HPa2: P a.
    apply FalseE.
    exact HnPa HPa2.
  + assume HQb: Q b.
    exact HQb.
Qed.

Theorem Schemat20b : forall P Q:set -> prop,
  (forall b:set, exists a:set, P a \/ Q b) ->
  exists a:set, forall b:set, P a \/ Q b.
let P Q.
assume Hforall: forall b:set, exists a:set, P a \/ Q b.
apply xm (exists a:set, P a).
- assume Hex: exists a:set, P a.
  apply Hex.
  let a. assume HPa: P a.
  witness a.
  let b.
  apply orIL.
  exact HPa.
- assume Hnex: ~(exists a:set, P a).
  set a := Empty.
  witness a.
  let b.
  apply Hforall b.
  let a'. assume Hor: P a' \/ Q b.
  apply Hor.
  + assume HPa': P a'.
    apply FalseE.
    apply Hnex.
    witness a'.
    exact HPa'.
  + assume HQb: Q b.
    apply orIR.
    exact HQb.
Qed.

Theorem Schemat22a : forall P Q:set -> prop,
  (exists a:set, P a) /\ (forall b:set, Q b) ->
  forall b:set, exists a:set, P a /\ Q b.
admit.
Qed.

Theorem Schemat22b : forall P Q:set -> prop,
  (forall b:set, exists a:set, P a /\ Q b) ->
  (exists a:set, P a) /\ (forall b:set, Q b).
admit.
Qed.

Theorem Schemat23b : forall P Q:set -> prop,
  (forall b:set, exists a:set, P a /\ Q b) ->
  exists a:set, forall b:set, P a /\ Q b.
admit.
Qed.

Theorem Schemat28 : forall S:set -> set -> prop,
  (forall a b:set, S a b) -> exists b:set, forall a:set, S a b.
admit.
Qed.

Theorem Schemat30 : forall S:set -> set -> prop,
  (exists a:set, forall b:set, S a b) -> exists a:set, S a a.
admit.
Qed.

Theorem Schemat31 : forall S:set -> set -> prop,
  (forall a:set, S a a) -> forall a:set, exists b:set, S b a.
admit.
Qed.

Theorem Schemat33 : forall S:set -> set -> prop,
  (forall a:set, S a a) -> forall a:set, exists b:set, S a b.
admit.
Qed.

Theorem Schemat36 : forall S:set -> set -> prop,
  (forall b:set, exists a:set, S a b) -> exists a:set, exists b:set, S a b.
admit.
Qed.
