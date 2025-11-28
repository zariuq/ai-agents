Axiom vertex_6_neighbors_contradiction:
  forall R : set -> set -> prop,
  forall V : set,
  forall v n1 n2 n3 n4 n5 n6 : set,
  (forall x, x :e V -> forall y, y :e V -> R x y -> R y x) ->
  (forall x, x :e V -> forall y, y :e V -> forall z, z :e V ->
     R x y -> R y z -> R x z -> False) ->
  (forall a, a :e V -> forall b, b :e V -> forall c, c :e V -> forall d, d :e V -> forall e, e :e V -> forall f, f :e V ->
    a <> b -> a <> c -> a <> d -> a <> e -> a <> f ->
    b <> c -> b <> d -> b <> e -> b <> f ->
    c <> d -> c <> e -> c <> f ->
    d <> e -> d <> f ->
    e <> f ->
    (R a b \/ R a c \/ R a d \/ R a e \/ R a f \/
     R b c \/ R b d \/ R b e \/ R b f \/
     R c d \/ R c e \/ R c f \/
     R d e \/ R d f \/
     R e f)) ->
  v :e V -> n1 :e V -> n2 :e V -> n3 :e V -> n4 :e V -> n5 :e V -> n6 :e V ->
  n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> n1 <> n6 ->
  n2 <> n3 -> n2 <> n4 -> n2 <> n5 -> n2 <> n6 ->
  n3 <> n4 -> n3 <> n5 -> n3 <> n6 ->
  n4 <> n5 -> n4 <> n6 ->
  n5 <> n6 ->
  R v n1 -> R v n2 -> R v n3 -> R v n4 -> R v n5 -> R v n6 ->
  False.

Axiom nat_p_17 : nat_p 17.
Axiom nat_p_18 : nat_p 18.
Axiom nat_18_def : 18 = ordsucc 17.

Theorem remove_one_from_18 : forall v :e 18,
  equip 17 (18 :\: {v}).
Admitted.

Theorem partition_complement : forall V A B: set,
  equip 17 V ->
  (forall x :e V, x :e A \/ x :e B) ->
  (forall x, x :e A -> x /:e B) ->
  (forall x, x :e B -> x /:e A) ->
  ~(exists T, T c= B /\ equip 12 T) ->
  exists S, S c= A /\ equip 6 S.
Admitted.

Theorem vertex_has_12_nonneighbors : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  (forall x, x :e 18 -> forall y, y :e 18 -> forall z, z :e 18 ->
     R x y -> R y z -> R x z -> False) ->
  (forall a, a :e 18 -> forall b, b :e 18 -> forall c, c :e 18 -> forall d, d :e 18 -> forall e, e :e 18 -> forall f, f :e 18 ->
    a <> b -> a <> c -> a <> d -> a <> e -> a <> f ->
    b <> c -> b <> d -> b <> e -> b <> f ->
    c <> d -> c <> e -> c <> f ->
    d <> e -> d <> f ->
    e <> f ->
    (R a b \/ R a c \/ R a d \/ R a e \/ R a f \/
     R b c \/ R b d \/ R b e \/ R b f \/
     R c d \/ R c e \/ R c f \/
     R d e \/ R d f \/
     R e f)) ->
  forall v :e 18, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: forall x, x :e 18 -> forall y, y :e 18 -> forall z, z :e 18 ->
     R x y -> R y z -> R x z -> False.
assume Hno6: forall a, a :e 18 -> forall b, b :e 18 -> forall c, c :e 18 -> forall d, d :e 18 -> forall e, e :e 18 -> forall f, f :e 18 ->
    a <> b -> a <> c -> a <> d -> a <> e -> a <> f ->
    b <> c -> b <> d -> b <> e -> b <> f ->
    c <> d -> c <> e -> c <> f ->
    d <> e -> d <> f ->
    e <> f ->
    (R a b \/ R a c \/ R a d \/ R a e \/ R a f \/
     R b c \/ R b d \/ R b e \/ R b f \/
     R c d \/ R c e \/ R c f \/
     R d e \/ R d f \/
     R e f).
let v. assume Hv: v :e 18.
prove exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T.
Admitted.
