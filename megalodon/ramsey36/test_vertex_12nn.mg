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

Theorem vertex_degree_at_most_5: forall R : set -> set -> prop,
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
  forall v :e 18, forall n1 n2 n3 n4 n5 n6 :e 18,
    n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> n1 <> n6 ->
    n2 <> n3 -> n2 <> n4 -> n2 <> n5 -> n2 <> n6 ->
    n3 <> n4 -> n3 <> n5 -> n3 <> n6 ->
    n4 <> n5 -> n4 <> n6 ->
    n5 <> n6 ->
    R v n1 -> R v n2 -> R v n3 -> R v n4 -> R v n5 -> R v n6 ->
    False.
let R.
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
let n1. assume Hn1: n1 :e 18.
let n2. assume Hn2: n2 :e 18.
let n3. assume Hn3: n3 :e 18.
let n4. assume Hn4: n4 :e 18.
let n5. assume Hn5: n5 :e 18.
let n6. assume Hn6: n6 :e 18.
assume Hn12: n1 <> n2.
assume Hn13: n1 <> n3.
assume Hn14: n1 <> n4.
assume Hn15: n1 <> n5.
assume Hn16: n1 <> n6.
assume Hn23: n2 <> n3.
assume Hn24: n2 <> n4.
assume Hn25: n2 <> n5.
assume Hn26: n2 <> n6.
assume Hn34: n3 <> n4.
assume Hn35: n3 <> n5.
assume Hn36: n3 <> n6.
assume Hn45: n4 <> n5.
assume Hn46: n4 <> n6.
assume Hn56: n5 <> n6.
assume Hvn1: R v n1.
assume Hvn2: R v n2.
assume Hvn3: R v n3.
assume Hvn4: R v n4.
assume Hvn5: R v n5.
assume Hvn6: R v n6.
prove False.
exact vertex_6_neighbors_contradiction R 18 v n1 n2 n3 n4 n5 n6
  (fun x Hx y Hy HRxy => Hsym x y HRxy)
  Htf Hno6
  Hv Hn1 Hn2 Hn3 Hn4 Hn5 Hn6
  Hn12 Hn13 Hn14 Hn15 Hn16
  Hn23 Hn24 Hn25 Hn26
  Hn34 Hn35 Hn36
  Hn45 Hn46
  Hn56
  Hvn1 Hvn2 Hvn3 Hvn4 Hvn5 Hvn6.
Qed.
