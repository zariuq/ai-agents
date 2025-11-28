Theorem vertex_6_neighbors_contradiction:
  forall R : set -> set -> prop,
  forall V : set,
  forall v n1 n2 n3 n4 n5 n6 : set,
  (forall x, x :e V -> forall y, y :e V -> R x y -> R y x) ->
  (forall x, x :e V -> forall y, y :e V -> forall z, z :e V -> R x y -> R y z -> R x z -> False) ->
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
let R V v n1 n2 n3 n4 n5 n6.
assume Hsym : forall x, x :e V -> forall y, y :e V -> R x y -> R y x.
assume Htf : forall x, x :e V -> forall y, y :e V -> forall z, z :e V -> R x y -> R y z -> R x z -> False.
assume Hno6 : forall a, a :e V -> forall b, b :e V -> forall c, c :e V -> forall d, d :e V -> forall e, e :e V -> forall f, f :e V ->
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
assume Hv : v :e V.
assume Hn1 : n1 :e V.
assume Hn2 : n2 :e V.
assume Hn3 : n3 :e V.
assume Hn4 : n4 :e V.
assume Hn5 : n5 :e V.
assume Hn6 : n6 :e V.
assume Hd12 : n1 <> n2.
assume Hd13 : n1 <> n3.
assume Hd14 : n1 <> n4.
assume Hd15 : n1 <> n5.
assume Hd16 : n1 <> n6.
assume Hd23 : n2 <> n3.
assume Hd24 : n2 <> n4.
assume Hd25 : n2 <> n5.
assume Hd26 : n2 <> n6.
assume Hd34 : n3 <> n4.
assume Hd35 : n3 <> n5.
assume Hd36 : n3 <> n6.
assume Hd45 : n4 <> n5.
assume Hd46 : n4 <> n6.
assume Hd56 : n5 <> n6.
assume Hvn1 : R v n1.
assume Hvn2 : R v n2.
assume Hvn3 : R v n3.
assume Hvn4 : R v n4.
assume Hvn5 : R v n5.
assume Hvn6 : R v n6.
claim Ledge : R n1 n2 \/ R n1 n3 \/ R n1 n4 \/ R n1 n5 \/ R n1 n6 \/ R n2 n3 \/ R n2 n4 \/ R n2 n5 \/ R n2 n6 \/ R n3 n4 \/ R n3 n5 \/ R n3 n6 \/ R n4 n5 \/ R n4 n6 \/ R n5 n6.
{ exact (Hno6 n1 Hn1 n2 Hn2 n3 Hn3 n4 Hn4 n5 Hn5 n6 Hn6 Hd12 Hd13 Hd14 Hd15 Hd16 Hd23 Hd24 Hd25 Hd26 Hd34 Hd35 Hd36 Hd45 Hd46 Hd56). }
claim C12 : R n1 n2 -> False.
{ assume H12. exact (Htf v Hv n1 Hn1 n2 Hn2 Hvn1 H12 Hvn2). }
claim C13 : R n1 n3 -> False.
{ assume H13. exact (Htf v Hv n1 Hn1 n3 Hn3 Hvn1 H13 Hvn3). }
claim C14 : R n1 n4 -> False.
{ assume H14. exact (Htf v Hv n1 Hn1 n4 Hn4 Hvn1 H14 Hvn4). }
claim C15 : R n1 n5 -> False.
{ assume H15. exact (Htf v Hv n1 Hn1 n5 Hn5 Hvn1 H15 Hvn5). }
claim C16 : R n1 n6 -> False.
{ assume H16. exact (Htf v Hv n1 Hn1 n6 Hn6 Hvn1 H16 Hvn6). }
claim C23 : R n2 n3 -> False.
{ assume H23. exact (Htf v Hv n2 Hn2 n3 Hn3 Hvn2 H23 Hvn3). }
claim C24 : R n2 n4 -> False.
{ assume H24. exact (Htf v Hv n2 Hn2 n4 Hn4 Hvn2 H24 Hvn4). }
claim C25 : R n2 n5 -> False.
{ assume H25. exact (Htf v Hv n2 Hn2 n5 Hn5 Hvn2 H25 Hvn5). }
claim C26 : R n2 n6 -> False.
{ assume H26. exact (Htf v Hv n2 Hn2 n6 Hn6 Hvn2 H26 Hvn6). }
claim C34 : R n3 n4 -> False.
{ assume H34. exact (Htf v Hv n3 Hn3 n4 Hn4 Hvn3 H34 Hvn4). }
claim C35 : R n3 n5 -> False.
{ assume H35. exact (Htf v Hv n3 Hn3 n5 Hn5 Hvn3 H35 Hvn5). }
claim C36 : R n3 n6 -> False.
{ assume H36. exact (Htf v Hv n3 Hn3 n6 Hn6 Hvn3 H36 Hvn6). }
claim C45 : R n4 n5 -> False.
{ assume H45. exact (Htf v Hv n4 Hn4 n5 Hn5 Hvn4 H45 Hvn5). }
claim C46 : R n4 n6 -> False.
{ assume H46. exact (Htf v Hv n4 Hn4 n6 Hn6 Hvn4 H46 Hvn6). }
claim C56 : R n5 n6 -> False.
{ assume H56. exact (Htf v Hv n5 Hn5 n6 Hn6 Hvn5 H56 Hvn6). }
exact (
  Ledge False
    (fun H14 =>
      H14 False
        (fun H13 =>
          H13 False
            (fun H12 =>
              H12 False
                (fun H11 =>
                  H11 False
                    (fun H10 =>
                      H10 False
                        (fun H9 =>
                          H9 False
                            (fun H8 =>
                              H8 False
                                (fun H7 =>
                                  H7 False
                                    (fun H6 =>
                                      H6 False
                                        (fun H5 =>
                                          H5 False
                                            (fun H4 =>
                                              H4 False
                                                (fun H3 =>
                                                  H3 False
                                                    (fun H2 =>
                                                      H2 False C12 C13)
                                                    C14)
                                                C15)
                                            C16)
                                        C23)
                                    C24)
                                C25)
                            C26)
                        C34)
                    C35)
                C36)
            C45)
        C46)
    C56).
Qed.
