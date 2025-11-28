Theorem Sing_nonempty : forall x:set, exists y:set, y :e {x}.
let x.
witness x.
exact SingI x.
Qed.

Theorem UPair_or : forall x y z:set, z :e {x,y} -> z = x \/ z = y.
let x y z.
assume Hz: z :e {x,y}.
prove z = x \/ z = y.
exact UPairE z x y Hz.
Qed.

Theorem Sing_eq : forall x y:set, y :e {x} -> y = x.
let x y.
assume Hy: y :e {x}.
exact SingE x y Hy.
Qed.

Theorem binunion_comm : forall X Y:set, X :\/: Y = Y :\/: X.
let X Y.
apply set_ext.
- let x. assume Hx: x :e X :\/: Y.
  apply binunionE X Y x Hx.
  + assume HxX: x :e X.
    exact binunionI2 Y X x HxX.
  + assume HxY: x :e Y.
    exact binunionI1 Y X x HxY.
- let x. assume Hx: x :e Y :\/: X.
  apply binunionE Y X x Hx.
  + assume HxY: x :e Y.
    exact binunionI2 X Y x HxY.
  + assume HxX: x :e X.
    exact binunionI1 X Y x HxX.
Qed.

Theorem binintersect_comm : forall X Y:set, X :/\: Y = Y :/\: X.
let X Y.
apply set_ext.
- let x. assume Hx: x :e X :/\: Y.
  claim HxX: x :e X.
    exact andEL (x :e X) (x :e Y) (binintersectE X Y x Hx).
  claim HxY: x :e Y.
    exact andER (x :e X) (x :e Y) (binintersectE X Y x Hx).
  exact binintersectI Y X x HxY HxX.
- let x. assume Hx: x :e Y :/\: X.
  claim HxY: x :e Y.
    exact andEL (x :e Y) (x :e X) (binintersectE Y X x Hx).
  claim HxX: x :e X.
    exact andER (x :e Y) (x :e X) (binintersectE Y X x Hx).
  exact binintersectI X Y x HxX HxY.
Qed.

Theorem zfmisc_compiles : True.
exact TrueI.
Qed.
