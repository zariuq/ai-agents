Theorem Subq_binunion_left : forall X Y:set, X c= X :\/: Y.
let X Y.
let x. assume Hx: x :e X.
exact binunionI1 X Y x Hx.
Qed.

Theorem Subq_binunion_right : forall X Y:set, Y c= X :\/: Y.
let X Y.
let x. assume Hx: x :e Y.
exact binunionI2 X Y x Hx.
Qed.

Theorem binintersect_Subq_left : forall X Y:set, X :/\: Y c= X.
let X Y.
let x. assume Hx: x :e X :/\: Y.
exact andEL (x :e X) (x :e Y) (binintersectE X Y x Hx).
Qed.

Theorem binintersect_Subq_right : forall X Y:set, X :/\: Y c= Y.
let X Y.
let x. assume Hx: x :e X :/\: Y.
exact andER (x :e X) (x :e Y) (binintersectE X Y x Hx).
Qed.

Theorem setminus_Empty : forall X:set, X :\: Empty = X.
let X.
apply set_ext.
- let x. assume Hx: x :e X :\: Empty.
  exact andEL (x :e X) (x /:e Empty) (setminusE X Empty x Hx).
- let x. assume Hx: x :e X.
  apply setminusI X Empty x.
  + exact Hx.
  + assume HxE: x :e Empty.
    apply EmptyAx.
    witness x.
    exact HxE.
Qed.

Theorem subset_compiles : True.
exact TrueI.
Qed.
