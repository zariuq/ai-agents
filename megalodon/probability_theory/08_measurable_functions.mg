Definition preimage : set -> (set -> set) -> set -> set :=
  fun Omega f A => {x :e Omega | f x :e A}.

Theorem preimage_subset :
  forall Omega, forall f : set -> set, forall A,
    preimage Omega f A c= Omega.
let Omega. let f : set -> set. let A.
let x.
assume Hx: x :e preimage Omega f A.
exact SepE1 Omega (fun y => f y :e A) x Hx.
Qed.

Theorem preimage_in_power :
  forall Omega, forall f : set -> set, forall A,
    preimage Omega f A :e Power Omega.
let Omega. let f : set -> set. let A.
apply PowerEq Omega (preimage Omega f A).
assume _ H2.
exact H2 (preimage_subset Omega f A).
Qed.

Theorem preimage_empty :
  forall Omega, forall f : set -> set,
    preimage Omega f Empty = Empty.
let Omega. let f : set -> set.
apply set_ext.
- prove preimage Omega f Empty c= Empty.
  let x.
  assume Hx: x :e preimage Omega f Empty.
  claim Hfx: f x :e Empty.
    exact SepE2 Omega (fun y => f y :e Empty) x Hx.
  prove x :e Empty.
  exact FalseE (EmptyE (f x) Hfx) (x :e Empty).
- exact Subq_Empty (preimage Omega f Empty).
Qed.

Theorem preimage_binunion :
  forall Omega, forall f : set -> set, forall A B,
    preimage Omega f (A :\/: B) = preimage Omega f A :\/: preimage Omega f B.
let Omega. let f : set -> set. let A. let B.
apply set_ext.
- prove preimage Omega f (A :\/: B) c= preimage Omega f A :\/: preimage Omega f B.
  let x.
  assume Hx: x :e preimage Omega f (A :\/: B).
  claim Hfx: f x :e A :\/: B.
    exact SepE2 Omega (fun y => f y :e A :\/: B) x Hx.
  apply orE (f x :e A) (f x :e B) (x :e preimage Omega f A :\/: preimage Omega f B)
    (fun H =>
      binunionI1 (preimage Omega f A) (preimage Omega f B) x
        (SepI Omega (fun y => f y :e A) x (SepE1 Omega (fun y => f y :e A :\/: B) x Hx) H))
    (fun H =>
      binunionI2 (preimage Omega f A) (preimage Omega f B) x
        (SepI Omega (fun y => f y :e B) x (SepE1 Omega (fun y => f y :e A :\/: B) x Hx) H))
    (binunionE A B (f x) Hfx).
- prove preimage Omega f A :\/: preimage Omega f B c= preimage Omega f (A :\/: B).
  let x.
  assume Hx: x :e preimage Omega f A :\/: preimage Omega f B.
  apply orE (x :e preimage Omega f A) (x :e preimage Omega f B) (x :e preimage Omega f (A :\/: B))
    (fun H =>
      SepI Omega (fun y => f y :e A :\/: B) x
        (SepE1 Omega (fun y => f y :e A) x H)
        (binunionI1 A B (f x) (SepE2 Omega (fun y => f y :e A) x H)))
    (fun H =>
      SepI Omega (fun y => f y :e A :\/: B) x
        (SepE1 Omega (fun y => f y :e B) x H)
        (binunionI2 A B (f x) (SepE2 Omega (fun y => f y :e B) x H)))
    (binunionE (preimage Omega f A) (preimage Omega f B) x Hx).
Qed.

Theorem preimage_binintersect :
  forall Omega, forall f : set -> set, forall A B,
    preimage Omega f (A :/\: B) = preimage Omega f A :/\: preimage Omega f B.
let Omega. let f : set -> set. let A. let B.
apply set_ext.
- prove preimage Omega f (A :/\: B) c= preimage Omega f A :/\: preimage Omega f B.
  let x.
  assume Hx: x :e preimage Omega f (A :/\: B).
  claim Hfx: f x :e A :/\: B.
    exact SepE2 Omega (fun y => f y :e A :/\: B) x Hx.
  claim HfxA: f x :e A.
    exact binintersectE1 A B (f x) Hfx.
  claim HfxB: f x :e B.
    exact binintersectE2 A B (f x) Hfx.
  apply binintersectI.
  + exact SepI Omega (fun y => f y :e A) x (SepE1 Omega (fun y => f y :e A :/\: B) x Hx) HfxA.
  + exact SepI Omega (fun y => f y :e B) x (SepE1 Omega (fun y => f y :e A :/\: B) x Hx) HfxB.
- prove preimage Omega f A :/\: preimage Omega f B c= preimage Omega f (A :/\: B).
  let x.
  assume Hx: x :e preimage Omega f A :/\: preimage Omega f B.
  claim HxA: x :e preimage Omega f A.
    exact binintersectE1 (preimage Omega f A) (preimage Omega f B) x Hx.
  claim HxB: x :e preimage Omega f B.
    exact binintersectE2 (preimage Omega f A) (preimage Omega f B) x Hx.
  claim HfxA: f x :e A.
    exact SepE2 Omega (fun y => f y :e A) x HxA.
  claim HfxB: f x :e B.
    exact SepE2 Omega (fun y => f y :e B) x HxB.
  exact SepI Omega (fun y => f y :e A :/\: B) x
    (SepE1 Omega (fun y => f y :e A) x HxA)
    (binintersectI A B (f x) HfxA HfxB).
Qed.

Theorem preimage_setminus :
  forall Omega, forall f : set -> set, forall A B,
    preimage Omega f (A :\: B) = preimage Omega f A :\: preimage Omega f B.
let Omega. let f : set -> set. let A. let B.
apply set_ext.
- prove preimage Omega f (A :\: B) c= preimage Omega f A :\: preimage Omega f B.
  let x.
  assume Hx: x :e preimage Omega f (A :\: B).
  claim Hfx: f x :e A :\: B.
    exact SepE2 Omega (fun y => f y :e A :\: B) x Hx.
  claim HfxA: f x :e A.
    exact setminusE1 A B (f x) Hfx.
  claim HfxNotB: f x /:e B.
    exact setminusE2 A B (f x) Hfx.
  apply setminusI.
  + exact SepI Omega (fun y => f y :e A) x (SepE1 Omega (fun y => f y :e A :\: B) x Hx) HfxA.
  + assume HContra.
    claim HfxB: f x :e B.
      exact SepE2 Omega (fun y => f y :e B) x HContra.
    exact HfxNotB HfxB.
- prove preimage Omega f A :\: preimage Omega f B c= preimage Omega f (A :\: B).
  let x.
  assume Hx: x :e preimage Omega f A :\: preimage Omega f B.
  claim HxA: x :e preimage Omega f A.
    exact setminusE1 (preimage Omega f A) (preimage Omega f B) x Hx.
  claim HxNotB: x /:e preimage Omega f B.
    exact setminusE2 (preimage Omega f A) (preimage Omega f B) x Hx.
  claim HfxA: f x :e A.
    exact SepE2 Omega (fun y => f y :e A) x HxA.
  claim HfxNotB: f x /:e B.
  {
    assume HfxB: f x :e B.
    claim HxB: x :e preimage Omega f B.
      exact SepI Omega (fun y => f y :e B) x (SepE1 Omega (fun y => f y :e A) x HxA) HfxB.
    exact HxNotB HxB.
  }
  exact SepI Omega (fun y => f y :e A :\: B) x
    (SepE1 Omega (fun y => f y :e A) x HxA)
    (setminusI A B (f x) HfxA HfxNotB).
Qed.

Theorem preimage_bigcup_nat :
  forall Omega, forall f : set -> set, forall A : set -> set,
    preimage Omega f (bigcup_nat A) = bigcup_nat (fun n => preimage Omega f (A n)).
let Omega. let f : set -> set. let A : set -> set.
set g := fun n : set => preimage Omega f (A n).
apply set_ext.
- prove preimage Omega f (bigcup_nat A) c= bigcup_nat g.
  let x.
  assume Hx: x :e preimage Omega f (bigcup_nat A).
  claim HxOmega: x :e Omega.
    exact SepE1 Omega (fun y => f y :e bigcup_nat A) x Hx.
  claim Hfx: f x :e bigcup_nat A.
    exact SepE2 Omega (fun y => f y :e bigcup_nat A) x Hx.
  claim BigDefA: bigcup_nat A = Union {A n|n :e omega}.
  { reflexivity. }
  claim HfxU: f x :e Union {A n|n :e omega}.
  {
    rewrite <- BigDefA.
    exact Hfx.
  }
  apply (UnionE_impred {A n|n :e omega} (f x) HfxU).
  let Y.
  assume Hfxy: f x :e Y.
  assume HY: Y :e {A n|n :e omega}.
  apply (ReplE_impred omega A Y HY).
  let n.
  assume Hn: n :e omega.
  assume HYeq: Y = A n.
  claim HfxAn: f x :e A n.
  {
    rewrite <- HYeq.
    exact Hfxy.
  }
  claim Hxgn: x :e g n.
  {
    exact SepI Omega (fun y => f y :e A n) x HxOmega HfxAn.
  }
  claim HgnIn: g n :e {g n|n :e omega}.
  {
    exact ReplI omega g n Hn.
  }
  claim BigDefg: bigcup_nat g = Union {g n|n :e omega}.
  { reflexivity. }
  rewrite BigDefg.
  exact UnionI {g n|n :e omega} x (g n) Hxgn HgnIn.
- prove bigcup_nat g c= preimage Omega f (bigcup_nat A).
  let x.
  assume Hx: x :e bigcup_nat g.
  claim BigDefg: bigcup_nat g = Union {g n|n :e omega}.
  { reflexivity. }
  claim HxU: x :e Union {g n|n :e omega}.
  {
    rewrite <- BigDefg.
    exact Hx.
  }
  apply (UnionE_impred {g n|n :e omega} x HxU).
  let Y.
  assume Hxy: x :e Y.
  assume HY: Y :e {g n|n :e omega}.
  apply (ReplE_impred omega g Y HY).
  let n.
  assume Hn: n :e omega.
  assume HYeq: Y = g n.
  claim Hxgn: x :e g n.
  {
    rewrite <- HYeq.
    exact Hxy.
  }
  claim HxOmega: x :e Omega.
    exact SepE1 Omega (fun y => f y :e A n) x Hxgn.
  claim HfxAn: f x :e A n.
    exact SepE2 Omega (fun y => f y :e A n) x Hxgn.
  claim HAnIn: A n :e {A n|n :e omega}.
  {
    exact ReplI omega A n Hn.
  }
  claim BigDefA: bigcup_nat A = Union {A n|n :e omega}.
  { reflexivity. }
  claim HfxU: f x :e Union {A n|n :e omega}.
  {
    exact UnionI {A n|n :e omega} (f x) (A n) HfxAn HAnIn.
  }
  claim HfxBig: f x :e bigcup_nat A.
  {
    rewrite BigDefA.
    exact HfxU.
  }
  exact SepI Omega (fun y => f y :e bigcup_nat A) x HxOmega HfxBig.
Qed.

Definition is_measurable : set -> set -> set -> set -> (set -> set) -> prop :=
  fun Omega F X G f =>
    (forall A :e G, preimage Omega f A :e F).

Definition indicator : set -> set -> set -> set :=
  fun Omega A x => If_i (x :e A) 1 0.

Theorem preimage_indicator_one :
  forall Omega A,
    preimage Omega (indicator Omega A) {1} = {x :e Omega | x :e A}.
let Omega. let A.
apply set_ext.
- prove preimage Omega (indicator Omega A) {1} c= {x :e Omega | x :e A}.
  let x.
  assume Hx: x :e preimage Omega (indicator Omega A) {1}.
  claim HxOmega: x :e Omega.
    exact SepE1 Omega (fun y => indicator Omega A y :e {1}) x Hx.
  claim Hind: indicator Omega A x :e {1}.
    exact SepE2 Omega (fun y => indicator Omega A y :e {1}) x Hx.
  claim Heq: indicator Omega A x = 1.
    exact SingE 1 (indicator Omega A x) Hind.
  apply orE (x :e A) (x /:e A) (x :e {x :e Omega | x :e A})
    (fun H => SepI Omega (fun y => y :e A) x HxOmega H)
    (fun HnA =>
      FalseE
        (neq_0_1
          (eq_trans 0 (indicator Omega A x) 1
            (eq_sym (indicator Omega A x) 0 (If_i_0 (x :e A) 1 0 HnA))
            Heq))
        (x :e {x :e Omega | x :e A}))
    (xm (x :e A)).
- prove {x :e Omega | x :e A} c= preimage Omega (indicator Omega A) {1}.
  let x.
  assume Hx: x :e {x :e Omega | x :e A}.
  claim HxOmega: x :e Omega.
    exact SepE1 Omega (fun y => y :e A) x Hx.
  claim HxA: x :e A.
    exact SepE2 Omega (fun y => y :e A) x Hx.
  claim Hpred: indicator Omega A x :e {1}.
  {
    claim Hdef: indicator Omega A x = If_i (x :e A) 1 0.
    { reflexivity. }
    rewrite Hdef.
    rewrite (If_i_1 (x :e A) 1 0 HxA).
    exact SingI 1.
  }
  exact SepI Omega (fun y => indicator Omega A y :e {1}) x HxOmega Hpred.
Qed.

Theorem preimage_indicator_zero :
  forall Omega A,
    preimage Omega (indicator Omega A) {0} = {x :e Omega | x /:e A}.
let Omega. let A.
apply set_ext.
- prove preimage Omega (indicator Omega A) {0} c= {x :e Omega | x /:e A}.
  let x.
  assume Hx: x :e preimage Omega (indicator Omega A) {0}.
  claim HxOmega: x :e Omega.
    exact SepE1 Omega (fun y => indicator Omega A y :e {0}) x Hx.
  claim Hind: indicator Omega A x :e {0}.
    exact SepE2 Omega (fun y => indicator Omega A y :e {0}) x Hx.
  claim Heq: indicator Omega A x = 0.
    exact SingE 0 (indicator Omega A x) Hind.
  apply SepI.
  + exact HxOmega.
  + assume HxA: x :e A.
    claim Heq1: indicator Omega A x = 1.
    {
      claim Hdef: indicator Omega A x = If_i (x :e A) 1 0.
      { reflexivity. }
      rewrite Hdef.
      rewrite (If_i_1 (x :e A) 1 0 HxA).
      reflexivity.
    }
    exact neq_0_1 (eq_trans 0 (indicator Omega A x) 1 (eq_sym (indicator Omega A x) 0 Heq) Heq1).
- prove {x :e Omega | x /:e A} c= preimage Omega (indicator Omega A) {0}.
  let x.
  assume Hx: x :e {x :e Omega | x /:e A}.
  claim HxOmega: x :e Omega.
    exact SepE1 Omega (fun y => y /:e A) x Hx.
  claim HxNotA: x /:e A.
    exact SepE2 Omega (fun y => y /:e A) x Hx.
  claim Hpred: indicator Omega A x :e {0}.
  {
    claim Hdef: indicator Omega A x = If_i (x :e A) 1 0.
    { reflexivity. }
    rewrite Hdef.
    rewrite (If_i_0 (x :e A) 1 0 HxNotA).
    exact SingI 0.
  }
  exact SepI Omega (fun y => indicator Omega A y :e {0}) x HxOmega Hpred.
Qed.

Theorem preimage_bigcup_fin :
  forall Omega, forall f : set -> set, forall A : set -> set, forall n,
    preimage Omega f (bigcup_fin A n) = bigcup_fin (fun i => preimage Omega f (A i)) n.
let Omega. let f : set -> set. let A : set -> set. let n.
set g := fun i : set => preimage Omega f (A i).
apply set_ext.
- prove preimage Omega f (bigcup_fin A n) c= bigcup_fin g n.
  let x.
  assume Hx: x :e preimage Omega f (bigcup_fin A n).
  claim HxOmega: x :e Omega.
    exact SepE1 Omega (fun y => f y :e bigcup_fin A n) x Hx.
  claim Hfx: f x :e bigcup_fin A n.
    exact SepE2 Omega (fun y => f y :e bigcup_fin A n) x Hx.
  claim BigDefA: bigcup_fin A n = Union {A i|i :e n}.
  { reflexivity. }
  claim HfxU: f x :e Union {A i|i :e n}.
  {
    rewrite <- BigDefA.
    exact Hfx.
  }
  apply (UnionE_impred {A i|i :e n} (f x) HfxU).
  let Y.
  assume Hfxy: f x :e Y.
  assume HY: Y :e {A i|i :e n}.
  apply (ReplE_impred n A Y HY).
  let i.
  assume Hi: i :e n.
  assume HYeq: Y = A i.
  claim HfxAi: f x :e A i.
  {
    rewrite <- HYeq.
    exact Hfxy.
  }
  claim Hxgi: x :e g i.
  {
    exact SepI Omega (fun y => f y :e A i) x HxOmega HfxAi.
  }
  claim HgiIn: g i :e {g i|i :e n}.
  {
    exact ReplI n g i Hi.
  }
  claim BigDefg: bigcup_fin g n = Union {g i|i :e n}.
  { reflexivity. }
  rewrite BigDefg.
  exact UnionI {g i|i :e n} x (g i) Hxgi HgiIn.
- prove bigcup_fin g n c= preimage Omega f (bigcup_fin A n).
  let x.
  assume Hx: x :e bigcup_fin g n.
  claim BigDefg: bigcup_fin g n = Union {g i|i :e n}.
  { reflexivity. }
  claim HxU: x :e Union {g i|i :e n}.
  {
    rewrite <- BigDefg.
    exact Hx.
  }
  apply (UnionE_impred {g i|i :e n} x HxU).
  let Y.
  assume Hxy: x :e Y.
  assume HY: Y :e {g i|i :e n}.
  apply (ReplE_impred n g Y HY).
  let i.
  assume Hi: i :e n.
  assume HYeq: Y = g i.
  claim Hxgi: x :e g i.
  {
    rewrite <- HYeq.
    exact Hxy.
  }
  claim HxOmega: x :e Omega.
    exact SepE1 Omega (fun y => f y :e A i) x Hxgi.
  claim HfxAi: f x :e A i.
    exact SepE2 Omega (fun y => f y :e A i) x Hxgi.
  claim HAiIn: A i :e {A i|i :e n}.
  {
    exact ReplI n A i Hi.
  }
  claim BigDefA: bigcup_fin A n = Union {A i|i :e n}.
  { reflexivity. }
  claim HfxU: f x :e Union {A i|i :e n}.
  {
    exact UnionI {A i|i :e n} (f x) (A i) HfxAi HAiIn.
  }
  claim HfxBig: f x :e bigcup_fin A n.
  {
    rewrite BigDefA.
    exact HfxU.
  }
  exact SepI Omega (fun y => f y :e bigcup_fin A n) x HxOmega HfxBig.
Qed.

Definition pairwise_disjoint_n : (set -> set) -> set -> prop :=
  fun f n => forall i j :e n, i <> j -> Disjoint (f i) (f j).

Definition simple_partition : set -> set -> (set -> set) -> set -> prop :=
  fun Omega F A n =>
    (forall i :e n, A i :e F)
    /\ pairwise_disjoint_n A n
    /\ bigcup_fin A n = Omega.

Definition simple_function_repr : set -> set -> (set -> set) -> (set -> set) -> (set -> set) -> set -> prop :=
  fun Omega F f v A n =>
    simple_partition Omega F A n
    /\ (forall x :e Omega, exists i :e n, x :e A i /\ f x = v i).
