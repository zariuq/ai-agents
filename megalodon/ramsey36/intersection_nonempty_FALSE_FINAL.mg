Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Axiom counterexample_R : set -> set -> prop.

Definition counterexample_S5 : set := 5.

Definition counterexample_V13 : set := 18 :\: 5.

Axiom counterexample_sym : forall x y, counterexample_R x y -> counterexample_R y x.

Axiom counterexample_tf : triangle_free 18 counterexample_R.

Axiom counterexample_no6 : no_k_indep 18 counterexample_R 6.

Theorem counterexample_S5_card : equip 5 counterexample_S5.
exact equip_ref 5.
Qed.

Axiom counterexample_V13_card : equip 13 counterexample_V13.

Theorem counterexample_S5_sub : counterexample_S5 c= 18.
exact nat_trans 18 nat_18 5 In_5_18.
Qed.

Theorem counterexample_V13_sub : counterexample_V13 c= 18.
intro x. assume H. exact setminusE1 18 5 x H.
Qed.

Axiom counterexample_S5_indep : is_indep_set 18 counterexample_R counterexample_S5.

Theorem counterexample_disjoint : forall x :e counterexample_S5, forall y :e counterexample_V13, x <> y.
intro x. assume Hx. intro y. assume Hy. intro Heq.
claim Hy5: y :e 5. rewrite <- Heq. exact Hx.
exact setminusE2 18 5 y Hy Hy5.
Qed.

Axiom counterexample_degree : forall v :e counterexample_S5,
  exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~counterexample_R v t) /\ v /:e T.

Theorem intersection_nonempty_false :
  ~(forall R:set -> set -> prop,
    forall S5 V13:set,
    (forall x y, R x y -> R y x) ->
    triangle_free 18 R ->
    no_k_indep 18 R 6 ->
    equip 5 S5 ->
    equip 13 V13 ->
    S5 c= 18 ->
    V13 c= 18 ->
    is_indep_set 18 R S5 ->
    (forall x :e S5, forall y :e V13, x <> y) ->
    (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) ->
    exists w :e V13, forall v :e S5, ~R v w).
prove ~(forall R:set -> set -> prop,
         forall S5 V13:set,
         (forall x y, R x y -> R y x) ->
         triangle_free 18 R ->
         no_k_indep 18 R 6 ->
         equip 5 S5 ->
         equip 13 V13 ->
         S5 c= 18 ->
         V13 c= 18 ->
         is_indep_set 18 R S5 ->
         (forall x :e S5, forall y :e V13, x <> y) ->
         (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) ->
         exists w :e V13, forall v :e S5, ~R v w).
assume Hlemma: forall R:set -> set -> prop,
                forall S5 V13:set,
                (forall x y, R x y -> R y x) ->
                triangle_free 18 R ->
                no_k_indep 18 R 6 ->
                equip 5 S5 ->
                equip 13 V13 ->
                S5 c= 18 ->
                V13 c= 18 ->
                is_indep_set 18 R S5 ->
                (forall x :e S5, forall y :e V13, x <> y) ->
                (forall v :e S5, exists T:set, T c= 18 /\ equip 12 T /\ (forall t :e T, ~R v t) /\ v /:e T) ->
                exists w :e V13, forall v :e S5, ~R v w.
prove False.
claim Hconclusion: exists w :e counterexample_V13, forall v :e counterexample_S5, ~counterexample_R v w.
  exact Hlemma counterexample_R counterexample_S5 counterexample_V13
        counterexample_sym counterexample_tf counterexample_no6
        counterexample_S5_card counterexample_V13_card
        counterexample_S5_sub counterexample_V13_sub
        counterexample_S5_indep counterexample_disjoint
        counterexample_degree.
apply Hconclusion.
let w.
assume Hw: w :e counterexample_V13 /\ (forall v :e counterexample_S5, ~counterexample_R v w).
claim HwV13: w :e counterexample_V13.
  exact andEL (w :e counterexample_V13) (forall v :e counterexample_S5, ~counterexample_R v w) Hw.
claim Hno_edges: forall v :e counterexample_S5, ~counterexample_R v w.
  exact andER (w :e counterexample_V13) (forall v :e counterexample_S5, ~counterexample_R v w) Hw.
claim Hex_neighbor: exists v :e counterexample_S5, counterexample_R v w.
  apply dneg.
  assume H_neg_ex: ~(exists v :e counterexample_S5, counterexample_R v w).
  claim H_all_non_adj: forall v :e counterexample_S5, ~counterexample_R v w.
    intro v. assume HvS5.
    intro HRvw.
    apply H_neg_ex.
    witness v. apply andI. exact HvS5. exact HRvw.
  
  let S6 := counterexample_S5 :\/: Sing w.

  claim Hw_in_18 : w :e 18.
    exact counterexample_V13_sub w HwV13.

  claim H_S6_sub: S6 c= 18.
    intro x. assume Hx.
    apply binunionE x counterexample_S5 (Sing w) Hx.
    - assume HxS5. exact counterexample_S5_sub x HxS5.
    - assume Hxw. apply SingE w x Hxw. intro Hbeq. rewrite Hbeq. exact Hw_in_18.

  claim Hw_not_in_S5: w /:e counterexample_S5.
    intro HwS5.
    exact counterexample_disjoint w w HwS5 HwV13 (eq_refl w).

  claim H_S5_indep_unpacked: forall x :e counterexample_S5, forall y :e counterexample_S5, x <> y -> ~counterexample_R x y.
    exact andER (counterexample_S5 c= 18) (forall x :e counterexample_S5, forall y :e counterexample_S5, x <> y -> ~counterexample_R x y) counterexample_S5_indep.

  claim H_S6_indep: is_indep_set 18 counterexample_R S6.
    apply andI.
    - exact H_S6_sub.
    - intro x. assume Hx. intro y. assume Hy. intro Hneq. intro HRxy.
      apply binunionE x counterexample_S5 (Sing w) Hx.
      + assume HxS5.
        apply binunionE y counterexample_S5 (Sing w) Hy.
        * assume HyS5.
          exact H_S5_indep_unpacked x HxS5 y HyS5 Hneq HRxy.
        * assume Hyw. apply SingE w y Hyw. intro Hyeqw.
          claim HRxw: counterexample_R x w. rewrite <- Hyeqw. exact HRxy.
          exact H_all_non_adj x HxS5 HRxw.
      + assume Hxw. apply SingE w x Hxw. intro Hxeqw.
        apply binunionE y counterexample_S5 (Sing w) Hy.
        * assume HyS5.
          claim HRwy: counterexample_R w y. rewrite <- Hxeqw. exact HRxy.
          claim HRyw: counterexample_R y w. exact counterexample_sym w y HRwy.
          exact H_all_non_adj y HyS5 HRyw.
        * assume Hyw. apply SingE w y Hyw. intro Hyeqw.
          claim Hww: w <> w. rewrite <- Hxeqw. rewrite <- Hyeqw. exact Hneq.
          exact Hww (eq_refl w).

  claim H_S6_card: equip 6 S6.
    apply counterexample_S5_card.
    let f. assume Hf.
    apply andEL (forall x :e counterexample_S5, f x :e 5) ((forall x y :e counterexample_S5, f x = f y -> x = y) /\ (forall y :e 5, exists x :e counterexample_S5, f x = y)) Hf.
    assume Hf_codom. assume Hf_bij.
    apply andEL (forall x y :e counterexample_S5, f x = f y -> x = y) (forall y :e 5, exists x :e counterexample_S5, f x = y) Hf_bij.
    assume Hfinj. assume Hfsurj.
    let g := fun x => If_i (x = w) 5 (f x).
    witness g.
    apply and3I.
    - intro x. assume Hx.
      apply binunionE x counterexample_S5 (Sing w) Hx.
      + assume HxS5.
        claim Hxneqw: x <> w.
           intro Hxeqw. claim HwS5: w :e counterexample_S5. rewrite <- Hxeqw. exact HxS5. exact Hw_not_in_S5 HwS5.
        rewrite (If_i_0 (x=w) 5 (f x) Hxneqw).
        claim Hfx5: f x :e 5. exact Hf_codom x HxS5.
        claim H5sub6: 5 c= 6.
          exact nat_trans 6 nat_6 5 In_5_6.
        exact H5sub6 (f x) Hfx5.
      + assume Hxw. apply SingE w x Hxw. intro Hxeqw.
        rewrite Hxeqw.
        rewrite (If_i_1 (w=w) 5 (f w) (eq_refl w)).
        exact In_5_6.
    - intro x. assume Hx. intro y. assume Hy.
      apply binunionE x counterexample_S5 (Sing w) Hx.
      + assume HxS5.
        apply binunionE y counterexample_S5 (Sing w) Hy.
        * assume HyS5.
          claim Hxneqw: x <> w. intro C. claim HwS5: w :e counterexample_S5. rewrite <- C. exact HxS5. exact Hw_not_in_S5 HwS5.
          claim Hyneqw: y <> w. intro C. claim HwS5: w :e counterexample_S5. rewrite <- C. exact HyS5. exact Hw_not_in_S5 HwS5.
          rewrite (If_i_0 (x=w) 5 (f x) Hxneqw).
          rewrite (If_i_0 (y=w) 5 (f y) Hyneqw).
          intro Hgeq.
          exact Hfinj x HxS5 y HyS5 Hgeq.
        * assume Hyw. apply SingE w y Hyw. intro Hyeqw.
          claim Hxneqw: x <> w. intro C. claim HwS5: w :e counterexample_S5. rewrite <- C. exact HxS5. exact Hw_not_in_S5 HwS5.
          rewrite Hyeqw.
          rewrite (If_i_0 (x=w) 5 (f x) Hxneqw).
          rewrite (If_i_1 (w=w) 5 (f w) (eq_refl w)).
          intro Hfx5.
          claim Hfx_in_5: f x :e 5. exact Hf_codom x HxS5.
          rewrite Hfx5 at Hfx_in_5.
          exact In_irref 5 Hfx_in_5.
      + assume Hxw. apply SingE w x Hxw. intro Hxeqw.
        apply binunionE y counterexample_S5 (Sing w) Hy.
        * assume HyS5.
          claim Hyneqw: y <> w. intro C. claim HwS5: w :e counterexample_S5. rewrite <- C. exact HyS5. exact Hw_not_in_S5 HwS5.
          rewrite Hxeqw.
          rewrite (If_i_1 (w=w) 5 (f w) (eq_refl w)).
          rewrite (If_i_0 (y=w) 5 (f y) Hyneqw).
          intro H5fy. symmetric at H5fy.
          claim Hfy_in_5: f y :e 5. exact Hf_codom y HyS5.
          rewrite H5fy at Hfy_in_5.
          exact In_irref 5 Hfy_in_5.
        * assume Hyw. apply SingE w y Hyw. intro Hyeqw.
          rewrite Hxeqw. rewrite Hyeqw. exact eq_refl w.
    - intro z. assume Hz.
      claim H_surj_5: forall k :e 5, exists x :e S6, g x = k.
        intro k. assume Hk5.
        claim Hex_x: exists x :e counterexample_S5, f x = k.
          exact Hfsurj k Hk5.
        apply Hex_x. let x. assume Hx.
        claim HxS5: x :e counterexample_S5. exact andEL (x :e counterexample_S5) (f x = k) Hx.
        claim Hfxk: f x = k. exact andER (x :e counterexample_S5) (f x = k) Hx.
        witness x.
        apply andI.
        * apply binunionI1 counterexample_S5 (Sing w) x HxS5.
        * claim Hxneqw: x <> w. intro C. claim HwS5: w :e counterexample_S5. rewrite <- C. exact HxS5. exact Hw_not_in_S5 HwS5.
          rewrite (If_i_0 (x=w) 5 (f x) Hxneqw).
          exact Hfxk.
      
      apply cases_6 z Hz (fun z:set => exists x :e S6, g x = z).
      + exact H_surj_5 0 In_0_5.
      + exact H_surj_5 1 In_1_5.
      + exact H_surj_5 2 In_2_5.
      + exact H_surj_5 3 In_3_5.
      + exact H_surj_5 4 In_4_5.
      + witness w.
        apply andI.
        * apply binunionI2 counterexample_S5 (Sing w) w (SingI w).
        * rewrite (If_i_1 (w=w) 5 (f w) (eq_refl w)).
          reflexivity.

  exact counterexample_no6 S6 H_S6_sub H_S6_card H_S6_indep.

apply Hex_neighbor.
let v.
assume Hv: v :e counterexample_S5 /\ counterexample_R v w.
claim HvS5: v :e counterexample_S5.
  exact andEL (v :e counterexample_S5) (counterexample_R v w) Hv.
claim HRvw: counterexample_R v w.
  exact andER (v :e counterexample_S5) (counterexample_R v w) Hv.
exact Hno_edges v HvS5 HRvw.
Qed.
