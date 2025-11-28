Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Definition counterexample_S5 : set := 5.

Definition counterexample_V13 : set := 18 :\: 5.

Theorem counterexample_S5_card : equip 5 counterexample_S5.
exact equip_ref 5.
Qed.

Axiom counterexample_V13_card : equip 13 counterexample_V13.

Theorem counterexample_S5_sub : counterexample_S5 c= 18.
claim H17sub18: 17 c= 18. exact nat_trans 18 nat_18 17 In_17_18.
claim H5in18: 5 :e 18. exact H17sub18 5 In_5_17.
exact nat_trans 18 nat_18 5 H5in18.
Qed.

Theorem counterexample_V13_sub : counterexample_V13 c= 18.
intro x. assume H. exact setminusE1 18 5 x H.
Qed.

Theorem counterexample_disjoint : forall x :e counterexample_S5, forall y :e counterexample_V13, x <> y.
intro x. assume Hx. intro y. assume Hy. intro Heq.
claim Hy5: y :e 5. rewrite <- Heq. exact Hx.
exact setminusE2 18 5 y Hy Hy5.
Qed.

Theorem independent_set_dominance :
  forall V:set, forall R:set -> set -> prop, forall S:set, forall w:set,
    (forall x y, R x y -> R y x) ->
    triangle_free V R ->
    no_k_indep V R 6 ->
    equip 5 S ->
    is_indep_set V R S ->
    w :e V :\: S ->
    exists v :e S, R v w.
  intro V. intro R. intro S. intro w.
  assume Hsym. assume Htf. assume Hno6. assume Hequip5S. assume HisS. assume Hw.
  apply dneg.
  assume H_neg_ex: ~(exists v :e S, R v w).
  claim H_all_non_adj: forall v :e S, ~R v w.
    intro v. assume HvS.
    intro HRvw.
    apply H_neg_ex.
    witness v. apply andI. exact HvS. exact HRvw.
  
  let S6 := S :\/: Sing w.

  claim H_w_in_V: w :e V.
    exact setminusE1 V S w Hw.

  claim H_w_not_in_S: w /:e S.
    exact setminusE2 V S w Hw.

  claim H_S_sub_V: S c= V.
    exact andEL (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)) HisS.

  claim H_S6_sub_V: S6 c= V.
    intro x. assume Hx.
    apply binunionE x S (Sing w) Hx.
    - assume HxS. exact H_S_sub_V x HxS.
    - assume Hxw. apply SingE w x Hxw. intro Hbeq. rewrite Hbeq. exact H_w_in_V.

  claim H_S_indep_unpacked: forall x :e S, forall y :e S, x <> y -> ~(R x y).
    exact andER (S c= V) (forall x :e S, forall y :e S, x <> y -> ~(R x y)) HisS.

  claim H_S6_indep: is_indep_set V R S6.
    apply andI.
    - exact H_S6_sub_V.
    - intro x. assume Hx. intro y. assume Hy. intro Hneq. intro HRxy.
      apply binunionE x S (Sing w) Hx.
      + assume HxS.
        apply binunionE y S (Sing w) Hy.
        * assume HyS.
          exact H_S_indep_unpacked x HxS y HyS Hneq HRxy.
        * assume Hyw. apply SingE w y Hyw. intro Hyeqw.
          claim HRxw: R x w. rewrite <- Hyeqw. exact HRxy.
          exact H_all_non_adj x HxS HRxw.
      + assume Hxw. apply SingE w x Hxw. intro Hxeqw.
        apply binunionE y S (Sing w) Hy.
        * assume HyS.
          claim HRwy: R w y. rewrite <- Hxeqw. exact HRxy.
          claim HRyw: R y w. exact Hsym y w HRwy.
          exact H_all_non_adj y HyS HRyw.
        * assume Hyw. apply SingE w y Hyw. intro Hyeqw.
          claim Hww: w <> w. rewrite <- Hxeqw. rewrite <- Hyeqw. exact Hneq.
          exact Hww (eq_refl w).

  claim H_S6_card: equip 6 S6.
    apply Hequip5S.
    let f. assume Hf.
    apply andEL (forall x :e S, f x :e 5) ((forall x y :e S, f x = f y -> x = y) /\ (forall y :e 5, exists x :e S, f x = y)) Hf.
    assume Hf_codom. assume Hf_bij.
    apply andEL (forall x y :e S, f x = f y -> x = y) (forall y :e 5, exists x :e S, f x = y) Hf_bij.
    assume Hfinj. assume Hfsurj.
    let g := fun x => If_i (x = w) 5 (f x).
    witness g.
    apply and3I.
    - intro x. assume Hx.
      apply binunionE x S (Sing w) Hx.
      + assume HxS.
        claim Hxneqw: x <> w.
           intro Hxeqw. claim HwS: w :e S. rewrite <- Hxeqw. exact HxS. exact H_w_not_in_S HwS.
        rewrite (If_i_0 (x=w) 5 (f x) Hxneqw).
        claim Hfx5: f x :e 5. exact Hf_codom x HxS.
        claim H5sub6: 5 c= 6.
          exact nat_trans 6 nat_6 5 In_5_6.
        exact H5sub6 (f x) Hfx5.
      + assume Hxw. apply SingE w x Hxw. intro Hxeqw.
        rewrite Hxeqw.
        rewrite (If_i_1 (w=w) 5 (f w) (eq_refl w)).
        exact In_5_6.
    - intro x. assume Hx. intro y. assume Hy.
      apply binunionE x S (Sing w) Hx.
      + assume HxS.
        apply binunionE y S (Sing w) Hy.
        * assume HyS.
          claim Hxneqw: x <> w. intro C. claim HwS: w :e S. rewrite <- C. exact HxS. exact H_w_not_in_S HwS.
          claim Hyneqw: y <> w. intro C. claim HwS: w :e S. rewrite <- C. exact HyS. exact H_w_not_in_S HwS.
          rewrite (If_i_0 (x=w) 5 (f x) Hxneqw).
          rewrite (If_i_0 (y=w) 5 (f y) Hyneqw).
          intro Hgeq.
          exact Hfinj x HxS y HyS Hgeq.
        * assume Hyw. apply SingE w y Hyw. intro Hyeqw.
          claim Hxneqw: x <> w. intro C. claim HwS: w :e S. rewrite <- C. exact HxS. exact H_w_not_in_S HwS.
          rewrite Hyeqw.
          rewrite (If_i_0 (x=w) 5 (f x) Hxneqw).
          rewrite (If_i_1 (w=w) 5 (f w) (eq_refl w)).
          intro Hfx5.
          claim Hfx_in_5: f x :e 5. exact Hf_codom x HxS.
          rewrite Hfx5 at Hfx_in_5.
          exact In_irref 5 Hfx_in_5.
      + assume Hxw. apply SingE w x Hxw. intro Hxeqw.
        apply binunionE y S (Sing w) Hy.
        * assume HyS.
          claim Hyneqw: y <> w. intro C. claim HwS: w :e S. rewrite <- C. exact HyS. exact H_w_not_in_S HwS.
          rewrite Hxeqw.
          rewrite (If_i_1 (w=w) 5 (f w) (eq_refl w)).
          rewrite (If_i_0 (y=w) 5 (f y) Hyneqw).
          intro H5fy. symmetric at H5fy.
          claim Hfy_in_5: f y :e 5. exact Hf_codom y HyS.
          rewrite H5fy at Hfy_in_5.
          exact In_irref 5 Hfy_in_5.
        * assume Hyw. apply SingE w y Hyw. intro Hyeqw.
          rewrite Hxeqw. rewrite Hyeqw. exact eq_refl w.
    - intro z. assume Hz.
      claim H_surj_5: forall k :e 5, exists x :e S, f x = k.
        exact Hfsurj.
      
      apply cases_6 z Hz (fun z:set => exists x :e S6, g x = z).
      + exact H_surj_5 0 In_0_5.
      + exact H_surj_5 1 In_1_5.
      + exact H_surj_5 2 In_2_5.
      + exact H_surj_5 3 In_3_5.
      + exact H_surj_5 4 In_4_5.
      + witness w.
        apply andI.
        * apply binunionI2 S (Sing w) w (SingI w).
        * rewrite (If_i_1 (w=w) 5 (f w) (eq_refl w)).
          reflexivity.

  exact Hno6 S6 H_S6_sub_V H_S6_card H_S6_indep.
Qed.

Theorem intersection_nonempty_false :
  forall R:set -> set -> prop,
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
    ~(exists w :e V13, forall v :e S5, ~R v w).
intro R. intro S5. intro V13.
assume Hsym. assume Htf. assume Hno6. assume Heq5. assume Heq13. assume HS5sub. assume HV13sub. assume HindS5. assume Hdisj. assume Hdeg.
apply notI.
assume Hex.
apply Hex.
let w. assume Hw.
claim HwV13: w :e V13.
  exact andEL (w :e V13) (forall v :e S5, ~R v w) Hw.
claim HwNoAdj: forall v :e S5, ~R v w.
  exact andER (w :e V13) (forall v :e S5, ~R v w) Hw.
claim HwNotInS5: w /:e S5.
  intro HwS5.
  exact Hdisj w HwS5 w HwV13 (eq_refl w).
claim HwV: w :e 18.
  exact HV13sub w HwV13.
claim Hw_set_diff: w :e 18 :\: S5.
  exact setminusI 18 S5 w HwV HwNotInS5.
claim Hex_adj: exists v :e S5, R v w.
  exact independent_set_dominance 18 R S5 w Hsym Htf Hno6 Heq5 HindS5 Hw_set_diff.
apply Hex_adj.
let v. assume Hv.
claim HvS5: v :e S5. exact andEL (v :e S5) (R v w) Hv.
claim HRvw: R v w. exact andER (v :e S5) (R v w) Hv.
exact HwNoAdj v HvS5 HRvw.
Qed.
