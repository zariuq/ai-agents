Section Blocker2_Full.

Variable E : set -> set -> prop.

Definition valid_coloring : (set -> set) -> prop :=
  fun col => forall x y : set, E x y -> col x <> col y.

Definition in_01_chain : (set -> set) -> set -> prop :=
  fun col v => col v = 0 \/ col v = 1.

Variable v0 : set.
Variable v1 : set.
Variable v2 : set.

Hypothesis v0_neq_v1 : v0 <> v1.
Hypothesis v0_neq_v2 : v0 <> v2.
Hypothesis v1_neq_v2 : v1 <> v2.

Hypothesis edge_01 : E v0 v1.
Hypothesis edge_02 : E v0 v2.

Variable col : set -> set.

Hypothesis col_v0 : col v0 = 0.
Hypothesis col_v1 : col v1 = 1.
Hypothesis col_v2 : col v2 = 0.

Theorem v0_in_chain : in_01_chain col v0.
prove col v0 = 0 \/ col v0 = 1.
apply orIL.
exact col_v0.
Qed.

Theorem v1_in_chain : in_01_chain col v1.
prove col v1 = 0 \/ col v1 = 1.
apply orIR.
exact col_v1.
Qed.

Theorem v2_in_chain : in_01_chain col v2.
prove col v2 = 0 \/ col v2 = 1.
apply orIL.
exact col_v2.
Qed.

Theorem v0_v2_same_original_color : col v0 = col v2.
rewrite col_v0.
rewrite col_v2.
reflexivity.
Qed.

Theorem swap_both_become_1 :
  forall col' : set -> set,
    col' v0 = 1 -> col' v2 = 1 -> col' v0 = col' v2.
let col'.
assume H0: col' v0 = 1.
assume H2: col' v2 = 1.
rewrite H0.
rewrite H2.
reflexivity.
Qed.

Theorem same_color_on_edge_invalid :
  forall col' : set -> set,
    col' v0 = col' v2 -> E v0 v2 -> ~valid_coloring col'.
let col'.
assume Hsame: col' v0 = col' v2.
assume Hedge: E v0 v2.
assume Hvalid: valid_coloring col'.
prove False.
apply Hvalid v0 v2 Hedge.
exact Hsame.
Qed.

Theorem swap_invalidates_coloring :
  forall col' : set -> set,
    col' v0 = 1 -> col' v2 = 1 -> ~valid_coloring col'.
let col'.
assume H0: col' v0 = 1.
assume H2: col' v2 = 1.
apply same_color_on_edge_invalid col'.
- apply swap_both_become_1 col' H0 H2.
- exact edge_02.
Qed.

Theorem chain_exists_but_swap_invalid :
  (in_01_chain col v0 /\ in_01_chain col v2) /\
  (forall col' : set -> set, col' v0 = 1 -> col' v2 = 1 -> ~valid_coloring col').
apply andI.
- apply andI.
  + exact v0_in_chain.
  + exact v2_in_chain.
- exact swap_invalidates_coloring.
Qed.

End Blocker2_Full.
