theory Disk_KCSD
  imports "../Core/GraphPrimitives"
begin

(* Chains: per-edge colors; finite support via finiteness of E. *)
type_synonym ('e) chain = "'e => col"

(* Per-edge dot lifted to chains via finite sum (parity). *)
definition dot_chain :: "('e set) => ('e) chain => ('e) chain => bool" where
  "dot_chain Edges x z == (SUM e:Edges. if dot2 (x e) (z e) then (1::nat) else 0) mod 2 = 1"

(* XOR on chains: pointwise XOR of colors *)
fun xor_chain :: "'e chain => 'e chain => 'e chain" where
  "xor_chain f g = (\<lambda>e. let (a1,b1) = f e; (a2,b2) = g e in (a1 ~= a2, b1 ~= b2))"

(* XOR-span: inductive closure under XOR *)
inductive_set cspan :: "('e chain set) => ('e chain set)" for S where
  cspan_zero: "zero_chain : cspan S"
| cspan_xor: "s : S ==> y : cspan S ==> xor_chain s y : cspan S"

(* Finite XOR fold over a set of chains *)
definition xor_fold :: "('a => 'e chain) => 'a set => 'e chain" where
  "xor_fold f A = Finite_Set.fold (%a acc. xor_chain (f a) acc) zero_chain A"

lemma xor_fold_empty: "xor_fold f {} = zero_chain"
  unfolding xor_fold_def by simp

(* Boolean algebra helpers - needed for xor_chain lemmas *)
lemma bool_neq_comm: "(a::bool) \<noteq> b \<longleftrightarrow> b \<noteq> a"
  by auto

lemma bool_eq_not_comm: "((a::bool) = (\<not> b)) = (b = (\<not> a))"
  by auto

lemma bool_xor_assoc: "((a::bool) \<noteq> b) \<noteq> c \<longleftrightarrow> a \<noteq> (b \<noteq> c)"
  by auto

(* XOR chain is commutative *)
lemma xor_chain_comm: "xor_chain x y = xor_chain y x"
  by (auto simp: xor_chain.simps Let_def split: prod.splits)

(* XOR chain is associative *)
lemma xor_chain_assoc: "xor_chain (xor_chain x y) z = xor_chain x (xor_chain y z)"
  by (auto simp: xor_chain.simps Let_def bool_xor_assoc split: prod.splits)

(* Left-commute property (AC law) *)
lemma xor_chain_left_commute: "xor_chain x (xor_chain y z) = xor_chain y (xor_chain x z)"
proof -
  have "xor_chain x (xor_chain y z) = xor_chain (xor_chain x y) z"
    by (simp only: xor_chain_assoc[symmetric])
  also have "... = xor_chain (xor_chain y x) z"
    by (simp only: xor_chain_comm)
  also have "... = xor_chain y (xor_chain x z)"
    by (simp only: xor_chain_assoc)
  finally show ?thesis .
qed

(* XOR is self-inverse: x ⊕ x = 0 *)
lemma xor_chain_self_inverse: "xor_chain x x = zero_chain"
  by (auto simp: xor_chain.simps zero_chain_def Let_def split: prod.splits)

(* Zero is left identity for XOR *)
lemma xor_zero_left: "xor_chain zero_chain x = x"
  by (auto simp: xor_chain.simps zero_chain_def Let_def split: prod.splits)

(* Zero is right identity for XOR *)
lemma xor_zero_right: "xor_chain x zero_chain = x"
  by (auto simp: xor_chain.simps zero_chain_def Let_def split: prod.splits)

(* comp_fun_commute instance for xor_chain *)
interpretation xor_commute: comp_fun_commute "\<lambda>x acc. xor_chain x acc"
proof
  fix x y
  show "(\<lambda>acc. xor_chain x acc) \<circ> (\<lambda>acc. xor_chain y acc) =
        (\<lambda>acc. xor_chain y acc) \<circ> (\<lambda>acc. xor_chain x acc)"
  proof (rule ext)
    fix z
    have "((\<lambda>acc. xor_chain x acc) \<circ> (\<lambda>acc. xor_chain y acc)) z = xor_chain x (xor_chain y z)"
      by simp
    also have "... = xor_chain (xor_chain x y) z"
      by (simp only: xor_chain_assoc[symmetric])
    also have "... = xor_chain (xor_chain y x) z"
      by (simp only: xor_chain_comm)
    also have "... = xor_chain y (xor_chain x z)"
      by (simp only: xor_chain_assoc)
    also have "... = ((\<lambda>acc. xor_chain y acc) \<circ> (\<lambda>acc. xor_chain x acc)) z"
      by simp
    finally show "((\<lambda>acc. xor_chain x acc) \<circ> (\<lambda>acc. xor_chain y acc)) z =
                  ((\<lambda>acc. xor_chain y acc) \<circ> (\<lambda>acc. xor_chain x acc)) z" .
  qed
qed

(* Parametric interpretation for xor_fold with function f *)
interpretation xor_fold_cfc: comp_fun_commute "\<lambda>a acc. xor_chain (f a) acc"
  for f :: "'a \<Rightarrow> 'e chain"
proof
  fix a b
  show "(\<lambda>acc. xor_chain (f a) acc) \<circ> (\<lambda>acc. xor_chain (f b) acc) =
        (\<lambda>acc. xor_chain (f b) acc) \<circ> (\<lambda>acc. xor_chain (f a) acc)"
  proof (rule ext)
    fix x
    have "((\<lambda>acc. xor_chain (f a) acc) \<circ> (\<lambda>acc. xor_chain (f b) acc)) x =
          xor_chain (f a) (xor_chain (f b) x)"
      by simp
    also have "... = xor_chain (xor_chain (f a) (f b)) x"
      by (simp only: xor_chain_assoc[symmetric])
    also have "... = xor_chain (xor_chain (f b) (f a)) x"
      by (simp only: xor_chain_comm)
    also have "... = xor_chain (f b) (xor_chain (f a) x)"
      by (simp only: xor_chain_assoc)
    also have "... = ((\<lambda>acc. xor_chain (f b) acc) \<circ> (\<lambda>acc. xor_chain (f a) acc)) x"
      by simp
    finally show "((\<lambda>acc. xor_chain (f a) acc) \<circ> (\<lambda>acc. xor_chain (f b) acc)) x =
                  ((\<lambda>acc. xor_chain (f b) acc) \<circ> (\<lambda>acc. xor_chain (f a) acc)) x" .
  qed
qed

(* fold_insert lemma for xor_fold *)
lemma xor_fold_insert:
  assumes "finite A" "x \<notin> A"
  shows "xor_fold f (insert x A) = xor_chain (f x) (xor_fold f A)"
  unfolding xor_fold_def
  using xor_fold_cfc.fold_insert[OF assms] .

(* cspan is closed under XOR of its own elements *)
lemma cspan_closed_under_xor:
  assumes "x : (cspan S :: ('e chain) set)"
  assumes "y : cspan S"
  shows "xor_chain x y : cspan S"
  using assms(1)
proof (induction rule: cspan.induct)
  case cspan_zero
  from assms(2) show ?case
    by (auto simp: xor_chain.simps zero_chain_def Let_def split: prod.splits)
next
  case (cspan_xor s z)
  (* x = xor_chain s z where s ∈ S, z ∈ cspan S
     IH: xor_chain z y ∈ cspan S
     Goal: xor_chain (xor_chain s z) y ∈ cspan S *)
  have eq: "xor_chain (xor_chain s z) y = xor_chain s (xor_chain z y)"
    using xor_chain_assoc by metis
  have "xor_chain s (xor_chain z y) : cspan S"
    by (rule cspan.cspan_xor[OF cspan_xor.hyps(1) cspan_xor.IH])
  with eq show ?case by simp
qed

(* ========================================================================= *)
(* B1: XOR Fold Closure (M4b.1)                                            *)
(* ========================================================================= *)

(* M4b.fold_closure: Finite XOR fold stays in cspan *)
lemma cspan_closed_xor_fold:
  assumes "finite A"
  assumes "ALL a : A. f a : (cspan S :: ('e chain) set)"
  shows "xor_fold f A : cspan S"
  using assms
proof (induction A rule: finite_induct)
  case empty
  have "xor_fold f {} = zero_chain"
    by (simp add: xor_fold_empty)
  thus ?case by (simp add: cspan_zero)
next
  case (insert x F)
  from insert.IH insert.prems have IH: "xor_fold f F : cspan S" by simp
  from insert.prems have fx_in: "f x : cspan S" by simp

  (* Use cspan closure under XOR *)
  from fx_in IH have xor_in: "xor_chain (f x) (xor_fold f F) : cspan S"
    by (rule cspan_closed_under_xor)

  have eq: "xor_fold f (insert x F) = xor_chain (f x) (xor_fold f F)"
    using insert.hyps by (rule xor_fold_insert)
  with xor_in show ?case by simp
qed

(* Stub predicates: proper 3-edge-coloring, Kempe cycles, closure, generators. *)
consts
  proper3 :: "('e => col) => bool"
  kempe_cycle :: "col => col => ('e => col) => 'e set => bool"
  toggle_on :: "('e => col) => 'e set => ('e => col)"
  gens_from_closure :: "('e => col) => ('e chain) set"   (* the set G from your note *)
  incident :: "'v => 'e => bool"  (* vertex-edge incidence relation *)

(* Cycle constraints per coordinate (parity 0 at each vertex) *)
locale disk_cubic =
  fixes G :: "('v,'e) graph" and B :: "'e set"
  assumes finE: "finite (E G)"
  assumes finV: "finite (V G)"
  assumes boundary_two_cycles:
    "EX B1 B2. B1 <= E G & B2 <= E G & B1 Int B2 = {} & B = B1 Un B2"
begin

(* ========================================================================= *)
(* B2: Support and Masking Infrastructure                                   *)
(* ========================================================================= *)

(* Support of a chain: edges where it is non-zero *)
definition support :: "('e chain) => 'e set" where
  "support y = {e. y e ~= (False, False)}"

(* Zero-boundary chains: vertex parity = 0 at each vertex in each coordinate *)
definition zero_boundary :: "('e chain) set" where
  "zero_boundary = {y. ALL v : V G.
    even (card {e : E G. incident v e & fst (y e)}) &
    even (card {e : E G. incident v e & snd (y e)})}"

(* Helper: zero_chain is in zero_boundary *)
lemma zero_chain_in_zero_boundary: "zero_chain : zero_boundary"
  unfolding zero_boundary_def zero_chain_def by simp

(* Helper lemma for controlled sym_diff rewriting (NO [simp] to avoid loops!) *)
lemma sym_diff_eq_Un_Diff:
  "sym_diff A B = (A - B) Un (B - A)"
  by auto

(* Main parity lemma for disjoint union form *)
lemma even_card_Un_Diff:
  assumes "finite A" "finite B"
  shows "even (card ((A - B) Un (B - A))) = (even (card A) = even (card B))"
proof -
  let ?m = "card (A - B)"
  let ?n = "card (B - A)"
  let ?k = "card (A Int B)"
  have disj: "(A - B) Int (B - A) = {}" by blast
  have union: "card ((A - B) Un (B - A)) = ?m + ?n"
    using assms disj by (simp add: card_Un_disjoint)
  have cardA: "card A = ?m + ?k"
    by (metis add.commute assms(1) card_Int_Diff)
  have cardB: "card B = ?n + ?k"
    by (metis Int_commute add.commute assms(2) card_Int_Diff)
  have "even (card ((A - B) Un (B - A))) =
        (even (card A) = even (card B))"
    using cardA cardB union by force
  thus ?thesis .
qed

corollary even_card_sym_diff:
  assumes "finite A" "finite B"
  shows "even (card (sym_diff A B)) = (even (card A) = even (card B))"
proof -
  show ?thesis
    using assms by (simp add: sym_diff_eq_Un_Diff even_card_Un_Diff)
qed

lemma fst_xor_chain_iff:
  "fst ((xor_chain y1 y2) e) = (fst (y1 e) \<noteq> fst (y2 e))"
  by (cases "y1 e"; cases "y2 e") (simp add: xor_chain.simps)

lemma snd_xor_chain_iff:
  "snd ((xor_chain y1 y2) e) = (snd (y1 e) \<noteq> snd (y2 e))"
  by (cases "y1 e"; cases "y2 e") (simp add: xor_chain.simps)

lemma even_card_Collect_neq:
  assumes "finite U"
  shows
    "even (card {x \<in> U. P x \<noteq> Q x}) =
     (even (card {x \<in> U. P x}) = even (card {x \<in> U. Q x}))"
proof -
  let ?A = "{x \<in> U. P x}"
  let ?B = "{x \<in> U. Q x}"
  have finA: "finite ?A" and finB: "finite ?B"
    using assms by auto
  have "{x \<in> U. P x \<noteq> Q x} = sym_diff ?A ?B"
    by (auto simp: sym_diff_def)
  with finA finB show ?thesis
    by (simp add: even_card_sym_diff)
qed


(* Finite support for chains on finite edge sets *)
lemma finite_support:
  assumes "support y <= E G"
  shows "finite (support y)"
  using assms finE by (rule finite_subset)

(* Mask a chain to E G *)
definition mask_on_E :: "('e chain) => ('e chain)" where
  "mask_on_E y = (\<lambda>e. if e : E G then y e else (False, False))"

(* Masking preserves zero_chain *)
lemma mask_zero: "mask_on_E zero_chain = zero_chain"
  unfolding mask_on_E_def zero_chain_def by simp

(* Support of masked chain is subset of E G *)
lemma support_mask_subset: "support (mask_on_E y) <= E G"
  unfolding support_def mask_on_E_def by auto

(* Chains equal on E G have equal masks *)
lemma mask_eq_on_E:
  assumes "ALL e : E G. y e = z e"
  shows "mask_on_E y = mask_on_E z"
  using assms unfolding mask_on_E_def by auto

end

end
