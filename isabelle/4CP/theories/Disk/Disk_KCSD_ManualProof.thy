theory Disk_KCSD_ManualProof
  imports "Disk_KCSD"
begin

(* ========================================================================= *)
(* MANUAL PROOFS FOR XOR CHAIN ALGEBRAIC PROPERTIES                        *)
(* ========================================================================= *)
(*
  Goal: Prove xor_chain commutativity and associativity manually
  using explicit case analysis to avoid the let-binding issue.

  Key insight: Need Boolean algebra helper lemmas first!
*)

(* CRITICAL HELPER LEMMA: XOR symmetry at Boolean level *)
lemma bool_xor_comm: "(a::bool) = (\<not> b) \<longleftrightarrow> b = (\<not> a)"
  by auto

lemma bool_neq_comm: "(a::bool) \<noteq> b \<longleftrightarrow> b \<noteq> a"
  by auto

(* Helper: Product pair XOR commutativity *)
lemma prod_xor_comm:
  fixes p q :: "bool \<times> bool"
  shows "(case p of (a1,b1) \<Rightarrow> case q of (a2,b2) \<Rightarrow> (a1 \<noteq> a2, b1 \<noteq> b2)) =
         (case q of (a2,b2) \<Rightarrow> case p of (a1,b1) \<Rightarrow> (a2 \<noteq> a1, b2 \<noteq> b1))"
  by (cases p; cases q) (simp add: bool_neq_comm)

(* NOW TRY: xor_chain commutativity with helper lemmas *)
lemma xor_chain_comm_with_helpers:
  "xor_chain f g = xor_chain g f"
proof (rule ext)
  fix x
  show "xor_chain f g x = xor_chain g f x"
    unfolding xor_chain.simps
    apply (simp add: Let_def split: prod.split)
    using bool_neq_comm by auto
qed

(* Alternative: Direct proof with case expansion and helper *)
lemma xor_chain_comm_case_expand:
  "xor_chain f g = xor_chain g f"
  by (rule ext) (simp add: Let_def bool_neq_comm split: prod.split)

(* Associativity - will also need helpers *)
lemma bool_xor_assoc:
  "((a::bool) \<noteq> b) \<noteq> c \<longleftrightarrow> a \<noteq> (b \<noteq> c)"
  by auto

lemma xor_chain_assoc_with_helpers:
  "xor_chain (xor_chain f g) h = xor_chain f (xor_chain g h)"
proof (rule ext)
  fix x
  show "xor_chain (xor_chain f g) h x = xor_chain f (xor_chain g h) x"
    unfolding xor_chain.simps
    apply (simp add: Let_def split: prod.split)
    using bool_xor_assoc by auto
qed

(* Clean version for actual use *)
lemma xor_chain_comm: "xor_chain f g = xor_chain g f"
  by (rule ext) (simp add: Let_def bool_neq_comm split: prod.split)

lemma xor_chain_assoc: "xor_chain (xor_chain f g) h = xor_chain f (xor_chain g h)"
  by (rule ext) (simp add: Let_def bool_xor_assoc split: prod.split)

(*
  KEY INSIGHT FOR DOCUMENTATION:

  The automation failed because Isabelle's simplifier didn't have:
  - bool_neq_comm: (a ≠ b) = (b ≠ a)
  - bool_xor_assoc: ((a ≠ b) ≠ c) = (a ≠ (b ≠ c))

  These are trivial Boolean algebra facts (`by auto`), but they needed to be
  stated explicitly before the xor_chain lemmas could be proven!

  Once we add these simple helpers, the proofs become one-liners.
*)

end
