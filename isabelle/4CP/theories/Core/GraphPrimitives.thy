theory GraphPrimitives
  imports Main
begin

(* Colors over GF(2)^2 as pairs of bools. *)
type_synonym col = "bool * bool"

fun dot2 :: "col => col => bool" where
  "dot2 (a1,b1) (a2,b2) = ((a1 & a2) ~= (b1 & b2))"

lemma dot2_nondegenerate:
  assumes "u ~= (False, False)"
  shows "EX v. dot2 u v"
proof -
  obtain u1 u2 where [simp]: "u = (u1,u2)" by (cases u) auto
  show ?thesis
  proof (cases u1)
    case True  (* take v = (True,False) *)
    then show ?thesis by (intro exI[of _ "(True,False)"]) simp
  next
    case False
    with assms have u2 by auto
    thus ?thesis by (intro exI[of _ "(False,True)"]) simp
  qed
qed

(* A light graph record: vertices, edges, and an incidence map. *)
record ('v,'e) graph =
  V :: "'v set"
  E :: "'e set"
  ends :: "'e => 'v * 'v"

(* Chains: functions from edges to GF(2)^2 *)
type_synonym 'e chain = "'e => col"

(* Simple chain operations - these will be connected to xor_space later *)
definition zero_chain :: "'e chain" where
  "zero_chain = (\<lambda>e. (False, False))"

(* Chain span - placeholder for now, will be defined properly *)
consts chain_span :: "'e chain set => 'e chain set"

(* Placeholder lemmas for glue - these assert the XOR linearity properties *)
axiomatization where
  chain_span_mono: "S <= T ==> chain_span S <= chain_span T"
and
  chain_orth_propagates:
    "ALL s : S. P s ==> ALL w : chain_span S. P w"

end
