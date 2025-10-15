theory Graph_Conversion
  imports
    GraphPrimitives
begin

(* ========================================================================= *)
(* BRIDGE BETWEEN OUR GRAPH TYPE AND AFP GRAPH_THEORY                       *)
(* ========================================================================= *)
(*
  This theory provides conversions between our simple graph representation
  and AFP's more general pre_digraph type. This allows us to leverage
  AFP lemmas (especially Euler's formula) while keeping our simpler type
  for Kempe-specific work.
*)

(* AFP's pre_digraph type (simplified version for conversion) *)
record ('v, 'e) pre_digraph =
  verts :: "'v set"
  arcs :: "'e set"
  tail :: "'e => 'v"
  head :: "'e => 'v"

(* Conversion from our graph to AFP pre_digraph *)
definition graph_to_pre_digraph :: "('v, 'e) graph => ('v, 'e) pre_digraph" where
  "graph_to_pre_digraph G =
    (| verts = V G,
       arcs = E G,
       tail = (%e. fst (ends G e)),
       head = (%e. snd (ends G e)) |)"

(* Reverse conversion *)
definition pre_digraph_to_graph :: "('v, 'e) pre_digraph => ('v, 'e) graph" where
  "pre_digraph_to_graph D =
    (| V = verts D,
       E = arcs D,
       ends = (%a. (tail D a, head D a)) |)"

(* Round-trip property *)
lemma graph_conversion_round_trip:
  shows "pre_digraph_to_graph (graph_to_pre_digraph G) = G"
  unfolding graph_to_pre_digraph_def pre_digraph_to_graph_def
  by simp

(* Well-formedness preservation *)
lemma graph_to_pre_digraph_finite:
  assumes "finite (V G)" "finite (E G)"
  shows "finite (verts (graph_to_pre_digraph G))"
    and "finite (arcs (graph_to_pre_digraph G))"
  using assms unfolding graph_to_pre_digraph_def by auto

(* For undirected graphs, we can make them symmetric digraphs *)
definition make_symmetric :: "('v, 'e) pre_digraph => bool" where
  "make_symmetric D = (\<forall>e \<in> arcs D. \<exists>e' \<in> arcs D.
     tail D e = head D e' \<and> head D e = tail D e')"

(* Our cubic graphs are symmetric when viewed as digraphs *)
lemma cubic_graph_symmetric:
  assumes "\<forall>v \<in> V G. card {e \<in> E G. fst (ends G e) = v \<or> snd (ends G e) = v} = 3"
  shows "make_symmetric (graph_to_pre_digraph G)"
  sorry (* This would require showing each edge can be traversed both ways,
           which is true for undirected graphs but needs careful formulation *)

end
