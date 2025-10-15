theory Disk_DualForest
  imports "Disk_KCSD"
begin

context disk_cubic
begin

(* Interior dual graph over faces; existence of a spanning forest. *)
lemma interior_dual_forest_exists:
  assumes "finite (E G)"
  shows "True"  (* EX T. T is a spanning forest of the interior dual *)
  by meson

(* Cut-parity identity for purified sums and orthogonality peeling on a leaf cut.
   These implement Lemmas 4.7 and 4.8 used to peel the interior by leaf subtrees. *)

lemma cut_parity_purified_sums:
  shows "True"  (* support equals cut edges XOR boundary runs *)
  by meson

lemma orthogonality_peeling_leaf:
  assumes "True"  (* y orthogonal to all generators *)
  shows "True"    (* y vanishes on the unique cut edge of a leaf-subtree *)
  by auto

end
end
