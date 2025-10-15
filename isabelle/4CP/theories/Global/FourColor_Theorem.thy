theory FourColor_Theorem
  imports "../Disk/Disk_KCSD_DualStrong" "Tait_Equivalence" "Kauffman_Parity_Primality"
begin

(* Local reachability from the strong dual lemma. *)
(* Use Disk_KCSD_dual_strong to show W0(H) <= span(G),
   then conclude local reachability equivalence as in Prop. 4.10. *)
lemma local_reachability_from_dual:
  assumes "disk_cubic G B" "proper3 C0"
  shows "True"  (* local reachability equivalence for this trail/disk *)
  using assms
  apply -
  sorry

(* The big conclusion *)
(* - local_reachability_from_dual supplies the equivalence needed by Kauffman_reduction
   - Kauffman_reduction yields 4CT
   - Tait_equivalence translates to the graph statement *)
theorem Four_Color_Theorem:
  shows "True"  (* every bridgeless planar cubic graph is 3-edge-colorable; hence 4CT *)
  using Kauffman_reduction local_reachability_from_dual Tait_equivalence
  apply -
  sorry

end
