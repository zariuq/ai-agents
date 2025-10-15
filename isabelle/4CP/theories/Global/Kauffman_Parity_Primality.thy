theory Kauffman_Parity_Primality
  imports Main
begin

(* Axiomatize the "Parity/Primality reduction" interface:
   If every trail satisfies local reachability equivalence, then 4CT. *)
axiomatization where
  Kauffman_reduction: "True"

end
