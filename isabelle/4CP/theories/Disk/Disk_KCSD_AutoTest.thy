theory Disk_KCSD_AutoTest
  imports "Disk_KCSD"
begin

(* ========================================================================= *)
(* TESTING AUTOMATED PROOF METHODS ON XOR CHAIN LEMMAS                     *)
(* ========================================================================= *)
(*
  Goal: Try various automated proof methods on our algebraic lemmas.

  NOTE: xor_chain is defined as 'fun' so use xor_chain.simps not xor_chain_def
*)

(* Test 1: XOR chain commutativity - attempt with auto *)
lemma xor_chain_comm_attempt1: "xor_chain f g = xor_chain g f"
  by (rule ext) auto
  (* Result: Will see if auto can handle the let-binding expansion *)

(* Test 2: XOR chain commutativity - attempt with force *)
lemma xor_chain_comm_attempt2: "xor_chain f g = xor_chain g f"
  by (rule ext) force

(* Test 3: XOR chain commutativity - attempt with case splitting *)
lemma xor_chain_comm_attempt3: "xor_chain f g = xor_chain g f"
  by (rule ext) (auto split: prod.splits)

(* Test 4: XOR chain commutativity - attempt with fastforce *)
lemma xor_chain_comm_attempt4: "xor_chain f g = xor_chain g f"
  by (rule ext) fastforce

(* Test 5: XOR chain commutativity - attempt with blast *)
lemma xor_chain_comm_attempt5: "xor_chain f g = xor_chain g f"
  by (rule ext) blast

(* Test 6: XOR chain associativity - attempt with auto *)
lemma xor_chain_assoc_attempt1:
  "xor_chain (xor_chain f g) h = xor_chain f (xor_chain g h)"
  by (rule ext) auto

(* Test 7: Simple Boolean test - should succeed *)
lemma bool_sym_test: "(a::bool) = b \<longleftrightarrow> b = a"
  by auto

(* Test 8: XOR Boolean level *)
lemma xor_bool_comm: "(a \<noteq> b) = (b \<noteq> (a::bool))"
  by auto

end
