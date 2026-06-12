Theory metta_m1_bridge_eval_sound
Ancestors
  metta_m1_cake_bridge metta_m1
Libs
  preamble

Definition bridge_evaluator_core_payload_atom_def:
  bridge_evaluator_core_payload_atom atom <=>
    bridge_supported_or_fallback_payload_atom atom
End

Definition bridge_evaluator_core_payload_result_def:
  bridge_evaluator_core_payload_result fuel space atom out <=>
    bridge_supported_or_split_fallback_payload_result fuel space atom out
End

Theorem bridge_evaluator_core_payload_atom_return_example:
  bridge_evaluator_core_payload_atom
    (metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 8])
Proof
  rw[bridge_evaluator_core_payload_atom_def,
     bridge_supported_or_fallback_payload_atom_def,
     bridge_supported_branch_payload_atom_def,
     bridge_control_payload_supported_atom_def] \\
  qexists_tac ‘metta_m1$Sym 8’ \\
  rw[]
QED

Theorem bridge_evaluator_core_payload_atom_add_negative_example:
  ~bridge_evaluator_core_payload_atom
    (metta_m1$Expr
      [metta_m1$Sym 11; metta_m1$IntLit 1; metta_m1$IntLit 2])
Proof
  rw[bridge_evaluator_core_payload_atom_def,
     bridge_supported_or_fallback_payload_atom_def,
     bridge_supported_branch_payload_atom_def,
     bridge_control_payload_supported_atom_def,
     bridge_nested_payload_supported_atom_def,
     bridge_fallback_payload_supported_atom_def,
     eval_m1_rec_proven_branch_atom_def]
QED

Theorem bridge_eval_m1_rec_evaluator_core_payload_sound:
  !fuel space atom out.
    bridge_evaluator_core_payload_atom atom /\
    MEM out (eval_m1_rec (SUC fuel) space atom) ==>
    eval_m1_rec_result_sound (SUC fuel) space atom out /\
    eval_m1_rec_family_sound (SUC fuel) space atom out /\
    bridge_evaluator_core_payload_result fuel space atom out
Proof
  rw[bridge_evaluator_core_payload_atom_def,
     bridge_evaluator_core_payload_result_def] \\
  metis_tac[bridge_eval_m1_rec_supported_or_split_fallback_fuller_sound]
QED

Definition bridge_primitive_payload_atom_def:
  bridge_primitive_payload_atom atom <=>
    eval_m1_rec_arith_compare_atom atom \/
    eval_m1_rec_boolean_atom atom
End

Definition bridge_primitive_payload_result_def:
  bridge_primitive_payload_result fuel space atom out <=>
    (eval_m1_rec_arith_compare_atom atom /\
     eval_m1_rec_arith_compare_sound fuel space atom out) \/
    (eval_m1_rec_boolean_atom atom /\
     eval_m1_rec_boolean_sound fuel space atom out)
End

Theorem bridge_primitive_payload_atom_add_example:
  bridge_primitive_payload_atom
    (metta_m1$Expr
      [metta_m1$Sym 11; metta_m1$IntLit 1; metta_m1$IntLit 2])
Proof
  rw[bridge_primitive_payload_atom_def,
     eval_m1_rec_arith_compare_atom_def]
QED

Theorem bridge_primitive_payload_atom_return_negative_example:
  ~bridge_primitive_payload_atom
    (metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 8])
Proof
  rw[bridge_primitive_payload_atom_def,
     eval_m1_rec_arith_compare_atom_def,
     eval_m1_rec_boolean_atom_def]
QED

Theorem bridge_eval_m1_rec_primitive_payload_sound:
  !fuel space atom out.
    bridge_primitive_payload_atom atom /\
    MEM out (eval_m1_rec (SUC fuel) space atom) ==>
    eval_m1_rec_result_sound (SUC fuel) space atom out /\
    eval_m1_rec_family_sound (SUC fuel) space atom out /\
    bridge_primitive_payload_result fuel space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  fs[bridge_primitive_payload_atom_def] >- (
    rw[bridge_primitive_payload_result_def] \\
    metis_tac[eval_m1_rec_arith_compare_input_sound]) \\
  rw[bridge_primitive_payload_result_def] \\
  metis_tac[eval_m1_rec_boolean_input_sound]
QED

Definition bridge_evaluator_payload_atom_def:
  bridge_evaluator_payload_atom atom <=>
    bridge_evaluator_core_payload_atom atom \/
    bridge_primitive_payload_atom atom
End

Definition bridge_evaluator_payload_result_def:
  bridge_evaluator_payload_result fuel space atom out <=>
    (bridge_evaluator_core_payload_atom atom /\
     bridge_evaluator_core_payload_result fuel space atom out) \/
    (bridge_primitive_payload_atom atom /\
     bridge_primitive_payload_result fuel space atom out)
End

Theorem bridge_evaluator_payload_atom_return_example:
  bridge_evaluator_payload_atom
    (metta_m1$Expr [metta_m1$Sym 19; metta_m1$Sym 8])
Proof
  rw[bridge_evaluator_payload_atom_def,
     bridge_evaluator_core_payload_atom_return_example]
QED

Theorem bridge_evaluator_payload_atom_add_example:
  bridge_evaluator_payload_atom
    (metta_m1$Expr
      [metta_m1$Sym 11; metta_m1$IntLit 1; metta_m1$IntLit 2])
Proof
  rw[bridge_evaluator_payload_atom_def,
     bridge_primitive_payload_atom_add_example]
QED

Theorem bridge_eval_m1_rec_evaluator_payload_sound:
  !fuel space atom out.
    bridge_evaluator_payload_atom atom /\
    MEM out (eval_m1_rec (SUC fuel) space atom) ==>
    eval_m1_rec_result_sound (SUC fuel) space atom out /\
    eval_m1_rec_family_sound (SUC fuel) space atom out /\
    bridge_evaluator_payload_result fuel space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  fs[bridge_evaluator_payload_atom_def] >- (
    drule bridge_eval_m1_rec_evaluator_core_payload_sound \\
    rw[bridge_evaluator_payload_result_def]) \\
  drule bridge_eval_m1_rec_primitive_payload_sound \\
  rw[bridge_evaluator_payload_result_def]
QED

Definition bridge_model_evaluator_payload_atom_def:
  bridge_model_evaluator_payload_atom atom <=>
    eval_m1_rec_family_atom atom \/
    bridge_fallback_payload_supported_atom atom
End

Definition bridge_model_evaluator_payload_result_def:
  bridge_model_evaluator_payload_result fuel space atom out <=>
    (eval_m1_rec_family_atom atom /\
     eval_m1_rec_family_sound (SUC fuel) space atom out) \/
    (bridge_fallback_payload_supported_atom atom /\
     bridge_fallback_payload_result fuel space atom out /\
     bridge_split_fallback_payload_result space atom out)
End

Theorem bridge_model_evaluator_payload_atom_total:
  !atom. bridge_model_evaluator_payload_atom atom
Proof
  rw[bridge_model_evaluator_payload_atom_def,
     bridge_fallback_payload_supported_atom_def] \\
  metis_tac[eval_m1_rec_family_atom_iff_proven_branch]
QED

Theorem bridge_model_evaluator_payload_atom_no_negative_example:
  ~(?atom. ~bridge_model_evaluator_payload_atom atom)
Proof
  metis_tac[bridge_model_evaluator_payload_atom_total]
QED

Theorem bridge_eval_m1_rec_model_evaluator_payload_sound:
  !fuel space atom out.
    bridge_model_evaluator_payload_atom atom /\
    MEM out (eval_m1_rec (SUC fuel) space atom) ==>
    eval_m1_rec_result_sound (SUC fuel) space atom out /\
    eval_m1_rec_family_sound (SUC fuel) space atom out /\
    bridge_model_evaluator_payload_result fuel space atom out
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac >-
    metis_tac[eval_m1_rec_result_sound] \\
  conj_tac >-
    metis_tac[eval_m1_rec_family_result_sound] \\
  fs[bridge_model_evaluator_payload_atom_def] >- (
    simp[Once bridge_model_evaluator_payload_result_def] \\
    disj1_tac \\
    metis_tac[eval_m1_rec_family_result_sound]) \\
  simp[Once bridge_model_evaluator_payload_result_def] \\
  disj2_tac \\
  metis_tac[bridge_eval_m1_rec_split_fallback_fuller_sound]
QED

val _ = export_theory();
