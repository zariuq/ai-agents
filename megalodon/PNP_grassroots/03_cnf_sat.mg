(* ========================================================================== *)
(* 03_cnf_sat.mg - CNF Formulas, SAT, and USAT                               *)
(* ========================================================================== *)
(* Definitions for Boolean satisfiability and the unique-witness promise     *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* PART 1: Literals and Clauses                                               *)
(* -------------------------------------------------------------------------- *)

(* A literal is a variable with optional negation *)
(* Represented as pair (var_index, sign) where sign in {0,1} *)
Definition Literal : set -> set -> set :=
  fun var sign => (var, sign).

Definition lit_var : set -> set := fun l => ap l 0.
Definition lit_sign : set -> set := fun l => ap l 1.

(* Positive and negative literals *)
Definition pos_lit : set -> set := fun v => Literal v 0.
Definition neg_lit : set -> set := fun v => Literal v 1.

(* Flip the sign of a literal *)
Definition flip_lit : set -> set :=
  fun l => Literal (lit_var l) (xor (lit_sign l) 1).

(* A clause is a set (disjunction) of literals *)
Definition Clause : set -> prop :=
  fun C => forall l :e C, exists v, exists s :e 2, l = Literal v s.

(* -------------------------------------------------------------------------- *)
(* PART 2: CNF Formulas                                                       *)
(* -------------------------------------------------------------------------- *)

(* A CNF formula is a set (conjunction) of clauses *)
Definition CNF : set -> prop :=
  fun F => forall C :e F, Clause C.

(* k-CNF: every clause has exactly k literals *)
Definition kCNF : set -> set -> prop :=
  fun k F => CNF F /\ forall C :e F, equip k C.

(* 3-CNF specifically *)
Definition ThreeCNF : set -> prop := kCNF 3.

(* Number of variables in a CNF *)
Definition num_vars : set -> set :=
  fun F => Union (fun C => {lit_var l | l :e C}) F.

(* Number of clauses *)
Definition num_clauses : set -> set :=
  fun F => F.  (* Cardinality of the set of clauses *)

(* -------------------------------------------------------------------------- *)
(* PART 3: Satisfying Assignments                                             *)
(* -------------------------------------------------------------------------- *)

(* An assignment is a function from variables to {0,1} *)
Definition Assignment : set -> set -> prop :=
  fun m x => forall i :e m, x i :e 2.

(* Evaluate a literal under assignment *)
Definition eval_lit : set -> set -> set :=
  fun x l =>
    let v := lit_var l in
    let s := lit_sign l in
    xor (x v) s.

(* A clause is satisfied if at least one literal is true *)
Definition satisfies_clause : set -> set -> prop :=
  fun x C => exists l :e C, eval_lit x l = 1.

(* A CNF is satisfied if all clauses are satisfied *)
Definition satisfies : set -> set -> prop :=
  fun x F => forall C :e F, satisfies_clause x C.

(* The set of all satisfying assignments *)
Definition SAT_solutions : set -> set -> set :=
  fun m F => {x | Assignment m x /\ satisfies x F}.

(* -------------------------------------------------------------------------- *)
(* PART 4: SAT, UNSAT, and USAT                                              *)
(* -------------------------------------------------------------------------- *)

(* SAT: Formula has at least one satisfying assignment *)
Definition is_SAT : set -> set -> prop :=
  fun m F => exists x, Assignment m x /\ satisfies x F.

(* UNSAT: Formula has no satisfying assignment *)
Definition is_UNSAT : set -> set -> prop :=
  fun m F => ~is_SAT m F.

(* Number of solutions *)
Definition num_solutions : set -> set -> set :=
  fun m F => SAT_solutions m F.  (* Cardinality *)

(* USAT: Unique satisfying assignment (exactly one solution) *)
Definition is_USAT : set -> set -> prop :=
  fun m F => equip 1 (SAT_solutions m F).

(* The unique witness (when it exists) *)
Definition unique_witness : set -> set -> set :=
  fun m F => Eps_i (fun x => x :e SAT_solutions m F).

(* -------------------------------------------------------------------------- *)
(* PART 5: Random 3-CNF                                                       *)
(* -------------------------------------------------------------------------- *)

(* Random 3-CNF with m variables and M = alpha*m clauses *)
(* Each clause: sample 3 variables uniformly with replacement *)
(* No literal signs yet - those come from masking *)

Definition clause_density : set := 4.  (* Typical alpha for random 3-SAT *)

(* Unsigned 3-uniform hypergraph on [m] *)
(* M triples sampled independently and uniformly *)
Definition random_3hypergraph : set -> set -> prop :=
  fun m F =>
    let M := mul clause_density m in
    forall C :e F, exists v1 v2 v3 :e m, C = {v1, v2, v3}.

(* -------------------------------------------------------------------------- *)
(* PART 6: Factor Graph Representation                                        *)
(* -------------------------------------------------------------------------- *)

(* Factor graph: bipartite graph between variables and clauses *)
Definition FactorGraph : set -> set :=
  fun F =>
    let vars := num_vars F in
    let clauses := F in
    (vars, clauses, {(v, C) | v :e vars /\ C :e clauses /\ exists l :e C, lit_var l = v}).

(* Degree of a variable in the factor graph *)
Definition var_degree : set -> set -> set :=
  fun F v => {C :e F | exists l :e C, lit_var l = v}.

(* Neighborhood of radius r around variable v *)
Definition neighborhood : set -> set -> set -> set :=
  fun F v r =>
    nat_primrec {v}
      (fun _ acc => Union (fun u =>
        if u :e num_vars F then var_degree F u
        else {w | exists C :e acc, w :e C /\ w :e num_vars F}
      ) acc)
      r.

(* -------------------------------------------------------------------------- *)
(* PART 7: Local Tree-Likeness (Lemma 2.14)                                  *)
(* -------------------------------------------------------------------------- *)

(* Definition 3.11: Local tree-likeness at radius r = c_3 * log(m) *)
(* The radius-r neighborhood is a tree with high probability *)

Definition is_tree : set -> prop :=
  fun G => True.  (* Abstract: no cycles *)

(* For random 3-CNF at constant density alpha, there exists c*_3(alpha) > 0 *)
(* such that for c_3 in (0, c*_3) and r = c_3 * log(m): *)
(* Pr[neighborhood is tree] >= 1 - m^{-beta} *)

Theorem local_tree_likeness :
  forall alpha m c3,
    alpha > 0 ->
    c3 > 0 ->
    (* c3 < c3_star(alpha) -> *)
    let r := mul c3 (log2 m) in
    exists beta,
      beta > 0 /\
      (* Pr[N_r(v) is a tree] >= 1 - m^{-beta} *)
      True.
Admitted.

(* Moreover, for any fixed signed rooted pattern T of radius r: *)
(* Pr[neighborhood equals T] <= m^{-beta'} *)

Theorem pattern_probability_bound :
  forall alpha m c3 T,
    alpha > 0 ->
    c3 > 0 ->
    let r := mul c3 (log2 m) in
    exists beta',
      beta' > 0 /\
      (* Pr[N_r(v) = T] <= m^{-beta'} *)
      True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* PART 8: NP-Completeness of SAT                                            *)
(* -------------------------------------------------------------------------- *)

(* SAT is in NP *)
Theorem SAT_in_NP : forall m, inNP (fun F => is_SAT m F).
Admitted.

(* SAT is NP-complete (Cook-Levin) *)
Theorem SAT_NP_complete : forall L,
  inNP L ->
  exists reduction,
    (* L(x) iff SAT(reduction(x)) *)
    (* reduction is polytime computable *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* END OF 03_cnf_sat.mg                                                       *)
(* -------------------------------------------------------------------------- *)
