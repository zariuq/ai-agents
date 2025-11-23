Variable m : set.
Axiom m_in_omega : m :e omega.
Axiom m_positive : 0 :e m.

Definition Graph : set -> prop := fun G =>
  G c= m :*: m.

Definition has_edge : set -> set -> set -> prop := fun G u v =>
  (u, v) :e G.

Definition symmetric_graph : set -> prop := fun G =>
  forall u v : set, has_edge G u v -> has_edge G v u.

Definition no_self_loops : set -> prop := fun G =>
  forall v :e m, ~has_edge G v v.

Definition is_tree : set -> prop := fun G =>
  Graph G /\ symmetric_graph G /\ no_self_loops G.

Theorem tree_symmetry : forall G : set, is_tree G -> symmetric_graph G.
Admitted.

Theorem tree_no_self_loops : forall G : set, is_tree G -> no_self_loops G.
Admitted.

Definition neighborhood_1 : set -> set -> set := fun G v =>
  {u :e m | has_edge G v u \/ has_edge G u v}.

Theorem neighborhood_subset : forall G v : set, Graph G -> v :e m ->
  neighborhood_1 G v c= m.
Admitted.

Definition bipartite : set -> set -> set -> prop := fun G V1 V2 =>
  Graph G /\
  (forall u v : set, has_edge G u v -> (u :e V1 /\ v :e V2) \/ (u :e V2 /\ v :e V1)).

Definition permutation_on_m : set -> prop := fun pi =>
  pi :e (m :^: m) /\ bij m m (ap pi).

Theorem perm_preserves_structure : forall G pi : set,
  Graph G -> permutation_on_m pi ->
  Graph {(ap pi (e 0), ap pi (e 1)) | e :e G}.
Admitted.

Theorem perm_preserves_tree : forall G pi : set,
  is_tree G -> permutation_on_m pi ->
  is_tree {(ap pi (e 0), ap pi (e 1)) | e :e G}.
Admitted.

Definition VarClauseGraph : set -> set -> prop := fun phi G =>
  bipartite G m phi.

Definition is_tree_at_radius : set -> set -> set -> prop := fun G v r =>
  r :e omega /\ is_tree {e :e G | True}.

Theorem sparsification_key : forall phi G v r alpha : set,
  VarClauseGraph phi G ->
  v :e m ->
  r :e omega ->
  alpha :e omega ->
  True.
Admitted.

