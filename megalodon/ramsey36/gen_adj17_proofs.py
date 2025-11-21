#!/usr/bin/env python3
"""Generate Megalodon proofs for Adj17 edge theorems, Adj17_sym, and Adj17_triangle_free.

The Adj17 definition is a 17-way left-associative disjunction:
  ((((P0 \/ P1) \/ P2) \/ ...) \/ P16)

This script generates:
1. Edge theorems (Adj17_i_j)
2. Distinctness Axioms (neq_i_j) for i < j (skipping (0,1), (0,2), (1,2) in preamble)
3. Adj17_sym (Symmetry)
4. Adj17_triangle_free (Clique number < 3)
"""

# Adjacency list for the 17-vertex Graver-Yackel graph
adj = {
    0: [9, 14, 15, 16],
    1: [7, 11, 13, 16],
    2: [8, 10, 12, 15],
    3: [6, 8, 13, 15, 16],
    4: [5, 7, 12, 14, 16],
    5: [4, 9, 10, 11, 13],
    6: [3, 10, 11, 12, 14],
    7: [1, 4, 9, 10, 15],
    8: [2, 3, 9, 11, 14],
    9: [0, 5, 7, 8, 12],
    10: [2, 5, 6, 7, 16],
    11: [1, 5, 6, 8, 15],
    12: [2, 4, 6, 9, 13],
    13: [1, 3, 5, 12, 14],
    14: [0, 4, 6, 8, 13],
    15: [0, 2, 3, 7, 11],
    16: [0, 1, 3, 4, 10],
}

def gen_vertex_clause(v, i_var="i", j_var="j"):
    """Generate the clause for a single vertex v."""
    neighbors = adj[v]
    neighbor_disj = r" \/ ".join(f"{j_var} = {n}" for n in neighbors)
    return f"({i_var} = {v} /\\ ({neighbor_disj}))"

def gen_partial_def(vertices, i_var="i", j_var="j"):
    """Generate the disjunction for a subset of vertices."""
    clauses = [gen_vertex_clause(v, i_var, j_var) for v in vertices]
    return r" \/ ".join(clauses)

def gen_vertex_navigation(vertex):
    """Generate orIL/orIR to navigate to vertex's clause."""
    if vertex == 16:
        return "apply orIR."
    elif vertex == 0:
        return "apply orIL. " * 16
    else:
        n_orIL = 16 - vertex
        return "apply orIL. " * n_orIL + "apply orIR."

def gen_neighbor_navigation(neighbors, target):
    """Generate orIL/orIR to navigate to target neighbor in list."""
    n = len(neighbors)
    idx = neighbors.index(target)
    n_orIL = n - 1 - idx

    if n_orIL == 0:
        return "apply orIR. reflexivity."
    elif idx == 0:
        return "apply orIL. " * n_orIL + "reflexivity."
    else:
        return "apply orIL. " * n_orIL + "apply orIR. reflexivity."

def gen_edge_theorem(i, j):
    """Generate a complete theorem proving Adj17 i j."""
    lines = []
    lines.append(f"Theorem Adj17_{i}_{j} : Adj17 {i} {j}.")
    lines.append(f"prove {gen_partial_def(list(range(17)), i_var=str(i), j_var=str(j))}.")
    lines.append(gen_vertex_navigation(i))
    lines.append("apply andI.")
    lines.append("- reflexivity.")
    lines.append(f"- {gen_neighbor_navigation(adj[i], j)}")
    lines.append("Qed.")
    return "\n".join(lines)

def gen_all_edge_theorems():
    """Generate all 68 directed edge theorems."""
    theorems = []
    for i in range(17):
        for j in adj[i]:
            theorems.append(gen_edge_theorem(i, j))
    return "\n\n".join(theorems)

def indent(text, prefix="  "):
    """Indent a block of text."""
    return "\n".join(prefix + line for line in text.splitlines())

# --- Adj17_sym Generator ---

def gen_recursive_neighbor_step(neighbors, v, hyp_name, i_var, j_var):
    """Recursively generate proof steps for neighbor disjunction."""
    lines = []
    left_subset = neighbors[:-1]
    left_pat = r" \/ ".join(f"{j_var} = {n}" for n in left_subset)
    lines.append(f"- assume HL: {left_pat}.")
    if len(left_subset) > 1:
        lines.append(f"  apply HL.")
        lines.append(indent(gen_recursive_neighbor_step(left_subset, v, "HL", i_var, j_var), "  "))
    else:
        n = left_subset[0]
        lines.append(f"  rewrite H{i_var}. rewrite HL.")
        lines.append(f"  exact Adj17_{n}_{v}.")
    right_n = neighbors[-1]
    lines.append(f"- assume HR: {j_var} = {right_n}.")
    lines.append(f"  rewrite H{i_var}. rewrite HR.")
    lines.append(f"  exact Adj17_{right_n}_{v}.")
    return "\n".join(lines)

def gen_vertex_case_body(v, hyp_name, i_var, j_var):
    """Generate the body of the proof for a specific vertex case."""
    lines = []
    lines.append(f"apply {hyp_name}.")
    lines.append(f"assume H{i_var}: {i_var} = {v}.")
    neighbor_disj = r" \/ ".join(f"{j_var} = {n}" for n in adj[v])
    lines.append(f"assume H_neighbors: {neighbor_disj}.")
    lines.append(f"apply H_neighbors.")
    lines.append(gen_recursive_neighbor_step(adj[v], v, "H_neighbors", i_var, j_var))
    return "\n".join(lines)

def gen_recursive_vertex_step(vertices, i_var, j_var):
    """Recursively generate proof steps for vertex disjunction."""
    k = vertices[-1]
    left_subset = vertices[:-1]
    lines = []
    left_def = gen_partial_def(left_subset, i_var, j_var)
    lines.append(f"- assume HL: {left_def}.")
    if len(left_subset) > 1:
        lines.append(f"  apply HL.")
        lines.append(indent(gen_recursive_vertex_step(left_subset, i_var, j_var), "  "))
    else:
        lines.append(indent(gen_vertex_case_body(left_subset[0], "HL", i_var, j_var), "  "))
    right_def = gen_vertex_clause(k, i_var, j_var)
    lines.append(f"- assume HR: {right_def}.")
    lines.append(indent(gen_vertex_case_body(k, "HR", i_var, j_var), "  "))
    return "\n".join(lines)

def gen_adj17_sym():
    """Generate Adj17_sym using recursive disjunction elimination."""
    lines = []
    lines.append("Theorem Adj17_sym : forall u v : set, Adj17 u v -> Adj17 v u.")
    lines.append("let u v.")
    lines.append("assume H: Adj17 u v.")
    lines.append("prove Adj17 v u.")
    lines.append("apply H.")
    lines.append(gen_recursive_vertex_step(list(range(17)), "u", "v"))
    lines.append("Qed.")
    return "\n".join(lines)

# --- Distinctness Axioms ---

def gen_neq_lemmas():
    """Generate distinctness axioms for i, j in 0..16."""
    lines = []
    existing = {(0, 1), (0, 2), (1, 2)}
    for i in range(17):
        for j in range(i + 1, 17):
            if (i, j) in existing:
                continue
            lines.append(f"Axiom neq_{i}_{j} : {i} <> {j}.")
    return "\n".join(lines)

# --- Adj17_triangle_free Generator ---

def apply_neq(i, j):
    """Return proof step to contradict i = j."""
    if i == j:
        raise ValueError("Cannot contradict i = i")
    if i < j:
        return(f"apply neq_{i}_{j}.") 
    else:
        return(f"apply neq_{j}_{i}. symmetry.")

def gen_tf_z_case(z_val, k, x_val, hyp_name="Hz", hz_eq_name="Hz_eq"):
    """Refute Adj17 x_val z_val where z_val = k."""
    if k in adj[x_val]:
        return f"(* Error: Triangle found {x_val}-{z_val}-{k} *) prove False. exact FalseE."

    lines = []
    lines.append(f"apply {hyp_name}.")
    
    def rec_x_split(vertices):
        res = []
        last = vertices[-1]
        left = vertices[:-1]
        left_def = gen_partial_def(left, i_var="x", j_var="z")
        
        res.append(f"- assume HL: {left_def}.")
        if len(left) > 1:
            res.append(f"  apply HL.")
            res.append(indent(rec_x_split(left), "  "))
        else:
            v = left[0]
            res.append(indent(rec_x_body(v, "HL"), "  "))
        
        right_def = gen_vertex_clause(last, i_var="x", j_var="z")
        res.append(f"- assume HR: {right_def}.")
        res.append(indent(rec_x_body(last, "HR"), "  "))
        return "\n".join(res)

    def rec_x_body(v, h_name):
        res = []
        if v != x_val:
            res.append(f"apply {h_name}.")
            res.append(f"assume Hx: x = {v}.")
            res.append(f"assume _.")
            res.append(apply_neq(x_val, v))
            res.append(f"rewrite <- Hx_eq. exact Hx.")
        else:
            res.append(f"apply {h_name}.")
            res.append("assume _.")
            ns = adj[v]
            n_disj = r" \/ ".join(f"z = {n}" for n in ns)
            res.append(f"assume Hz_ns: {n_disj}.")
            res.append("apply Hz_ns.")
            res.append(rec_neigh_split(ns))
        return "\n".join(res)

    def rec_neigh_split(ns):
        res = []
        left = ns[:-1]
        left_pat = r" \/ ".join(f"z = {n}" for n in left)
        res.append(f"- assume HL: {left_pat}.")
        if len(left) > 1:
            res.append(f"  apply HL.")
            res.append(indent(rec_neigh_split(left), "  "))
        else:
            n = left[0]
            res.append(indent(rec_neigh_body(n, "HL"), "  "))
        
        n = ns[-1]
        res.append(f"- assume HR: z = {n}.")
        res.append(indent(rec_neigh_body(n, "HR"), "  "))
        return "\n".join(res)

    def rec_neigh_body(n, h_name):
        res = []
        res.append(apply_neq(k, n))
        res.append(f"rewrite <- {hz_eq_name}.")
        res.append(f"exact {h_name}.")
        return "\n".join(res)

    lines.append(rec_x_split(list(range(17))))
    return "\n".join(lines)


def gen_tf_y_body(y_val, x_val, hyp_y_n_name):
    """Body for y=y_val (inside x=x_val)."""
    lines = []
    lines.append("apply Hyz.")
    
    def rec_yz_split(vertices):
        res = []
        last = vertices[-1]
        left = vertices[:-1]
        left_def = gen_partial_def(left, i_var="y", j_var="z")
        
        res.append(f"- assume HL: {left_def}.")
        if len(left) > 1:
            res.append(f"  apply HL.")
            res.append(indent(rec_yz_split(left), "  "))
        else:
            v = left[0]
            res.append(indent(rec_yz_body(v, "HL"), "  "))
            
        right_def = gen_vertex_clause(last, i_var="y", j_var="z")
        res.append(f"- assume HR: {right_def}.")
        res.append(indent(rec_yz_body(last, "HR"), "  "))
        return "\n".join(res)

    def rec_yz_body(v, h_name):
        res = []
        if v != y_val:
            res.append(f"apply {h_name}.")
            res.append(f"assume Hy_v: y = {v}.")
            res.append(f"assume _.")
            res.append(apply_neq(y_val, v))
            res.append(f"rewrite <- {hyp_y_n_name}.")
            res.append("exact Hy_v.")
        else:
            res.append(f"apply {h_name}.")
            res.append("assume _.")
            ns = adj[v]
            n_disj = r" \/ ".join(f"z = {n}" for n in ns)
            res.append(f"assume Hz_ns: {n_disj}.")
            res.append("apply Hz_ns.")
            res.append(rec_z_neigh_split(ns))
        return "\n".join(res)

    def rec_z_neigh_split(ns):
        res = []
        left = ns[:-1]
        left_pat = r" \/ ".join(f"z = {n}" for n in left)
        res.append(f"- assume HL: {left_pat}.")
        if len(left) > 1:
            res.append(f"  apply HL.")
            res.append(indent(rec_z_neigh_split(left), "  "))
        else:
            n = left[0]
            res.append(indent(rec_z_neigh_body(n, "HL"), "  "))
        
        n = ns[-1]
        res.append(f"- assume HR: z = {n}.")
        res.append(indent(rec_z_neigh_body(n, "HR"), "  "))
        return "\n".join(res)

    def rec_z_neigh_body(n, h_name):
        res = []
        # h_name is z=n
        res.append(gen_tf_z_case(n, n, x_val, "Hxz", h_name))
        return "\n".join(res)

    lines.append(rec_yz_split(list(range(17))))
    return "\n".join(lines)

def gen_adj17_triangle_free():
    lines = []
    lines.append("Theorem Adj17_triangle_free : forall x y z : set, Adj17 x y -> Adj17 y z -> Adj17 x z -> False.")
    lines.append("let x y z.")
    lines.append("assume Hxy Hyz Hxz.")
    lines.append("apply Hxy.")
    
    def rec_x_split(vertices):
        res = []
        last = vertices[-1]
        left = vertices[:-1]
        left_def = gen_partial_def(left, i_var="x", j_var="y")
        res.append(f"- assume HL: {left_def}.")
        if len(left) > 1:
            res.append(f"  apply HL.")
            res.append(indent(rec_x_split(left), "  "))
        else:
            v = left[0]
            res.append(indent(rec_x_body(v, "HL"), "  "))
        right_def = gen_vertex_clause(last, i_var="x", j_var="y")
        res.append(f"- assume HR: {right_def}.")
        res.append(indent(rec_x_body(last, "HR"), "  "))
        return "\n".join(res)

    def rec_x_body(v, h_name):
        res = []
        res.append(f"apply {h_name}.")
        res.append(f"assume Hx_eq: x = {v}.")
        ns = adj[v]
        n_disj = r" \/ ".join(f"y = {n}" for n in ns)
        res.append(f"assume Hy: {n_disj}.")
        res.append(f"apply Hy.")
        
        def rec_y_neigh_split(ns):
            r = []
            left = ns[:-1]
            left_pat = r" \/ ".join(f"y = {n}" for n in left)
            r.append(f"- assume HL: {left_pat}.")
            if len(left) > 1:
                r.append(f"  apply HL.")
                r.append(indent(rec_y_neigh_split(left), "  "))
            else:
                n = left[0]
                r.append(indent(rec_y_neigh_body(n, "HL"), "  "))
            n = ns[-1]
            r.append(f"- assume HR: y = {n}.")
            r.append(indent(rec_y_neigh_body(n, "HR"), "  "))
            return "\n".join(r)

        def rec_y_neigh_body(n, h_name):
            r = []
            # h_name is hypothesis y=n
            r.append(gen_tf_y_body(n, v, h_name))
            return "\n".join(r)
            
        res.append(rec_y_neigh_split(ns))
        return "\n".join(res)

    lines.append(rec_x_split(list(range(17))))
    lines.append("Qed.")
    return "\n".join(lines)

def main():
    # print(gen_all_edge_theorems()) # Already in adj17_complete.mg
    print(gen_neq_lemmas())
    print("\n")
    print(gen_adj17_sym())
    print("\n")
    print(gen_adj17_triangle_free())

if __name__ == "__main__":
    main()
