import os

# Define the graph edges and initial capacities
graph_edges = [
    (1, 2, 25), (1, 3, 20), (2, 4, 35), (2, 3, 30),
    (3, 4, 20), (4, 5, 40), (5, 6, 29),
    (1, 6, 200) # Trap for Greedy BFS (1 hop but high cost)
]
# Lower infinity to 200 to ensure add table covers it
initial_costs = {
    1: 0, 2: 200, 3: 200, 4: 200, 5: 200, 6: 200
}
# Determine all unique weights and max possible cost
all_weights = sorted(list(set(w for _, _, w in graph_edges)))
max_cost = 300 # Covers 200 + max_weight

def generate_add_facts(max_val, weights):
    facts = []
    for c in range(0, max_val + 1):
        for w in weights:
            res = c + w
            # Generate facts up to a safe limit
            facts.append(f"(my-add {c} {w} {res})")
    return "\n".join(facts)

def generate_mm2_file(output_path):
    add_facts = generate_add_facts(max_cost, all_weights)
    
    # Generate initial cost facts
    cost_facts = "\n".join([f"(cost {n} {c})" for n, c in initial_costs.items()])

    mm2_content = f"""
;; Shortest Weighted Path (Dijkstra / Bellman-Ford Style) - V2
;; =====================================================
;; Finds the minimum path cost to all nodes.
;; Iteratively relaxes edges: cost(v) = min(cost(v), cost(u) + w).
;; Uses Bulk Synchronous Phase architecture.
;; Fix: Infinity = 200 to match add-table range.

;; ======================================================================
;; DATA
;; ======================================================================

{add_facts}

(edge 1 2 25)
(edge 1 3 20)
(edge 2 4 35)
(edge 2 3 30)
(edge 3 4 20)
(edge 4 5 40)
(edge 5 6 29)
(edge 1 6 200)

{cost_facts}

;; ======================================================================
;; CONTROL: Phase Runner
;; ======================================================================
(phase 1)

(exec (10 run-phases)
  (, (phase $p) (next-phase $p $next)
     (worker-template $p $loc $pat $tmpl)
     (exec (10 run-phases) $rpt $rtmpl))
  (O (+ (phase $next))
     (- (phase $p))
     (+ (exec (0 $loc) $pat $tmpl))
     (+ (exec (10 run-phases) $rpt $rtmpl))))

(next-phase 1 2)
(next-phase 2 3)
(next-phase 3 4)
(next-phase 4 5)
(next-phase 5 6)
(next-phase 6 1)

;; ======================================================================
;; WORKER TEMPLATES
;; ======================================================================

;; PHASE 1: Expand
;; Consumes (edge), Reads (cost)
;; Produces (processing-edge) + (cost-val) + (weight-val)
(worker-template 1 phase-1
  (, (edge $u $v $w) (cost $u $c))
  (O (count (step-1-count $k) $k ($u $v))
     (- (edge $u $v $w))
     (+ (processing-edge $u $v $w))
     (+ (cost-val $u $v $c))
     (+ (weight-val $u $v $w))))

;; PHASE 2: Create Sum Task
;; Consumes (cost-val) + (weight-val)
;; Produces (sum-task)
(worker-template 2 phase-2
  (, (cost-val $u $v $c) (weight-val $u $v $w))
  (O (count (step-2-count $k) $k ($u $v))
     (- (cost-val $u $v $c))
     (- (weight-val $u $v $w))
     (+ (sum-task $u $v $c $w))))

;; PHASE 3: Perform Sum (Calculate Offer)
;; Matches (sum-task) and (my-add)
;; Produces (offer $v $new_cost)
(worker-template 3 phase-3
  (, (sum-task $u $v $c $w) (my-add $c $w $total))
  (O (count (step-3-count $k) $k ($u $v))
     (- (sum-task $u $v $c $w))
     (+ (offer $v $total))))

;; PHASE 4: Aggregate Min (Pick Best Offer vs Current)
;; Sub-task A: Consume (offer) -> (candidate-cost)
;; Sub-task B: Consume (cost) -> (processing-cost) + (candidate-cost)
(worker-template 4 phase-4-offers
  (, (offer $v $total))
  (O (count (step-4a-count $k) $k $v)
     (- (offer $v $total))
     (+ (candidate-cost $v $total))))

(worker-template 4 phase-4-current
  (, (cost $v $c))
  (O (count (step-4b-count $k) $k $v)
     (- (cost $v $c))
     (+ (processing-cost $v $c))
     (+ (candidate-cost $v $c))))

;; PHASE 5: Finalize Min
;; Consumes (candidate-cost)
;; Produces (new-cost) via MIN
(worker-template 5 phase-5-min
  (, (candidate-cost $v $val))
  (O (min (new-cost $v $min) $min $val)
     (- (candidate-cost $v $val))))

;; PHASE 6: Commit and Restore
;; 6a: Update Cost
(worker-template 6 phase-6-update
  (, (new-cost $v $new) (processing-cost $v $old))
  (O (count (step-6a-count $k) $k $v)
     (- (new-cost $v $new))
     (- (processing-cost $v $old))
     (+ (cost $v $new))))

;; 6b: Restore Edges
(worker-template 6 phase-6-restore
  (, (processing-edge $u $v $w))
  (O (count (step-6b-count $k) $k ($u $v))
     (- (processing-edge $u $v $w))
     (+ (edge $u $v $w))))
"""
    with open(output_path, "w") as f:
        f.write(mm2_content.strip())
    print(f"Generated {output_path}")

# --- Execution ---
output_file = "hyperon/MORK/examples/priority/shortest_weighted_path.mm2"
generate_mm2_file(output_file)

print(f"\nNow running MORK on {output_file}")
