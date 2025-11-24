import os

# Define the graph edges and initial capacities
graph_edges = [
    (1, 2, 25), (1, 3, 20), (2, 4, 35), (2, 3, 30),
    (3, 4, 20), (4, 5, 40), (5, 6, 29)
]
initial_caps = {
    1: 0, 2: None, 3: None, 4: None, 5: None, 6: None
}
# Determine all unique weights and max possible cost
all_weights = sorted(list(set(w for _, _, w in graph_edges)))
max_cost = sum(all_weights) + 10 # A bit over, for safety. Max: 25+20+35+40+29 = 149

def generate_add_facts(max_val, weights):
    facts = []
    # Add C + W = Result
    for c in range(0, max_val + 1):
        for w in weights:
            res = c + w
            facts.append(f"(my-add {c} {w} {res})") # Renamed 'add' to 'my-add'
    return "\n".join(facts)

def generate_mm2_file(output_path):
    add_facts = generate_add_facts(max_cost, all_weights)

    mm2_content = f"""
;; Greedy Weighted Path (BFS with Cost) - V3 (Bugfix for MORK internal panic)
;; ========================================
;; Finds the weighted path cost to all nodes using a Greedy BFS strategy.
;; Uses explicit (my-add) facts, but isolates their matching to avoid Runner-Exec panic.

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

(reach 1 0)
(unseen 2)
(unseen 3)
(unseen 4)
(unseen 5)
(unseen 6)

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
(next-phase 5 1) ;; Cycle through 5 phases

;; ======================================================================
;; WORKER TEMPLATES
;; ======================================================================

;; PHASE 1: Expand Frontier
;; Consumes (reach), Reads (edge), Reads (unseen)
;; Produces (closed) + (cost-val $u $v $c) + (weight-val $u $v $w)
(worker-template 1 phase-1
  (, (reach $u $c) (edge $u $v $w) (unseen $v))
  (O (count (step-1-count $k) $k ($u $v)) ;; Dummy Aggregator
     (- (reach $u $c))
     (+ (closed $u $c))
     (+ (cost-val $u $v $c))             ;; Store cost from u
     (+ (weight-val $u $v $w))))         ;; Store weight of edge

;; PHASE 2: Create Sum Task (intermediate step to avoid direct my-add match in worker-template)
;; Consumes (cost-val) + (weight-val)
;; Produces (sum-task $u $v $c $w)
(worker-template 2 phase-2
  (, (cost-val $u $v $c) (weight-val $u $v $w))
  (O (count (step-2-count $k) $k ($u $v)) ;; Dummy Aggregator
     (- (cost-val $u $v $c))
     (- (weight-val $u $v $w))
     (+ (sum-task $u $v $c $w))))

;; PHASE 3: Perform Sum using (my-add) facts
;; Consumes (sum-task)
;; Produces (edge-cost)
(worker-template 3 phase-3
  (, (sum-task $u $v $c $w) (my-add $c $w $total))
  (O (count (step-3-count $k) $k ($u $v)) ;; Dummy Aggregator
     (- (sum-task $u $v $c $w))
     (+ (edge-cost $u $v $total))))

;; PHASE 4: Pick Best Path (Per Node)
;; Consumes (edge-cost)
;; Produces (best-cost) via MIN Sink
(worker-template 4 phase-4
  (, (edge-cost $u $v $total))
  (O (min (best-cost $v $min) $min $total)
     (- (edge-cost $u $v $total))))

;; PHASE 5: Commit (Update Frontier)
;; Consumes (best-cost), Consumes (unseen)
;; Produces (reach)
(worker-template 5 phase-5
  (, (best-cost $v $c) (unseen $v))
  (O (count (step-5-count $k) $k $v) ;; Dummy Aggregator
     (- (unseen $v))
     (- (best-cost $v $c))
     (+ (reach $v $c))))

;; Worker Templates for Cleanup (if best-cost remains but unseen is consumed by another path)
(worker-template 5 phase-5-cleanup
  (, (best-cost $v $c))
  (O ))
"""
    with open(output_path, "w") as f:
        f.write(mm2_content.strip())
    print(f"Generated {output_path}")

# --- Execution ---
output_file = "hyperon/MORK/examples/priority/greedy_weighted_path_v2.mm2"
generate_mm2_file(output_file)

print(f"\nNow running MORK on {output_file}")