import os

# Define the template for the robust Widest Path algorithm
TEMPLATE = """
;; Widest Path Problem - {name}
;; ============================================
;; Computes the path with the Maximum Bottleneck Capacity.
;; Target Node: {target}. Expected Width: {expected}.

;; ======================================================================
;; DATA
;; ======================================================================

{edges}

{caps}

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
(worker-template 1 phase-1
  (, (edge $u $v $w) (cap $u $uc))
  (O (count (step-1-count $k) $k ($u $v))
     (- (edge $u $v $w))
     (+ (processing-edge $u $v $w))
     (+ (calc-min $u $v $uc))
     (+ (calc-min $u $v $w))))

;; PHASE 2: Aggregate Min
(worker-template 2 phase-2
  (, (calc-min $u $v $val))
  (O (min (edge-offer $u $v $b) $b $val)
     (- (calc-min $u $v $val))))

;; PHASE 3: Collect Offers
(worker-template 3 phase-3-offers
  (, (edge-offer $u $v $offer))
  (O (count (step-3a-count $k) $k ($u $v))
     (- (edge-offer $u $v $offer))
     (+ (calc-max $v $offer))))

(worker-template 3 phase-3-current
  (, (cap $v $c))
  (O (count (step-3b-count $k) $k $v)
     (- (cap $v $c))
     (+ (processing-cap $v $c))
     (+ (calc-max $v $c))))

;; PHASE 4: Aggregate Max
(worker-template 4 phase-4
  (, (calc-max $v $val))
  (O (max (new-cap $v $mx) $mx $val)
     (- (calc-max $v $val))))

;; PHASE 5: Update State
(worker-template 5 phase-5
  (, (new-cap $v $new) (processing-cap $v $old))
  (O (count (step-5-count $k) $k $v)
     (- (new-cap $v $new))
     (- (processing-cap $v $old))
     (+ (cap $v $new))))

;; PHASE 6: Restore Edges
(worker-template 6 phase-6
  (, (processing-edge $u $v $w))
  (O (count (step-6-count $k) $k ($u $v))
     (- (processing-edge $u $v $w))
     (+ (edge $u $v $w))))
""

# Define the 3 Graphs
graphs = [
    {
        "filename": "widest_path_graph_a.mm2",
        "name": "Graph A (Reference)",
        "target": 6,
        "expected": 29,
        "edges": [
            (1, 2, 25), (1, 3, 20), (2, 4, 35), (2, 3, 30),
            (3, 4, 20), (4, 5, 40), (5, 6, 29)
        ],
        "nodes": [1, 2, 3, 4, 5, 6],
        "start": 1
    },
    {
        "filename": "widest_path_graph_b.mm2",
        "name": "Graph B (Long Wide vs Short Narrow)",
        "target": 4,
        "expected": 100,
        "edges": [
            (1, 2, 100), (2, 3, 100), (3, 4, 100), # Path 1 (Wide)
            (1, 4, 10)                             # Path 2 (Narrow)
        ],
        "nodes": [1, 2, 3, 4],
        "start": 1
    },
    {
        "filename": "widest_path_graph_c.mm2",
        "name": "Graph C (Bottleneck Trap)",
        "target": 4,
        "expected": 50,
        "edges": [
            (1, 2, 100), (2, 4, 10),  # Path 1: Bottleneck 10
            (1, 3, 100), (3, 4, 50)   # Path 2: Bottleneck 50 (Winner)
        ],
        "nodes": [1, 2, 3, 4],
        "start": 1
    }
]

def generate_files():
    for g in graphs:
        edges_str = "\n".join([f"(edge {u} {v} {w})" for u, v, w in g["edges"]])
        caps_str = "\n".join([f"(cap {n} {1000 if n == g['start'] else 0})" for n in g["nodes"]])
        
        content = TEMPLATE.format(
            name=g["name"],
            target=g["target"],
            expected=g["expected"],
            edges=edges_str,
            caps=caps_str
        )
        
        path = f"hyperon/MORK/examples/priority/{g['filename']}"
        with open(path, "w") as f:
            f.write(content.strip())
        print(f"Generated {path}")

generate_files()
