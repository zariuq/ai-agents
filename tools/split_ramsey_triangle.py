#!/usr/bin/env python3
"""Generate per-triple TPTP problems for Adj17 triangle-free.

Creates a directory of small .p files, one for each unordered triple (i,j,k)
with i<j<k, encoding:

  fof(triple_i_j_k, conjecture, ~(adj17(ci,cj) & adj17(cj,ck) & adj17(ci,ck))).

The adj17 definition and distinctness axioms are shared from the source
TPTP file (default: megalodon/ramsey36/adj17_triangle_free.tptp). This keeps
each problem tiny so the pipeline (Vampire -> Dedukti -> Dedukit -> Megalodon)
can run fast per file.
"""

import argparse
import os
import re


def parse_adj17_source(path: str):
    with open(path, "r") as f:
        text = f.read()
    # Extract adj17_def; distinct will be generated as unit axioms
    adj_def = re.findall(r"fof\(adj17_def.*?\)\.\s*", text, flags=re.S)
    if not adj_def:
        raise RuntimeError("Could not find adj17_def in source TPTP")
    return adj_def[0].strip()


def generate_triples(n: int):
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                yield (i, j, k)


def generate_distinct_units(n: int):
    for i in range(n):
        for j in range(i + 1, n):
            yield f"fof(distinct_{i}_{j}, axiom, c{i} != c{j})."


def write_problem(out_dir: str, triple, adj_def: str, vertices: int):
    i, j, k = triple
    fname = os.path.join(out_dir, f"tri_{i}_{j}_{k}.p")
    conj = f"fof(tri_{i}_{j}_{k}, conjecture, ~(adj17(c{i}, c{j}) & adj17(c{j}, c{k}) & adj17(c{i}, c{k})))."
    with open(fname, "w") as f:
        f.write(adj_def)
        f.write("\n\n")
        for ax in generate_distinct_units(vertices):
            f.write(ax + "\n")
        f.write("\n")
        f.write(conj)
        f.write("\n")


def main():
    parser = argparse.ArgumentParser(description="Split Adj17 triangle-free into per-triple TPTP problems")
    parser.add_argument("--source", default="megalodon/ramsey36/adj17_triangle_free.tptp",
                        help="Path to the full triangle-free TPTP file")
    parser.add_argument("--out-dir", default="megalodon/tests/dedukti_bridge/triangle_split",
                        help="Output directory for per-triple .p files")
    parser.add_argument("--vertices", type=int, default=17, help="Number of vertices (default 17)")
    args = parser.parse_args()

    adj_def = parse_adj17_source(args.source)
    os.makedirs(args.out_dir, exist_ok=True)

    count = 0
    for triple in generate_triples(args.vertices):
        write_problem(args.out_dir, triple, adj_def, args.vertices)
        count += 1

    print(f"Wrote {count} problems to {args.out_dir}")


if __name__ == "__main__":
    main()
