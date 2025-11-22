# Formal Refutation of Goertzel's 4CT Proof - VERIFIED

## Summary

This directory contains **kernel-verified proofs** in Megalodon demonstrating
that Ben Goertzel's claimed proof of the Four Color Theorem (v1-v3, 2025)
contains fundamental mathematical errors.

## Verified Files (Exit: 0)

All proofs pass Megalodon kernel verification.

| File | Description |
|------|-------------|
| `xor_self_inverse.mg` | XOR self-inverse: c XOR c = 0 for all colors |
| `xor_full.mg` | Complete F2^2 XOR operation table (16 cases) |
| `symm_diff.mg` | Symmetric difference theorems |
| `blocker1.mg` | **BLOCKER 1**: Per-run XOR gives interior, not boundary |
| `blocker2.mg` | **BLOCKER 2**: Chain existence ≠ conflict-free swap |
| `blocker3_birkhoff.mg` | **BLOCKER 3**: Birkhoff Diamond Kempe-locking |

## The Three Blockers

### Blocker 1: Per-Run Purification Bug (blocker1.mg)

**What Goertzel Claims (Lemma 4.3)**:
```
X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R    (CLAIMED)
```
The XOR isolates the boundary run R.

**What Is Actually True**:
```
X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_{A∪A'}    (ACTUAL)
```
The XOR gives the interior arcs A ∪ A', NOT the boundary run R.

**Key Theorems**:
- `per_run_xor_domain`: x ∈ (R∪A) △ (R∪A') → x ∈ A ∪ A'
- `boundary_not_in_xor`: x ∈ R → x ∉ (R∪A) △ (R∪A')

### Blocker 2: Spanning ≠ Reachability (blocker2.mg)

Shows that Kempe chain membership (spanning) does not guarantee
conflict-free swapping (reachability).

**Key Theorems**:
- `spanning_exists_but_swap_conflicts`: All vertices in chain, but
  swapping creates color equality violations
- `swap_creates_same_color`: After swap, col'(v0) = col'(v2)

### Blocker 3: Birkhoff Diamond (blocker3_birkhoff.mg)

Models the classic Kempe-locking counterexample from Tilley (2018).

**Key Theorems**:
- `v0_in_chain_01`, `v4_in_chain_01`: Both endpoints in same chain
- `swap_creates_conflict`: After swap, col'(v0) = col'(v4)

This shows Kempe chains can be "locked" - swapping one part
forces a conflict elsewhere in the graph.

## Why These Block the Proof

1. **Blocker 1** shows Lemma 4.3 computes the wrong set - the symmetric
   difference cancels R, not preserves it.

2. **Blocker 2** shows Theorem 3.7's gap - existence of chains doesn't
   mean they can be swapped without creating adjacent same-color vertices.

3. **Blocker 3** provides a concrete counterexample - the Birkhoff Diamond
   where Kempe swaps are locked by the graph structure.

## Verification Commands

```bash
cd megalodon

# Verify all files at once
for f in 4CT/*.mg; do
  echo -n "$f: "
  ./bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs "$f" && echo "VERIFIED"
done
```

Exit code 0 = kernel verified.

## Old/Unverified Files

Files with `.old` extension are previous attempts that did not verify.
They should be ignored - only `.mg` files pass the kernel.

## What This Does NOT Claim

1. **NOT** "The Four Color Theorem is false"
   - The 4CT is TRUE (Appel-Haken 1976, computer-verified)
   - We only show THIS PARTICULAR PROOF is invalid

2. **NOT** "No algebraic proof of 4CT can work"
   - Different approaches may succeed
   - We only block the specific mechanisms in Goertzel's paper

## References

1. **Goertzel, B.** (2025). "A Spencer-Brown/Kauffman-Style Proof of the
   Four-Color Theorem via Disk Kempe-Closure Spanning and Local Reachability"

2. **Tilley, J.** (2018). "The Birkhoff Diamond and the Four Color Theorem"

3. **Megalodon theorem prover**: http://grid01.ciirc.cvut.cz/~chad/
