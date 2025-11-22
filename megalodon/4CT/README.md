# Formal Refutation of Goertzel's 4CT Proof

## Summary

This directory contains **formal, kernel-verifiable proofs** demonstrating that Ben Goertzel's claimed proof of the Four Color Theorem (v1-v3, 2025) is **fundamentally blocked** via three independent mechanisms:

| Blocker | Type | Status | File |
|---------|------|--------|------|
| **1** | Proof technique broken | **Kernel-verified** | `BlockerTheorem.mg` |
| **2** | Span ⇒ Reachability conditional | **Proven** | `SpanningImpliesReachability.mg` |
| **3** | Concrete counterexample | **Axiomatized (Tilley 2018)** | `BirkhoffDiamond.mg` |

**Main Result**: `NO_GO_THEOREM.mg` packages all results into a clean, referee-ready statement.

---

## The Bug (Blocker 1)

### What Goertzel Claims

**Lemma 4.3** (Per-run purification): For face generator X^f_{αβ}(C) and Kempe cycle D containing run R:

```
X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R    (CLAIMED)
```

This claims the XOR isolates the **boundary run R**.

### What Is Actually True

```
X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_{D\R} = γ · 1_{A∪A'}    (ACTUAL)
```

The XOR gives the **interior arcs A ∪ A'**, NOT the boundary run R.

### Why This Happens

For run R with Kempe cycle D = R ∪ A ∪ A':
- In coloring C: contribution is γ · 1_{R∪A}
- In coloring C^R: contribution is γ · 1_{R∪A'}
- XOR: γ · 1_{(R∪A) △ (R∪A')}

Computing the symmetric difference:
- **On R**: Both sets contain R, so R **cancels** (contributes 0)
- **On A**: Only (R∪A) contains A, so A **survives**
- **On A'**: Only (R∪A') contains A', so A' **survives**

Result: (R∪A) △ (R∪A') = A ∪ A' = D \ R

**The paper has it exactly backwards.**

---

## File Descriptions

### `BlockerTheorem.mg` (844 lines) - BLOCKER 1

**Core theorem**: Per-run purification yields interior-only chains.

Key proven lemmas (all kernel-verified):
- `xor_assoc`, `xor_comm`, `xor_zero_l`, `xor_zero_r`, `xor_self`
- `chain_xor_assoc`, `chain_xor_comm`, `chain_xor_zero_r`, `chain_xor_self`
- `indicator_xor_symm_diff`: XOR of indicators = indicator of symmetric difference
- `symmetric_diff_with_common_part`: (R∪A) △ (R∪A') = A ∪ A'
- **`per_run_xor_is_interior`**: The main blocking theorem
- `per_run_diff_zero_on_boundary`: Per-run difference is 0 on boundary
- `paper_claim_impossible`: Goertzel's claimed result is impossible
- `span_per_run_diffs_is_interior`: Span of all per-run diffs is interior-only

### `SpanningImpliesReachability.mg` (500+ lines) - BLOCKER 2

**Core theorem**: Disk-spanning implies local reachability.

Key proven results:
- `difference_vanishes_on_boundary`: Δ = C₁ ⊕ C₂ is 0 on boundary
- `three_color_xor_is_zero`: r ⊕ b ⊕ p = 0 in F₂²
- `difference_satisfies_kirchhoff`: Difference of proper colorings satisfies Kirchhoff
- `difference_in_W0`: Δ ∈ W₀(H)
- **`spanning_implies_reachability`**: If W₀(H) ⊆ span(G) and generators realizable, then local reachability holds
- **`reachability_failure_implies_spanning_failure`**: Contrapositive
- `kempe_locked_disproves_spanning`: Kempe-locked regions disprove spanning

### `BirkhoffDiamond.mg` (624 lines) - BLOCKER 3

**Core theorem**: Concrete Kempe-locked counterexample.

The Birkhoff Diamond (order 10):
- 6 outer ring vertices: V0, V1, V2, V3, V4, V5
- 4 inner vertices: VA, VB, VC, VD
- Locked edge: xy = (V0, V3)

Key results:
- `birkhoff_is_kempe_locked`: Computationally verified by Tilley (2018)
- `H_birkhoff_is_edge_kempe_locked`: Via Tait duality
- **`birkhoff_disproves_goertzel`**: W₀(H_birkhoff) ⊄ span(G)
- `goertzel_prop_4_11_is_false`: ∃H where local reachability fails

### `NO_GO_THEOREM.mg` - COMPLETE PACKAGING

Referee-ready theorem statements:
- `Complete_NoGo_Theorem`: All three blockers combined
- `no_salvage_possible`: Why creative fixes won't work

### Other Files

- `F2_Color.mg` (1,653 lines): Complete F₂² color algebra, all kernel-verified
- `RunPurification.mg` (705 lines): Run invariance and purification attempts
- `Lemma43_Correction.mg` (415 lines): Direct proof of the Lemma 4.3 bug
- `PROOF_AVENUE_BLOCKED.mg` (596 lines): Axiomatic proof of blocking

---

## The Three Blockers Explained

### Blocker 1: Proof Technique is Broken

**Statement**: Per-run purification gives interior-only chains.

**Implication**:
- Lemma 4.3 is mathematically false
- Lemma 4.4 (face-level purification) cannot be derived
- The entire purification → peeling → spanning proof path fails

**Strength**: This is a **calculation error**, not a typo or gap. The paper's claimed result is **mathematically impossible** given the definitions.

### Blocker 2: Span ⇒ Reachability (Conditional)

**Statement**: If W₀(H) ⊆ span(G) and generators are Kempe-realizable, then local reachability holds.

**Contrapositive**: If local reachability fails, then W₀(H) ⊄ span(G).

**Implication**: The truth of Theorem 4.10 (disk-spanning) is **tied to** the truth of Proposition 4.11 (local reachability). If one fails, so does the other.

### Blocker 3: Kempe-Locked Counterexample

**Statement**: The Birkhoff Diamond is Kempe-locked.

**Evidence**: Computationally verified by Tilley (2018), published in MDPI Mathematics.

**Implication**:
- Via Tait duality, H_birkhoff is edge-Kempe-locked
- By contrapositive of Blocker 2: W₀(H_birkhoff) ⊄ span(G)
- Theorem 4.10 is **FALSE** for at least one between-region H

---

## Combined Effect: No Wiggle Room

```
┌─────────────────────────────────────────────────────────────┐
│                    DOUBLY BLOCKED                           │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  (A) The PROOF TECHNIQUE is broken:                         │
│      • Per-run XOR gives interior, not boundary             │
│      • No linear combination can produce boundary chains    │
│      • Lemma 4.3 is mathematically false                    │
│                                                             │
│  (B) The THEOREM STATEMENT is false for some H:             │
│      • Kempe-locked configurations exist                    │
│      • For H_birkhoff: W₀(H) ⊄ span(G)                      │
│      • Proposition 4.11 fails                               │
│                                                             │
│  CONCLUSION: No creative salvage can fix both issues.       │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

---

## What This Does NOT Claim

1. **NOT** "The Four Color Theorem is false"
   - The 4CT is TRUE (Appel-Haken 1976, computer-verified)
   - We only show THIS PARTICULAR PROOF is invalid

2. **NOT** "No algebraic proof of 4CT can work"
   - Different generators or different spanning arguments may succeed
   - We only block the specific per-run purification mechanism

3. **NOT** "W₀(H) ⊄ span(G) for ALL H"
   - Spanning may hold for many between-regions
   - We only prove it fails for SOME H (Kempe-locked ones)

---

## Verification

### Building Megalodon

```bash
cd /home/user/ai-agents/megalodon
./setup_megalodon.sh  # Downloads and builds Megalodon
```

### Checking Proofs

```bash
# Check BlockerTheorem
./bin/megalodon -mizar -I examples/mizar/PfgMizarNov2020Preamble.mgs 4CT/BlockerTheorem.mg

# Check SpanningImpliesReachability
./bin/megalodon -mizar -I examples/mizar/PfgMizarNov2020Preamble.mgs 4CT/SpanningImpliesReachability.mg

# Check full No-Go Theorem
./bin/megalodon -mizar -I examples/mizar/PfgMizarNov2020Preamble.mgs 4CT/NO_GO_THEOREM.mg
```

Exit code 0 = kernel verified.

---

## Proof Status Summary

| Lemma | Status | Notes |
|-------|--------|-------|
| XOR algebra | **Kernel-verified** | All 16 operations compute to reflexivity |
| `per_run_xor_is_interior` | **Kernel-verified** | Core Blocker 1 result |
| `spanning_implies_reachability` | Proven (structural) | Relies on geometric axioms |
| `reachability_failure_implies_spanning_failure` | **Proven** | Clean contrapositive |
| `birkhoff_is_kempe_locked` | Axiomatized | Tilley (2018) computational verification |
| `Complete_NoGo_Theorem` | **Proven** | Combines all blockers |

Total: ~5,200 lines of formal proofs

---

## References

1. **Goertzel, B.** (2025). "A Spencer-Brown/Kauffman-Style Proof of the Four-Color Theorem via Disk Kempe-Closure Spanning and Local Reachability" v1, v2, v3.

2. **Tilley, J.** (2018). "Kempe-Locking Configurations" *MDPI Mathematics* 6(12):309.
   https://www.mdpi.com/2227-7390/6/12/309

3. **Tilley, J.** (2018). "The Birkhoff Diamond as Double Agent" arXiv:1809.02807.

4. **Tait, P.G.** (1880). "Remarks on the Colouring of Maps" *Proc. Royal Society of Edinburgh* 10:501-503.

5. **Kauffman, L.H.** (2005). "Reformulating the Map Color Theorem" *Discrete Mathematics* 302(1-3):145-172.

---

## Authors

This formal analysis was developed through collaboration between human mathematicians and AI assistants (Claude), using the Megalodon theorem prover.

---

## License

This work is provided for academic and research purposes. The formal proofs are licensed under CC BY 4.0.
