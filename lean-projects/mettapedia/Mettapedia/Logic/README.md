# Mettapedia Logic Module

This module formalizes probabilistic logic networks (PLN) and their connections to
probability theory, imprecise probability, and Heyting algebras.

## Key Insight: PLN Evidence ↔ Credal Sets ↔ Interval Probability

### The Connection

PLN represents beliefs as **Evidence** pairs `(n⁺, n⁻)` where:
- `n⁺` = positive evidence (support for proposition)
- `n⁻` = negative evidence (support against proposition)

The **strength** of evidence is `s = n⁺ / (n⁺ + n⁻)` ∈ [0,1].

**Key Theorem**: Evidence forms a **partial order** where two values can be
**incomparable** (neither dominates the other). This incomparability represents
**epistemic uncertainty** about the true state of the world!

### The Credal Set Bridge

When we have uncertainty about which Evidence value is correct, we represent this
as a **credal set** (set of possible Evidence values). This induces:

```
Single Evidence value    →  Point probability (precise)
Set of Evidence values   →  Interval probability [min_s, max_s] (imprecise)
```

**Formally Proven** (`HeytingValuationOnEvidence.lean`):
- `credalGap_singleton`: Singleton credal sets have gap = 0 (point probability)
- `evidence_not_boolean`: Evidence has no Boolean complement

### Analogy with Heyting K&S

| PLN Evidence | Heyting K&S | Interpretation |
|--------------|-------------|----------------|
| Singleton credal set | Boolean element (a ⊔ ¬a = ⊤) | Precise knowledge |
| Non-singleton credal set | Non-Boolean element | Epistemic uncertainty |
| Credal gap | Excluded middle gap | Measure of uncertainty |
| Strength interval | [ν(a), 1-ν(¬a)] | Probability bounds |

### The Reverse Direction: Credal Sets → PLN Evidence

Given an interval [p_lower, p_upper], we CAN construct Evidence:
- For any s ∈ [p_lower, p_upper], take e = (k·s, k·(1-s)) for any k > 0

**But Evidence is RICHER than intervals!**

| What credal sets capture | What PLN Evidence adds |
|--------------------------|------------------------|
| Probability bounds [a, b] | Actual evidence counts |
| "What we know" | "How we know it" |
| Point in [0,1]² | Extra dimension: total evidence |

The extra structure in Evidence:
1. **Confidence**: Total evidence (n⁺ + n⁻) measures certainty
2. **Compositionality**: Evidence combines via ⊕ (counts add)
3. **Beta conjugacy**: Evidence = sufficient statistic for Beta(α, β) posterior

So: `Intervals ↪ Evidence` is an embedding, but Evidence has more structure!

This explains WHY PLN uses 2D evidence instead of just intervals:
the 2nd dimension (total count) enables proper evidence aggregation.

**Formally Proven** (`HeytingValuationOnEvidence.lean`):
- `evidence_richer_than_strength`: ∃ e₁ e₂ with same strength but different totals
- `strength_fiber_infinite`: For any s ∈ (0,1), infinitely many Evidence values have strength s
- `evidence_confidence_distinguishes`: Confidence distinguishes what intervals cannot

### Why This Matters

1. **Unifies** PLN evidence theory with imprecise probability (Walley 1991)
2. **Explains** why PLN needs 2D evidence: the partial order captures incomparability
3. **Connects** to Heyting/intuitionistic logic: non-Boolean = uncertain
4. **Provides** interval bounds from the quantale structure
5. **Reveals** Evidence as richer than intervals: includes confidence/weight

## Files

| File | Description |
|------|-------------|
| `PLNEvidence.lean` | Evidence structure, quantale operations (⊗, ⊕) |
| `PLNDeduction.lean` | PLN deduction rules formalized |
| `EvidenceQuantale.lean` | Commutative quantale instance for Evidence |
| `EvidenceIntervalBounds.lean` | Strength function, incomparability, Fréchet bounds |
| `HeytingValuationOnEvidence.lean` | Credal sets, PLN↔Heyting connection |
| `EvidenceBeta.lean` | Bridge to Beta distribution (conjugate prior) |

## References

- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
- Goertzel et al., "Probabilistic Logic Networks" (2008)
- Knuth & Skilling, "Foundations of Inference" (2012)
