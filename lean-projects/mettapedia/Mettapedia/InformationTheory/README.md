# Information Theory (Lean 4)

`Mettapedia/InformationTheory` formalizes the basic information measures —
Shannon entropy, Kullback–Leibler divergence, and mutual information — including
a Faddeev-style axiomatic characterization of entropy.

## Files

| File | Contents |
|------|----------|
| `Basic.lean` | basic definitions |
| `EntropyKL.lean` | entropy and Kullback–Leibler divergence |
| `MutualInformation.lean` | mutual information |
| `Main.lean` | aggregate entry point |
| `ShannonEntropy/` (8) | Shannon-entropy development, incl. the Faddeev characterization |

## Status

`axiom`-free; one `sorry` remains, in the work-in-progress
`ShannonEntropy/Faddeev.lean` (the Faddeev characterization). Reproduce from this
directory:

```bash
# 1 sorry hit (ShannonEntropy/Faddeev.lean):
rg -n --glob '*.lean' '^\s*(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
```
