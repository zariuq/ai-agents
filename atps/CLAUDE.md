# ATP Premise Selection Experiments

## PLN Premise Selection

Maintain the spirit of Probabilistic Logic Networks — extensible into Hyperon AGI, not just statistics.
- PLN Book: `/home/zar/claude/literature/Hyperon Study Materials/pln_book_txt/pln_book_full.txt`
- PLN Lean formalization: `/home/zar/claude/lean-projects/mettapedia/`
- PeTTa PLN libraries: `hyperon/PeTTa/pln_inference/`, `hyperon/PeTTa/lib/lib_pln_xi.metta`

## System Resources

**Machine:** 14 cores. Use max 8 for ATP work, always `nice -n 19`.

```bash
CORES=8; NICE="nice -n 19";
```
## Evaluation Rules

- Save E prover output to .out files (results without proofs are worthless)
- Never overwrite existing .out or result files
- One script per step: selection, proving, analysis
- Run 5-problem smoke test before full eval

- Note, if you mess up data integrity, it will be deleted as wasted effort.
