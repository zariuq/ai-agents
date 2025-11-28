#!/bin/bash
# Concatenate all relevant files for GPT-5.1/Gemini council help
# Focus: R(3,4)=9 proof completion in Megalodon

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT="council_context_${TIMESTAMP}.txt"

echo "Creating comprehensive context file: $OUTPUT"
echo "================================================================================" > "$OUTPUT"
echo "MEGALODON R(3,4)=9 PROOF - COUNCIL HELP REQUEST" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
echo "Timestamp: $(date)" >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "REQUEST: Help complete the remaining admits in r34_proof_kruger.mg" >> "$OUTPUT"
echo "Main challenges:" >> "$OUTPUT"
echo "  1. no_3_regular_9 - Parity/handshake lemma (27 edges / 2 = contradiction)" >> "$OUTPUT"
echo "  2. force_3_regularity - Cardinality reasoning on degree bounds" >> "$OUTPUT"
echo "  3. degree_lower_from_r33_6 - Apply R(3,3)=6 to induced subgraph" >> "$OUTPUT"
echo "  4. vertex_degree_from_complement - Disjoint union cardinality" >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 1: Current proof file
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 1: CURRENT PROOF FILE (r34_proof_kruger.mg)" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
cat r34_proof_kruger.mg >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 2: Progress status
if [ -f "R34_PROGRESS_STATUS.md" ]; then
    echo "================================================================================" >> "$OUTPUT"
    echo "SECTION 2: PROGRESS STATUS" >> "$OUTPUT"
    echo "================================================================================" >> "$OUTPUT"
    cat R34_PROGRESS_STATUS.md >> "$OUTPUT"
    echo "" >> "$OUTPUT"
    echo "" >> "$OUTPUT"
fi

# Section 3: Krüger's thesis (the proof strategy)
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 3: KRÜGER'S THESIS - R(3,4)=9 PROOF (lines 500-600)" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
if [ -f "related_literature/FULLTEXT01.txt" ]; then
    sed -n '500,600p' related_literature/FULLTEXT01.txt >> "$OUTPUT"
else
    echo "WARNING: FULLTEXT01.txt not found" >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 4: Paper's TeX (if available)
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 4: PAPER TEX SOURCE (if available)" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
if [ -f "paper/2025_02_07_b1cb8ce31b5aabf14429g.tex" ]; then
    cat paper/2025_02_07_b1cb8ce31b5aabf14429g.tex >> "$OUTPUT"
else
    echo "WARNING: Paper .tex not found" >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 5: Megalodon Preamble (essential axioms and definitions)
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 5: MEGALODON PREAMBLE - AXIOMS & DEFINITIONS" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
if [ -f "../Megalodon/examples/egal/PfgEAug2022Preamble.mgs" ]; then
    head -500 ../Megalodon/examples/egal/PfgEAug2022Preamble.mgs >> "$OUTPUT"
else
    echo "WARNING: Preamble not found" >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "... [Preamble truncated at 500 lines - full version available]" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 6: Existing R(3,3)=6 proof structure
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 6: R(3,3)=6 PROOF STRUCTURE (for reference)" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
if [ -f "../Megalodon/examples/egal/Ramsey_3_3_6.mg" ]; then
    head -100 ../Megalodon/examples/egal/Ramsey_3_3_6.mg >> "$OUTPUT"
    echo "... [R(3,3)=6 proof truncated - see lines 515+ for main theorem]" >> "$OUTPUT"
else
    echo "WARNING: Ramsey_3_3_6.mg not found" >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 7: Parity library
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 7: PARITY LIBRARY (for no_3_regular_9)" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
if [ -f "parity_lib.mg" ]; then
    cat parity_lib.mg >> "$OUTPUT"
else
    echo "WARNING: parity_lib.mg not found" >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 8: Cardinality toolkit
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 8: CARDINALITY TOOLKIT (relevant excerpts)" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
if [ -f "cardinality_toolkit.mg" ]; then
    head -200 cardinality_toolkit.mg >> "$OUTPUT"
    echo "... [Toolkit truncated - see full file for equip_17_without_one proof]" >> "$OUTPUT"
else
    echo "WARNING: cardinality_toolkit.mg not found" >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 9: Union cardinality work
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 9: UNION CARDINALITY INFRASTRUCTURE" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
if [ -f "union_cardinality_proven.mg" ]; then
    cat union_cardinality_proven.mg >> "$OUTPUT"
else
    echo "WARNING: union_cardinality_proven.mg not found" >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 10: How-to guide for Megalodon
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 10: MEGALODON HOW-TO GUIDE" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
if [ -f "../how-to-megalodon.md" ]; then
    cat ../how-to-megalodon.md >> "$OUTPUT"
else
    echo "WARNING: how-to-megalodon.md not found" >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 11: Related arithmetic files
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 11: ARITHMETIC INFRASTRUCTURE" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
echo "--- arithmetic_add_nat.mg ---" >> "$OUTPUT"
if [ -f "arithmetic_add_nat.mg" ]; then
    cat arithmetic_add_nat.mg >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "--- arithmetic_17_12_5.mg ---" >> "$OUTPUT"
if [ -f "arithmetic_17_12_5.mg" ]; then
    cat arithmetic_17_12_5.mg >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Section 12: Mizar l3_finset_1 example (if available)
echo "================================================================================" >> "$OUTPUT"
echo "SECTION 12: MIZAR l3_finset_1 EXAMPLE (union cardinality)" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
if [ -f "../theory/mizar/mml/all_Mega_20251125_222344.txt" ]; then
    cat ../theory/mizar/mml/all_Mega_20251125_222344.txt >> "$OUTPUT"
else
    echo "WARNING: Mizar example not found" >> "$OUTPUT"
fi
echo "" >> "$OUTPUT"
echo "" >> "$OUTPUT"

# Final summary
echo "================================================================================" >> "$OUTPUT"
echo "KEY QUESTIONS FOR COUNCIL:" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "1. PARITY LEMMA (no_3_regular_9):" >> "$OUTPUT"
echo "   How to prove: 'If every vertex in a 9-vertex symmetric relation has" >> "$OUTPUT"
echo "   exactly 3 neighbors, derive contradiction?'" >> "$OUTPUT"
echo "   Strategy: Sum of degrees = 9*3 = 27, but should equal 2*edges (even)." >> "$OUTPUT"
echo "   Need: Prove 27 is odd, odd ≠ 2k for any k." >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "2. REGULARITY FORCING (force_3_regularity):" >> "$OUTPUT"
echo "   Given: deg(v) ≤ 3 (proven) and deg(v) ≥ 3 (via R(3,3)=6)" >> "$OUTPUT"
echo "   Need: Construct explicit witness set N with |N|=3 and prove equip 3 N." >> "$OUTPUT"
echo "   Current approach: N := {x∈9 | R v x ∧ x≠v}" >> "$OUTPUT"
echo "   Challenge: How to prove this set has cardinality exactly 3?" >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "3. LOWER BOUND (degree_lower_from_r33_6):" >> "$OUTPUT"
echo "   Given: v has 3 neighbors N and 6 non-neighbors M" >> "$OUTPUT"
echo "   Need: Apply R(3,3)=6 to M (induced subgraph) to derive contradiction." >> "$OUTPUT"
echo "   Challenge: Formalize induced subgraph reasoning." >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "4. DISJOINT UNION (vertex_degree_from_complement):" >> "$OUTPUT"
echo "   Given: N∩M=∅, |N|=3, |M|=5" >> "$OUTPUT"
echo "   Need: Prove |N∪M|=8" >> "$OUTPUT"
echo "   Challenge: Megalodon syntax for disjoint union cardinality." >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "MEGALODON SYNTAX NOTES:" >> "$OUTPUT"
echo "- equip n A means 'exists bijection between n and A'" >> "$OUTPUT"
echo "- bij n A f means 'f is a bijection from n to A'" >> "$OUTPUT"
echo "- nat_p n means 'n is a natural number'" >> "$OUTPUT"
echo "- setsum (:+:) is tagged union with Inj0/Inj1" >> "$OUTPUT"
echo "- add_nat is ordinal addition" >> "$OUTPUT"
echo "- Admitted leaves a theorem proven but admitted" >> "$OUTPUT"
echo "- admit is NOT valid mid-proof (use Admitted for full theorem)" >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "Please provide Megalodon proof code that can compile with:" >> "$OUTPUT"
echo "  /path/to/megalodon -I PfgEAug2022Preamble.mgs r34_proof_kruger.mg" >> "$OUTPUT"
echo "" >> "$OUTPUT"
echo "================================================================================" >> "$OUTPUT"

echo "Done! Created: $OUTPUT"
echo "File size: $(wc -l < "$OUTPUT") lines"
echo ""
echo "Usage:"
echo "  cat $OUTPUT | pbcopy    # Copy to clipboard (macOS)"
echo "  cat $OUTPUT             # Display content"
echo "  less $OUTPUT            # Page through content"
