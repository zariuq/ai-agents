#!/usr/bin/env bash
set -euo pipefail

MEGALODON="/home/zar/claude/megalodon/bin/megalodon"
PREAMBLE="/home/zar/claude/megalodon/Megalodon/examples/egal/PfgEAug2022Preamble.mgs"
ROOT="/home/zar/claude/megalodon/probability_theory"

"$MEGALODON" -I "$PREAMBLE" -s "$ROOT/full_probability_theory.mgs" "$ROOT/full_probability_theory.mg"

"$MEGALODON" -I "$PREAMBLE" -I "$ROOT/full_probability_theory.mgs" -s "$ROOT/05_real_analysis.mgs" "$ROOT/05_real_analysis.mg"
"$MEGALODON" -I "$PREAMBLE" -I "$ROOT/full_probability_theory.mgs" -I "$ROOT/05_real_analysis.mgs" -s "$ROOT/06_outer_measure.mgs" "$ROOT/06_outer_measure.mg"
"$MEGALODON" -I "$PREAMBLE" -I "$ROOT/full_probability_theory.mgs" -I "$ROOT/05_real_analysis.mgs" -I "$ROOT/06_outer_measure.mgs" -s "$ROOT/07_caratheodory.mgs" "$ROOT/07_caratheodory.mg"
"$MEGALODON" -I "$PREAMBLE" -I "$ROOT/full_probability_theory.mgs" -I "$ROOT/05_real_analysis.mgs" -I "$ROOT/06_outer_measure.mgs" -I "$ROOT/07_caratheodory.mgs" -s "$ROOT/08_measurable_functions.mgs" "$ROOT/08_measurable_functions.mg"

"$MEGALODON" -I "$PREAMBLE" -I "$ROOT/full_probability_theory.mgs" -I "$ROOT/05_real_analysis.mgs" -I "$ROOT/06_outer_measure.mgs" -I "$ROOT/07_caratheodory.mgs" -I "$ROOT/08_measurable_functions.mgs" -s "$ROOT/09_integration_simple.mgs" "$ROOT/09_integration_simple.mg"
"$MEGALODON" -I "$PREAMBLE" -I "$ROOT/full_probability_theory.mgs" -I "$ROOT/05_real_analysis.mgs" -I "$ROOT/06_outer_measure.mgs" -I "$ROOT/07_caratheodory.mgs" -I "$ROOT/08_measurable_functions.mgs" -I "$ROOT/09_integration_simple.mgs" -s "$ROOT/10_integration_lebesgue.mgs" "$ROOT/10_integration_lebesgue.mg"

"$MEGALODON" -I "$PREAMBLE" -I "$ROOT/full_probability_theory.mgs" -I "$ROOT/05_real_analysis.mgs" -I "$ROOT/06_outer_measure.mgs" -I "$ROOT/07_caratheodory.mgs" -I "$ROOT/08_measurable_functions.mgs" -I "$ROOT/09_integration_simple.mgs" -I "$ROOT/10_integration_lebesgue.mgs" -s "$ROOT/11_product_measure.mgs" "$ROOT/11_product_measure.mg"

"$MEGALODON" -I "$PREAMBLE" -I "$ROOT/full_probability_theory.mgs" -I "$ROOT/05_real_analysis.mgs" -I "$ROOT/06_outer_measure.mgs" -I "$ROOT/07_caratheodory.mgs" -I "$ROOT/08_measurable_functions.mgs" -I "$ROOT/09_integration_simple.mgs" -I "$ROOT/10_integration_lebesgue.mgs" -I "$ROOT/11_product_measure.mgs" -s "$ROOT/12_random_variables.mgs" "$ROOT/12_random_variables.mg"

"$MEGALODON" -I "$PREAMBLE" -I "$ROOT/full_probability_theory.mgs" -I "$ROOT/05_real_analysis.mgs" -I "$ROOT/06_outer_measure.mgs" -I "$ROOT/07_caratheodory.mgs" -I "$ROOT/08_measurable_functions.mgs" -I "$ROOT/09_integration_simple.mgs" -I "$ROOT/10_integration_lebesgue.mgs" -I "$ROOT/11_product_measure.mgs" -I "$ROOT/12_random_variables.mgs" -s "$ROOT/13_convergence_theorems.mgs" "$ROOT/13_convergence_theorems.mg"
