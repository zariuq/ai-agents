/-
Joy and Pain Ontology
Based on "On the Ontology of Joy and Pain, Happiness and Suffering" (Garden of Minds)
and Ben Goertzel's "Logic of Pain" and "Well-Being Catalysis"

Core insight:
  - Proto-pain = experience associated with SEPARATION of pattern from substrate
  - Proto-joy = experience associated with FORMATION/UNIFICATION of pattern with substrate
  - Well-being = ongoing re-formation and individuation of pattern
-/

set_option linter.unusedVariables false

/-!
## 1. PATTERN DYNAMICS
══════════════════════════════════════════════════════════════════

A pattern exists in a substrate with some degree of instantiation.
Over time, patterns can form (strengthen) or separate (weaken).
-/

-- Time as natural numbers (discrete moments)
abbrev Time := Nat

-- Pattern strength: degree to which pattern is instantiated in substrate
-- Ranges conceptually from 0 (dissolved) to 100 (fully individuated)
abbrev Strength := Int

-- A pattern's state over time
structure PatternDynamics where
  strength : Time → Strength
  -- Bounded between 0 and 100
  nonneg : ∀ t, 0 ≤ strength t
  bounded : ∀ t, strength t ≤ 100

-- Rate of change (discrete derivative)
def delta (p : PatternDynamics) (t : Time) : Strength :=
  p.strength (t + 1) - p.strength t

-- SEPARATION: pattern weakening in substrate
def isSeparating (p : PatternDynamics) (t : Time) : Prop :=
  delta p t < 0

-- FORMATION: pattern strengthening in substrate
def isForming (p : PatternDynamics) (t : Time) : Prop :=
  delta p t > 0

-- STABLE: pattern maintaining
def isStable (p : PatternDynamics) (t : Time) : Prop :=
  delta p t = 0

-- Trichotomy: at each moment, exactly one of these holds
theorem dynamics_trichotomy (p : PatternDynamics) (t : Time) :
    (isSeparating p t ∨ isForming p t ∨ isStable p t) ∧
    ¬(isSeparating p t ∧ isForming p t) ∧
    ¬(isSeparating p t ∧ isStable p t) ∧
    ¬(isForming p t ∧ isStable p t) := by
  unfold isSeparating isForming isStable delta
  constructor
  · -- Trichotomy for Int comparison
    rcases Int.lt_trichotomy (p.strength (t + 1) - p.strength t) 0 with h | h | h
    · left; exact h
    · right; right; exact h
    · right; left; exact h
  · refine ⟨?_, ?_, ?_⟩
    · intro ⟨h1, h2⟩; exact Int.lt_irrefl _ (Int.lt_trans h1 h2)
    · intro ⟨h1, h2⟩; rw [h2] at h1; exact Int.lt_irrefl 0 h1
    · intro ⟨h1, h2⟩; rw [h2] at h1; exact Int.lt_irrefl 0 h1

/-!
## 2. PROTO-VALENCE (Before Consciousness)
══════════════════════════════════════════════════════════════════

Proto-pain and proto-joy are the raw experiential qualities
associated with separation and formation events, respectively.
-/

inductive ProtoValence where
  | ProtoPain   -- Associated with separation
  | ProtoJoy    -- Associated with formation
  | Neutral     -- Associated with stability
  deriving Repr, DecidableEq

def protoValence (p : PatternDynamics) (t : Time) : ProtoValence :=
  if delta p t < 0 then .ProtoPain
  else if delta p t > 0 then .ProtoJoy
  else .Neutral

-- Proto-valence correctly reflects dynamics
theorem protoValence_separation (p : PatternDynamics) (t : Time)
    (h : isSeparating p t) : protoValence p t = .ProtoPain := by
  unfold protoValence isSeparating at *
  simp [h]

theorem protoValence_formation (p : PatternDynamics) (t : Time)
    (h : isForming p t) : protoValence p t = .ProtoJoy := by
  unfold protoValence isForming at *
  have hNotNeg : ¬(delta p t < 0) := fun hNeg => Int.lt_irrefl _ (Int.lt_trans hNeg h)
  simp [hNotNeg, h]

/-!
## 3. REFLEXIVE SYSTEMS (Self-Modeling Patterns)
══════════════════════════════════════════════════════════════════

A reflexive system is a pattern that includes a model of itself.
Pain and joy (as opposed to proto-pain/joy) require reflexivity.
-/

-- A reflexive pattern models itself
structure ReflexivePattern extends PatternDynamics where
  -- The pattern's model of its own state
  selfModel : Time → Strength
  -- How accurately the self-model tracks actual state (0-100)
  modelAccuracy : Time → Strength
  accuracyNonneg : ∀ t, 0 ≤ modelAccuracy t
  accuracyBounded : ∀ t, modelAccuracy t ≤ 100

-- Threshold for "adequate" self-modeling (50%)
def reflexivityThreshold : Strength := 50

-- A transition is REFLEXIVE if adequately self-modeled
def isReflexiveTransition (r : ReflexivePattern) (t : Time) : Prop :=
  r.modelAccuracy t ≥ reflexivityThreshold

-- A transition is NON-REFLEXIVE if poorly self-modeled
def isNonReflexiveTransition (r : ReflexivePattern) (t : Time) : Prop :=
  r.modelAccuracy t < reflexivityThreshold

/-!
## 4. PAIN AND JOY (Conscious Valence)
══════════════════════════════════════════════════════════════════

From the ontology:
  Pain = proto-pain propagated to a reflexive system that does NOT
         adequately model the separation (non-reflexive separation)
  Joy = proto-joy propagated to a reflexive system that DOES
        adequately model the formation (reflexive formation)

Key insight: Pain comes from UNMODELED separation.
             Joy comes from MODELED formation.
-/

-- PAIN: Non-reflexive separation in a reflexive system
-- "The mindless death of a self-aware pattern-system"
def isPain (r : ReflexivePattern) (t : Time) : Prop :=
  isSeparating r.toPatternDynamics t ∧ isNonReflexiveTransition r t

-- JOY: Reflexive formation in a reflexive system
-- Conscious participation in one's own growth/individuation
def isJoy (r : ReflexivePattern) (t : Time) : Prop :=
  isForming r.toPatternDynamics t ∧ isReflexiveTransition r t

-- MINDFUL SEPARATION: Reflexive separation (less painful)
def isMindfulSeparation (r : ReflexivePattern) (t : Time) : Prop :=
  isSeparating r.toPatternDynamics t ∧ isReflexiveTransition r t

-- UNCONSCIOUS FORMATION: Non-reflexive formation (less joyful)
def isUnconsciousFormation (r : ReflexivePattern) (t : Time) : Prop :=
  isForming r.toPatternDynamics t ∧ isNonReflexiveTransition r t

-- KEY THEOREM: Pain and joy are incompatible at any moment
theorem pain_joy_incompatible (r : ReflexivePattern) (t : Time) :
    ¬(isPain r t ∧ isJoy r t) := by
  intro ⟨hPain, hJoy⟩
  unfold isPain isJoy isSeparating isForming at *
  obtain ⟨hSep, _⟩ := hPain
  obtain ⟨hForm, _⟩ := hJoy
  exact Int.lt_irrefl _ (Int.lt_trans hSep hForm)

-- Reflexivity reduces pain: if separation is reflexive, it's not pain
theorem reflexivity_prevents_pain (r : ReflexivePattern) (t : Time)
    (hSep : isSeparating r.toPatternDynamics t)
    (hRef : isReflexiveTransition r t) :
    ¬isPain r t := by
  intro hPain
  unfold isPain isNonReflexiveTransition isReflexiveTransition at *
  obtain ⟨_, hNonRef⟩ := hPain
  exact Int.lt_irrefl (r.modelAccuracy t) (Int.lt_of_lt_of_le hNonRef hRef)

/-!
## 5. SUFFERING AND HAPPINESS (Cascading Valence)
══════════════════════════════════════════════════════════════════

From the ontology:
  Suffering = auto-propagating cascade or cycle of proto-pain
  Happiness = auto-propagating cascade or cycle of proto-joy

Key insight: It's not just pain, but SUSTAINED, SELF-REINFORCING pain.
-/

-- Duration threshold for cascade
def cascadeThreshold : Nat := 3

-- A CASCADE is a sustained run of a condition
def isCascade (condition : Time → Prop) (start : Time) (duration : Nat) : Prop :=
  duration ≥ cascadeThreshold ∧ ∀ t, start ≤ t ∧ t < start + duration → condition t

-- SUFFERING: Sustained cascade of separation/pain
def isSuffering (r : ReflexivePattern) (t : Time) : Prop :=
  ∃ d : Nat, isCascade (fun τ => isSeparating r.toPatternDynamics τ) t d

-- HAPPINESS: Sustained cascade of formation/joy
def isHappiness (r : ReflexivePattern) (t : Time) : Prop :=
  ∃ d : Nat, isCascade (fun τ => isForming r.toPatternDynamics τ) t d

-- Suffering implies separation at the start
theorem suffering_implies_separation (r : ReflexivePattern) (t : Time)
    (h : isSuffering r t) : isSeparating r.toPatternDynamics t := by
  unfold isSuffering isCascade cascadeThreshold at h
  obtain ⟨d, ⟨hThresh, hAll⟩⟩ := h
  apply hAll t
  constructor
  · exact Nat.le_refl t
  · have : d > 0 := Nat.lt_of_lt_of_le (by decide : 0 < 3) hThresh
    exact Nat.lt_add_of_pos_right this

-- Happiness implies formation at the start
theorem happiness_implies_formation (r : ReflexivePattern) (t : Time)
    (h : isHappiness r t) : isForming r.toPatternDynamics t := by
  unfold isHappiness isCascade cascadeThreshold at h
  obtain ⟨d, ⟨hThresh, hAll⟩⟩ := h
  apply hAll t
  constructor
  · exact Nat.le_refl t
  · have : d > 0 := Nat.lt_of_lt_of_le (by decide : 0 < 3) hThresh
    exact Nat.lt_add_of_pos_right this

/-!
## 6. WELL-BEING AS ONGOING INDIVIDUATION
══════════════════════════════════════════════════════════════════

Well-being is NOT just formation events.
Well-being is the ONGOING RE-FORMATION and INDIVIDUATION of pattern.

This is the dynamic maintenance of self through change.
-/

-- INDIVIDUATION: Sustained reflexive formation
def isIndividuating (r : ReflexivePattern) (t : Time) : Prop :=
  isForming r.toPatternDynamics t ∧ isReflexiveTransition r t

-- Individuation IS joy (by definition alignment)
theorem individuation_is_joy (r : ReflexivePattern) (t : Time) :
    isIndividuating r t ↔ isJoy r t := by
  unfold isIndividuating isJoy
  rfl

/-!
## 7. MULTI-DOMAIN WELL-BEING (VibeStar Connection)
══════════════════════════════════════════════════════════════════

Life involves multiple pattern-domains.
Overall well-being = aggregate individuation across domains.
-/

-- Life domains (from VibeStar)
inductive LifeDomain where
  | Health        -- Physical/mental health
  | Relationships -- Social connections
  | Creation      -- Work, art, building
  | Spaces        -- Living environment
  | Resources     -- Material means
  | Play          -- Recreation, fun
  | Oneness       -- Spiritual connection
  deriving Repr, DecidableEq

-- A person has a reflexive pattern in each domain
structure MultiDomainPattern where
  patterns : LifeDomain → ReflexivePattern
  -- Importance weights for each domain
  weights : LifeDomain → Strength
  weightsNonneg : ∀ d, 0 ≤ weights d

-- Domain-specific well-being
def domainWellBeing (m : MultiDomainPattern) (d : LifeDomain) (t : Time) : Prop :=
  isIndividuating (m.patterns d) t

/-!
## 8. MIXED EMOTIONS (Multi-Pattern Coexistence)
══════════════════════════════════════════════════════════════════

From psychology research (Larsen & McGraw 2011, etc.):
  - Humans CAN experience pain and joy simultaneously
  - This is adaptive and beneficial for coping
  - Examples: nostalgia, "being moved", grief + gratitude

Reconciliation with pain_joy_incompatible:
  - Pain and joy are incompatible FOR A SINGLE PATTERN
  - But humans contain MULTIPLE patterns across domains
  - Mixed emotions arise from different patterns in different states
-/

-- Mixed emotions: simultaneous pain and joy across different domains
def hasMixedEmotions (m : MultiDomainPattern) (t : Time) : Prop :=
  ∃ d₁ d₂ : LifeDomain, d₁ ≠ d₂ ∧
    isPain (m.patterns d₁) t ∧ isJoy (m.patterns d₂) t

-- THEOREM: Mixed emotions are structurally possible
-- (The multi-domain structure permits what single patterns forbid)
theorem mixed_emotions_possible (m : MultiDomainPattern) (t : Time)
    (d₁ d₂ : LifeDomain) (h_diff : d₁ ≠ d₂)
    (h_pain : isPain (m.patterns d₁) t)
    (h_joy : isJoy (m.patterns d₂) t) :
    hasMixedEmotions m t :=
  ⟨d₁, d₂, h_diff, h_pain, h_joy⟩

-- THEOREM: Pain and joy remain incompatible WITHIN a single domain
-- (This is why mixed emotions require multiple domains)
theorem same_domain_no_mixed (m : MultiDomainPattern) (d : LifeDomain) (t : Time) :
    ¬(isPain (m.patterns d) t ∧ isJoy (m.patterns d) t) :=
  pain_joy_incompatible (m.patterns d) t

-- Example: Nostalgia = joy in memory/meaning + pain in loss
-- Grief + gratitude = pain in Relationships + joy in Oneness/meaning

/-!
## 9. KEY THEOREMS
══════════════════════════════════════════════════════════════════
-/

-- Joy requires both formation AND reflexivity
theorem joy_requires_both (r : ReflexivePattern) (t : Time)
    (hJoy : isJoy r t) :
    isForming r.toPatternDynamics t ∧ isReflexiveTransition r t := hJoy

-- Pain can be prevented by adequate reflexivity (mindfulness)
theorem mindfulness_prevents_pain (r : ReflexivePattern) (t : Time)
    (hRef : isReflexiveTransition r t) :
    ¬isPain r t := by
  intro hPain
  unfold isPain isNonReflexiveTransition isReflexiveTransition at *
  obtain ⟨_, hNonRef⟩ := hPain
  exact Int.lt_irrefl (r.modelAccuracy t) (Int.lt_of_lt_of_le hNonRef hRef)

-- Stable patterns feel neutral (neither joy nor pain)
theorem stability_is_neutral (r : ReflexivePattern) (t : Time)
    (hStable : isStable r.toPatternDynamics t) :
    ¬isJoy r t ∧ ¬isPain r t := by
  constructor
  · intro hJoy
    unfold isJoy isForming isStable at *
    obtain ⟨hForm, _⟩ := hJoy
    rw [hStable] at hForm
    exact Int.lt_irrefl 0 hForm
  · intro hPain
    unfold isPain isSeparating isStable at *
    obtain ⟨hSep, _⟩ := hPain
    rw [hStable] at hSep
    exact Int.lt_irrefl 0 hSep

-- The fully disintegrated (strength = 0) can begin individuating again
theorem dissolution_enables_reindividuation (r : ReflexivePattern) (t : Time)
    (hDissolved : r.strength t = 0)
    (hReforming : r.strength (t + 1) > 0)
    (hRef : isReflexiveTransition r t) :
    isJoy r t := by
  unfold isJoy isForming delta isReflexiveTransition at *
  constructor
  · simp [hDissolved]; exact hReforming
  · exact hRef

/-!
## SUMMARY
══════════════════════════════════════════════════════════════════

PROVEN THEOREMS:
1. dynamics_trichotomy: Separation, formation, stability are exclusive
2. pain_joy_incompatible: Can't have pain and joy simultaneously (single pattern)
3. reflexivity_prevents_pain: Mindfulness prevents pain
4. suffering_implies_separation: Suffering entails separation
5. happiness_implies_formation: Happiness entails formation
6. individuation_is_joy: Individuation ↔ Joy
7. mindfulness_prevents_pain: High reflexivity blocks pain
8. stability_is_neutral: Stable patterns are neither joyful nor painful
9. dissolution_enables_reindividuation: From zero, one can begin again
10. mixed_emotions_possible: Pain + joy CAN coexist across domains
11. same_domain_no_mixed: Pain + joy CANNOT coexist in same domain

KEY INSIGHTS FORMALIZED:
- Proto-pain ← separation; Proto-joy ← formation
- Pain = unmodeled separation; Joy = modeled formation
- Suffering = cascading separation; Happiness = cascading formation
- Well-being = ONGOING INDIVIDUATION (not just formation events)
- Mindfulness (reflexivity) is protective against suffering
- MIXED EMOTIONS: Multi-domain systems enable pain/joy coexistence
  (reconciles atomic incompatibility with psychological reality)
-/

#check dynamics_trichotomy
#check pain_joy_incompatible
#check reflexivity_prevents_pain
#check individuation_is_joy
#check dissolution_enables_reindividuation
#check mixed_emotions_possible
#check same_domain_no_mixed
