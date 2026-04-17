/-
# Propositions as Sessions

Formalization of Wadler's (2012) correspondence between propositions
and sessions, building on Caires-Pfenning (2010).

## Key Correspondence

| Linear Logic      | Session Type     | Process           |
|-------------------|------------------|-------------------|
| A ⊗ B             | A ⊗ B            | x[y].(P | Q)      |
| A ⅋ B             | A ⅋ B            | x(y).P            |
| A & B             | A & B            | x.case(P, Q)      |
| A ⊕ B             | A ⊕ B            | x.inl; P          |
| !A                | !A               | !x(y).P           |
| ?A                | ?A               | ?x[y].P           |
| 1                 | end              | x[].0             |
| ⊥                 | end⊥             | x().P             |

## Main Results

- Type preservation under reduction
- Progress: well-typed processes are deadlock-free
- Cut elimination corresponds to communication

## References

- Wadler (2012): Propositions as Sessions
- Caires & Pfenning (2010): Session Types as Intuitionistic Linear Propositions
-/

import Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi.SessionTypes

namespace Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi

open SessionType

/-! ## Classical Linear Logic (CLL) Propositions

Following Wadler, we use classical linear logic for symmetric duality.
-/

/-- Classical linear logic propositions -/
inductive CLLProp where
  /-- Atomic proposition -/
  | atom : String → CLLProp
  /-- Dual of atomic -/
  | atomDual : String → CLLProp
  /-- Tensor: A ⊗ B -/
  | tensor : CLLProp → CLLProp → CLLProp
  /-- Par: A ⅋ B -/
  | par : CLLProp → CLLProp → CLLProp
  /-- With: A & B -/
  | addConj : CLLProp → CLLProp → CLLProp
  /-- Plus: A ⊕ B -/
  | addDisj : CLLProp → CLLProp → CLLProp
  /-- One: 1 -/
  | one : CLLProp
  /-- Bottom: ⊥ -/
  | bot : CLLProp
  /-- Top: ⊤ -/
  | top : CLLProp
  /-- Zero: 0 -/
  | zero : CLLProp
  /-- Of course: !A -/
  | ofCourse : CLLProp → CLLProp
  /-- Why not: ?A -/
  | whyNot : CLLProp → CLLProp
  deriving DecidableEq, Repr, Inhabited

namespace CLLProp

/-- Linear negation (duality) -/
def dual : CLLProp → CLLProp
  | .atom x => .atomDual x
  | .atomDual x => .atom x
  | .tensor a b => .par a.dual b.dual
  | .par a b => .tensor a.dual b.dual
  | .addConj a b => .addDisj a.dual b.dual
  | .addDisj a b => .addConj a.dual b.dual
  | .one => .bot
  | .bot => .one
  | .top => .zero
  | .zero => .top
  | .ofCourse a => .whyNot a.dual
  | .whyNot a => .ofCourse a.dual

/-- Duality is involutive -/
theorem dual_dual (a : CLLProp) : a.dual.dual = a := by
  induction a with
  | atom _ => rfl
  | atomDual _ => rfl
  | one => rfl
  | bot => rfl
  | top => rfl
  | zero => rfl
  | tensor a b iha ihb => simp only [dual, iha, ihb]
  | par a b iha ihb => simp only [dual, iha, ihb]
  | addConj a b iha ihb => simp only [dual, iha, ihb]
  | addDisj a b iha ihb => simp only [dual, iha, ihb]
  | ofCourse a ih => simp only [dual, ih]
  | whyNot a ih => simp only [dual, ih]

/-- No CLLProp is self-dual. Each constructor maps to a different constructor under dual. -/
theorem CLLProp.dual_ne_self (a : CLLProp) : a ≠ a.dual := by
  cases a with
  | atom _ => exact fun h => nomatch h
  | atomDual _ => exact fun h => nomatch h
  | tensor _ _ => exact fun h => nomatch h
  | par _ _ => exact fun h => nomatch h
  | addConj _ _ => exact fun h => nomatch h
  | addDisj _ _ => exact fun h => nomatch h
  | one => exact fun h => nomatch h
  | bot => exact fun h => nomatch h
  | top => exact fun h => nomatch h
  | zero => exact fun h => nomatch h
  | ofCourse _ => exact fun h => nomatch h
  | whyNot _ => exact fun h => nomatch h

instance : ToString CLLProp where
  toString p := go p
where
  go : CLLProp → String
    | .atom x => x
    | .atomDual x => s!"{x}⊥"
    | .tensor a b => s!"({go a} ⊗ {go b})"
    | .par a b => s!"({go a} ⅋ {go b})"
    | .addConj a b => s!"({go a} & {go b})"
    | .addDisj a b => s!"({go a} ⊕ {go b})"
    | .one => "1"
    | .bot => "⊥"
    | .top => "⊤"
    | .zero => "0"
    | .ofCourse a => s!"!{go a}"
    | .whyNot a => s!"?{go a}"

end CLLProp

/-! ## Typing Contexts

Linear contexts where each proposition is used exactly once.
Contexts are multisets of (channel, proposition) pairs.
-/

/-- Channel name -/
abbrev Chan := String

/-- A typing assignment: channel has type A -/
structure TypeAssign where
  chan : Chan
  prop : CLLProp
  deriving DecidableEq, Repr

/-- Typing context (linear, so multiset semantics) -/
abbrev Context := List TypeAssign

/-- Empty context -/
def Context.empty : Context := []

/-- Singleton context -/
def Context.singleton (x : Chan) (a : CLLProp) : Context := [{ chan := x, prop := a }]

/-- Context union (for tensor rule) -/
def Context.union (Γ Δ : Context) : Context := Γ ++ Δ

/-- A context is linear if each channel appears at most once -/
def Context.linear (Γ : Context) : Prop :=
  ∀ i j : Fin Γ.length, Γ[i].chan = Γ[j].chan → i = j

/-- Get all channels in a context -/
def Context.chans (Γ : Context) : List Chan := Γ.map (·.chan)

/-- Channel not in context -/
def Context.notMem (c : Chan) (Γ : Context) : Prop := c ∉ Γ.chans

/-- Two contexts are disjoint (no shared channels) -/
def Context.disjoint (Γ Δ : Context) : Prop :=
  ∀ c ∈ Γ.chans, c ∉ Δ.chans

/-- In a linear context, if a channel appears at position n, it doesn't appear before n -/
theorem Context.linear_no_dup_prefix (Γ : Context) (hlin : Γ.linear) (n : Fin Γ.length)
    (i : Fin Γ.length) (hi : i.val < n.val) : Γ[i].chan ≠ Γ[n].chan := by
  intro heq
  have := hlin i n heq
  omega

/-- Channel at end of context is not in the prefix -/
theorem Context.end_not_in_prefix (Γ : Context) (ta : TypeAssign) (hlin : (Γ ++ [ta]).linear) :
    ta.chan ∉ Γ.chans := by
  intro hmem
  simp only [Context.chans, List.mem_map] at hmem
  obtain ⟨ta', hta'Γ, hchan⟩ := hmem
  -- ta' ∈ Γ with ta'.chan = ta.chan
  -- In the linear context Γ ++ [ta], ta appears at position |Γ|
  -- ta' appears at some position i < |Γ|
  -- They have the same channel, contradicting linearity
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hta'Γ
  have hn : Γ.length < (Γ ++ [ta]).length := by simp
  have hilt : i < (Γ ++ [ta]).length := Nat.lt_of_lt_of_le hi (by simp)
  let fi : Fin (Γ ++ [ta]).length := ⟨i, hilt⟩
  let fn : Fin (Γ ++ [ta]).length := ⟨Γ.length, hn⟩
  have hget_i : (Γ ++ [ta]).get fi = Γ[i] := by simp [fi, List.getElem_append_left hi]
  have hget_n : (Γ ++ [ta]).get fn = ta := by simp [fn]
  have heq' : ((Γ ++ [ta]).get fi).chan = ((Γ ++ [ta]).get fn).chan := by
    simp only [hget_i, hget_n, hget, hchan]
  have hfin_eq := hlin fi fn heq'
  simp only [fi, fn, Fin.mk.injEq] at hfin_eq
  omega

/-! ## Processes (π-calculus with Sessions)

Based on Wadler's CP calculus.
-/

/-- Process terms -/
inductive CPProc where
  /-- Terminated process -/
  | nil : CPProc
  /-- Parallel composition: P | Q -/
  | par : CPProc → CPProc → CPProc
  /-- Output on x, bind y, continue as P | Q -/
  | out : Chan → Chan → CPProc → CPProc → CPProc
  /-- Input on x, bind y, continue as P -/
  | inp : Chan → Chan → CPProc → CPProc
  /-- Left selection on x, continue as P -/
  | inl : Chan → CPProc → CPProc
  /-- Right selection on x, continue as P -/
  | inr : Chan → CPProc → CPProc
  /-- Case on x, branches P and Q -/
  | case : Chan → CPProc → CPProc → CPProc
  /-- Empty output on x (for 1) -/
  | emptyOut : Chan → CPProc
  /-- Empty input on x, continue as P (for ⊥) -/
  | emptyInp : Chan → CPProc → CPProc
  /-- Server accept on x, bind y, continue as P -/
  | accept : Chan → Chan → CPProc → CPProc
  /-- Client request on x, bind y, continue as P -/
  | request : Chan → Chan → CPProc → CPProc
  /-- Link two channels -/
  | link : Chan → Chan → CPProc
  /-- Channel restriction (new channel) -/
  | nu : Chan → CLLProp → CPProc → CPProc
  deriving Repr, Inhabited

instance : ToString CPProc where
  toString p := go p
where
  go : CPProc → String
    | .nil => "0"
    | .par p q => s!"({go p} | {go q})"
    | .out x y p q => s!"{x}[{y}].({go p} | {go q})"
    | .inp x y p => s!"{x}({y}).{go p}"
    | .inl x p => s!"{x}.inl;{go p}"
    | .inr x p => s!"{x}.inr;{go p}"
    | .case x p q => s!"{x}.case({go p}, {go q})"
    | .emptyOut x => s!"{x}[]"
    | .emptyInp x p => s!"{x}().{go p}"
    | .accept x y p => s!"!{x}({y}).{go p}"
    | .request x y p => s!"?{x}[{y}].{go p}"
    | .link x w => s!"{x}↔{w}"
    | .nu x a p => s!"(ν{x}:{a}){go p}"

/-- Channel substitution in processes: P[y/z] replaces z with y -/
def CPProc.subst (p : CPProc) (y z : Chan) : CPProc :=
  let s := fun c => if c == z then y else c
  match p with
  | .nil => .nil
  | .par p1 p2 => .par (p1.subst y z) (p2.subst y z)
  | .out x w p1 p2 =>
    if w == z then .out (s x) w p1 (p2.subst y z)  -- w binds z in p1
    else .out (s x) (s w) (p1.subst y z) (p2.subst y z)
  | .inp x w p1 =>
    if w == z then p  -- z is bound, don't substitute in body
    else .inp (s x) w (p1.subst y z)
  | .inl x p1 => .inl (s x) (p1.subst y z)
  | .inr x p1 => .inr (s x) (p1.subst y z)
  | .case x p1 p2 => .case (s x) (p1.subst y z) (p2.subst y z)
  | .emptyOut x => .emptyOut (s x)
  | .emptyInp x p1 => .emptyInp (s x) (p1.subst y z)
  | .accept x w p1 =>
    if w == z then .accept (s x) w p1  -- z is bound
    else .accept (s x) w (p1.subst y z)
  | .request x w p1 =>
    if w == z then .request (s x) w p1  -- z is bound
    else .request (s x) w (p1.subst y z)
  | .link x w => .link (s x) (s w)
  | .nu x a p1 =>
    if x == z then p  -- z is bound by ν, don't substitute
    else .nu x a (p1.subst y z)

/-- Free channels in a process (channels mentioned that aren't bound).
    In tensor output `x[w].(P|Q)`, the channel `w` is bound (sent to partner)
    and used in P, so it's filtered from P's free channels. -/
def CPProc.freeChans : CPProc → List Chan
  | .nil => []
  | .par p1 p2 => p1.freeChans ++ p2.freeChans
  | .out x w p1 p2 => [x] ++ (p1.freeChans.filter (· != w)) ++ p2.freeChans
  | .inp x w p1 => [x] ++ (p1.freeChans.filter (· != w))
  | .inl x p1 => [x] ++ p1.freeChans
  | .inr x p1 => [x] ++ p1.freeChans
  | .case x p1 p2 => [x] ++ p1.freeChans ++ p2.freeChans
  | .emptyOut x => [x]
  | .emptyInp x p1 => [x] ++ p1.freeChans
  | .accept x w p1 => [x] ++ (p1.freeChans.filter (· != w))
  | .request x w p1 => [x] ++ (p1.freeChans.filter (· != w))
  | .link x w => [x, w]
  | .nu x _ p1 => p1.freeChans.filter (· != x)

/-- Helper: if x == y then y else x = x -/
private theorem beq_ite_self (x y : Chan) : (if x == y then y else x) = x := by
  by_cases h : x = y
  · simp [h]
  · simp [beq_eq_false_iff_ne.mpr h]

/-- Substituting a channel for itself has no effect -/
theorem CPProc.subst_self (p : CPProc) (y : Chan) : p.subst y y = p := by
  induction p with
  | nil => rfl
  | par p1 p2 ih1 ih2 => simp only [subst, ih1, ih2]
  | out x w p1 p2 ih1 ih2 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte, beq_ite_self, ih2]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1, ih2]
  | inp x w p1 ih1 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1]
  | inl x p1 ih1 => simp only [subst, beq_ite_self, ih1]
  | inr x p1 ih1 => simp only [subst, beq_ite_self, ih1]
  | case x p1 p2 ih1 ih2 => simp only [subst, beq_ite_self, ih1, ih2]
  | emptyOut x => simp only [subst, beq_ite_self]
  | emptyInp x p1 ih1 => simp only [subst, beq_ite_self, ih1]
  | accept x w p1 ih1 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte, beq_ite_self]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1]
  | request x w p1 ih1 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte, beq_ite_self]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1]
  | link x w => simp only [subst, beq_ite_self]
  | nu x a p1 ih1 =>
    simp only [subst]
    by_cases hx : x = y
    · simp only [hx, beq_self_eq_true, ↓reduceIte]
    · simp only [beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true, ↓reduceIte, ih1]

/-- Substituting a channel not free in the process has no effect -/
theorem CPProc.subst_not_free (p : CPProc) (y z : Chan) (h : z ∉ p.freeChans) :
    p.subst y z = p := by
  induction p with
  | nil => rfl
  | par p1 p2 ih1 ih2 =>
    simp only [freeChans, List.mem_append, not_or] at h
    simp only [subst, ih1 h.1, ih2 h.2]
  | out x w p1 p2 ih1 ih2 =>
    -- freeChans: [x] ++ (p1.freeChans.filter (· != w)) ++ p2.freeChans
    -- subst: if w == z then .out (s x) w p1 (p2.subst y z) else .out (s x) (s w) ...
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    -- h.1.1 : z ≠ x, h.1.2 : z ∈ p1.freeChans → z = w, h.2 : z ∉ p2.freeChans
    unfold subst
    by_cases hwz : w = z
    · -- w = z: binding shadows z in p1, only substitute in p2
      have hzx : z ≠ x := h.1.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have h2 : z ∉ p2.freeChans := h.2
      simp only [hwz, beq_self_eq_true, ↓reduceIte, hxz, Bool.false_eq_true, ih2 h2]
    · have hzx : z ≠ x := h.1.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      -- h.1.2 : z ∈ p1.freeChans → ¬z ≠ w (i.e., → z = w by double negation)
      have h1 : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.1.2 hmem)).symm
      have h2 : z ∉ p2.freeChans := h.2
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 h1, ih2 h2]
  | inp x w p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hwz : w = z
    · simp only [hwz, beq_self_eq_true, ↓reduceIte]
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      have hfree : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.2 hmem)).symm
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 hfree]
  | inl x p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h.2]
  | inr x p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h.2]
  | case x p1 p2 ih1 ih2 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    have h1 : z ∉ p1.freeChans := h.1.2
    have h2 : z ∉ p2.freeChans := h.2
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h1, ih2 h2]
  | emptyOut x =>
    unfold freeChans at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr fun heq => h heq.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte]
  | emptyInp x p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h.2]
  | accept x w p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hwz : w = z
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      simp only [hwz, beq_self_eq_true, hxz, Bool.false_eq_true, if_true, if_false]
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      have hfree : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.2 hmem)).symm
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 hfree]
  | request x w p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hwz : w = z
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      simp only [hwz, beq_self_eq_true, hxz, Bool.false_eq_true, if_true, if_false]
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      have hfree : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.2 hmem)).symm
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 hfree]
  | link x w =>
    unfold freeChans at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr fun heq => h.1 heq.symm
    have hwz : (w == z) = false := beq_eq_false_iff_ne.mpr fun heq => h.2 heq.symm
    simp only [subst, hxz, hwz, Bool.false_eq_true, ↓reduceIte]
  | nu x a p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_filter, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hxz : x = z
    · simp only [hxz, beq_self_eq_true, ↓reduceIte]
    · have hfree : z ∉ p1.freeChans := fun hmem => h hmem fun heq => hxz heq.symm
      simp only [beq_eq_false_iff_ne.mpr hxz, Bool.false_eq_true, ↓reduceIte, ih1 hfree]

/-! ## Typing Rules

These correspond to linear logic proof rules.
-/

/-- Helper to create type assignment -/
def mkAssign (x : Chan) (a : CLLProp) : TypeAssign := { chan := x, prop := a }

/-- Well-typedness judgment: Γ ⊢ P -/
inductive CPTyped : Context → CPProc → Prop where
  /-- Axiom/Link: x:A, w:A⊥ ⊢ x↔w -/
  | ax (x w : Chan) (a : CLLProp) :
      CPTyped [mkAssign x a, mkAssign w a.dual] (.link x w)

  /-- Cut: If Γ,x:A ⊢ P and Δ,x:A⊥ ⊢ Q then Γ,Δ ⊢ (νx:A)(P | Q) -/
  | cut (Γ Δ : Context) (x : Chan) (a : CLLProp) (p q : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x a]) p)
      (hq : CPTyped (Δ ++ [mkAssign x a.dual]) q) :
      CPTyped (Γ ++ Δ) (.nu x a (.par p q))

  /-- ⊗R: If Γ,y:A ⊢ P and Δ,x:B ⊢ Q then Γ,Δ,x:A⊗B ⊢ x[y].(P|Q) -/
  | tensorR (Γ Δ : Context) (x y : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign y a]) p)
      (hq : CPTyped (Δ ++ [mkAssign x b]) q) :
      CPTyped (Γ ++ Δ ++ [mkAssign x (.tensor a b)]) (.out x y p q)

  /-- ⅋R: If Γ,y:A,x:B ⊢ P then Γ,x:A⅋B ⊢ x(y).P -/
  | parR (Γ : Context) (x y : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign y a, mkAssign x b]) p) :
      CPTyped (Γ ++ [mkAssign x (.par a b)]) (.inp x y p)

  /-- &R: If Γ,x:A ⊢ P and Γ,x:B ⊢ Q then Γ,x:A&B ⊢ x.case(P,Q) -/
  | addConjR (Γ : Context) (x : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x a]) p)
      (hq : CPTyped (Γ ++ [mkAssign x b]) q) :
      CPTyped (Γ ++ [mkAssign x (.addConj a b)]) (.case x p q)

  /-- ⊕R₁: If Γ,x:A ⊢ P then Γ,x:A⊕B ⊢ x.inl;P -/
  | addDisjR1 (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x a]) p) :
      CPTyped (Γ ++ [mkAssign x (.addDisj a b)]) (.inl x p)

  /-- ⊕R₂: If Γ,x:B ⊢ P then Γ,x:A⊕B ⊢ x.inr;P -/
  | addDisjR2 (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x b]) p) :
      CPTyped (Γ ++ [mkAssign x (.addDisj a b)]) (.inr x p)

  /-- 1R: x:1 ⊢ x[] -/
  | oneR (x : Chan) :
      CPTyped [mkAssign x .one] (.emptyOut x)

  /-- ⊥R: If Γ ⊢ P then Γ,x:⊥ ⊢ x().P -/
  | botR (Γ : Context) (x : Chan) (p : CPProc)
      (hp : CPTyped Γ p) :
      CPTyped (Γ ++ [mkAssign x .bot]) (.emptyInp x p)

  /-- ⊤R: Γ,x:⊤ ⊢ anything (unused premise) -/
  | topR (Γ : Context) (x : Chan) (p : CPProc) :
      CPTyped (Γ ++ [mkAssign x .top]) p

  /-- Mix: If Γ ⊢ P and Δ ⊢ Q then Γ,Δ ⊢ P | Q
      Parallel composition with disjoint contexts (mix rule). -/
  | mix (Γ Δ : Context) (p q : CPProc)
      (hp : CPTyped Γ p)
      (hq : CPTyped Δ q) :
      CPTyped (Γ ++ Δ) (.par p q)

/-! ### Depth-Indexed Typing for Strong Induction

We define a depth-indexed version of the typing judgment for strong induction proofs.
The depth bounds the height of the derivation tree. -/

/-- Depth-indexed typing: CPTypedD n Γ p means Γ ⊢ p is derivable in at most n steps -/
inductive CPTypedD : Nat → Context → CPProc → Prop where
  | ax (x w : Chan) (a : CLLProp) :
      CPTypedD 0 [mkAssign x a, mkAssign w a.dual] (.link x w)
  | cut (n m : Nat) (Γ Δ : Context) (x : Chan) (a : CLLProp) (p q : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign x a]) p)
      (hq : CPTypedD m (Δ ++ [mkAssign x a.dual]) q) :
      CPTypedD (n + m + 1) (Γ ++ Δ) (.nu x a (.par p q))
  | tensorR (n m : Nat) (Γ Δ : Context) (x y : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign y a]) p)
      (hq : CPTypedD m (Δ ++ [mkAssign x b]) q) :
      CPTypedD (n + m + 1) (Γ ++ Δ ++ [mkAssign x (.tensor a b)]) (.out x y p q)
  | parR (n : Nat) (Γ : Context) (x y : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign y a, mkAssign x b]) p) :
      CPTypedD (n + 1) (Γ ++ [mkAssign x (.par a b)]) (.inp x y p)
  | addConjR (n m : Nat) (Γ : Context) (x : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign x a]) p)
      (hq : CPTypedD m (Γ ++ [mkAssign x b]) q) :
      CPTypedD (n + m + 1) (Γ ++ [mkAssign x (.addConj a b)]) (.case x p q)
  | addDisjR1 (n : Nat) (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign x a]) p) :
      CPTypedD (n + 1) (Γ ++ [mkAssign x (.addDisj a b)]) (.inl x p)
  | addDisjR2 (n : Nat) (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign x b]) p) :
      CPTypedD (n + 1) (Γ ++ [mkAssign x (.addDisj a b)]) (.inr x p)
  | oneR (x : Chan) :
      CPTypedD 0 [mkAssign x .one] (.emptyOut x)
  | botR (n : Nat) (Γ : Context) (x : Chan) (p : CPProc)
      (hp : CPTypedD n Γ p) :
      CPTypedD (n + 1) (Γ ++ [mkAssign x .bot]) (.emptyInp x p)
  | topR (Γ : Context) (x : Chan) (p : CPProc) :
      CPTypedD 0 (Γ ++ [mkAssign x .top]) p
  | mix (n m : Nat) (Γ Δ : Context) (p q : CPProc)
      (hp : CPTypedD n Γ p)
      (hq : CPTypedD m Δ q) :
      CPTypedD (n + m + 1) (Γ ++ Δ) (.par p q)

/-- Depth-indexed typing implies regular typing -/
theorem CPTypedD.toCPTyped : CPTypedD n Γ p → CPTyped Γ p := by
  intro h
  induction h with
  | ax x w a => exact CPTyped.ax x w a
  | cut _ _ _ _ _ _ _ _ _ _ ihp ihq => exact CPTyped.cut _ _ _ _ _ _ ihp ihq
  | tensorR _ _ _ _ _ _ _ _ _ _ _ _ ihp ihq => exact CPTyped.tensorR _ _ _ _ _ _ _ _ ihp ihq
  | parR _ _ _ _ _ _ _ _ ihp => exact CPTyped.parR _ _ _ _ _ _ ihp
  | addConjR _ _ _ _ _ _ _ _ _ _ ihp ihq => exact CPTyped.addConjR _ _ _ _ _ _ ihp ihq
  | addDisjR1 _ _ _ _ _ _ _ ihp => exact CPTyped.addDisjR1 _ _ _ _ _ ihp
  | addDisjR2 _ _ _ _ _ _ _ ihp => exact CPTyped.addDisjR2 _ _ _ _ _ ihp
  | oneR x => exact CPTyped.oneR x
  | botR _ _ _ _ _ ihp => exact CPTyped.botR _ _ _ ihp
  | topR Γ x p => exact CPTyped.topR Γ x p
  | mix _ _ _ _ _ _ _ _ ihp ihq => exact CPTyped.mix _ _ _ _ ihp ihq

/-- Regular typing implies depth-indexed typing for some depth -/
theorem CPTyped.toCPTypedD (h : CPTyped Γ p) : ∃ n, CPTypedD n Γ p := by
  induction h with
  | ax x w a => exact ⟨0, CPTypedD.ax x w a⟩
  | cut _ _ _ _ _ _ _ _ ihp ihq =>
    obtain ⟨n, hn⟩ := ihp
    obtain ⟨m, hm⟩ := ihq
    exact ⟨n + m + 1, CPTypedD.cut n m _ _ _ _ _ _ hn hm⟩
  | tensorR _ _ _ _ _ _ _ _ _ _ ihp ihq =>
    obtain ⟨n, hn⟩ := ihp
    obtain ⟨m, hm⟩ := ihq
    exact ⟨n + m + 1, CPTypedD.tensorR n m _ _ _ _ _ _ _ _ hn hm⟩
  | parR _ _ _ _ _ _ _ ihp =>
    obtain ⟨n, hn⟩ := ihp
    exact ⟨n + 1, CPTypedD.parR n _ _ _ _ _ _ hn⟩
  | addConjR _ _ _ _ _ _ _ _ ihp ihq =>
    obtain ⟨n, hn⟩ := ihp
    obtain ⟨m, hm⟩ := ihq
    exact ⟨n + m + 1, CPTypedD.addConjR n m _ _ _ _ _ _ hn hm⟩
  | addDisjR1 _ _ _ _ _ _ ihp =>
    obtain ⟨n, hn⟩ := ihp
    exact ⟨n + 1, CPTypedD.addDisjR1 n _ _ _ _ _ hn⟩
  | addDisjR2 _ _ _ _ _ _ ihp =>
    obtain ⟨n, hn⟩ := ihp
    exact ⟨n + 1, CPTypedD.addDisjR2 n _ _ _ _ _ hn⟩
  | oneR x => exact ⟨0, CPTypedD.oneR x⟩
  | botR _ _ _ _ ihp =>
    obtain ⟨n, hn⟩ := ihp
    exact ⟨n + 1, CPTypedD.botR n _ _ _ hn⟩
  | topR Γ x p => exact ⟨0, CPTypedD.topR Γ x p⟩
  | mix _ _ _ _ _ _ ihp ihq =>
    obtain ⟨n, hn⟩ := ihp
    obtain ⟨m, hm⟩ := ihq
    exact ⟨n + m + 1, CPTypedD.mix n m _ _ _ _ hn hm⟩

/-- Equivalence between depth-indexed and regular typing -/
theorem CPTyped_iff_CPTypedD : CPTyped Γ p ↔ ∃ n, CPTypedD n Γ p :=
  ⟨CPTyped.toCPTypedD, fun ⟨_, h⟩ => h.toCPTyped⟩

/-- Well-typed processes have linear contexts (each channel appears at most once).
    This is fundamental to linear logic: every channel is used exactly once.

    Note: This requires careful analysis of each typing rule. The ax rule assumes
    x ≠ w for well-formedness. The cut/tensorR/mix rules require context disjointness.
    TODO: Full proof requires formalizing these constraints. -/
theorem CPTyped.context_linear (h : CPTyped Γ p) : Γ.linear := by
  -- Full proof requires showing each typing rule preserves linearity.
  -- Key blockers:
  -- 1. ax rule: needs proof that x ≠ w (implicit in the rule but not tracked)
  -- 2. cut/tensorR/mix: need disjointness premises in the typing rules
  -- 3. topR: types any process, so Γ' could be non-linear
  -- TODO: Refactor CPTyped to include linearity/disjointness hypotheses
  sorry

/-- Free channels of a well-typed process are contained in the context.
    This is a key property of linear logic typing: every channel used in a
    process must be accounted for in the typing context.

    Note: The topR case is problematic since it types any process. We use sorry
    there, but in practice topR is used with specific well-formed processes. -/
theorem CPTyped.freeChans_subset_context (h : CPTyped Γ p) :
    ∀ c ∈ p.freeChans, ∃ ta ∈ Γ, ta.chan = c := by
  induction h with
  | ax x w a =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_cons, List.not_mem_nil, or_false] at hc
    cases hc with
    | inl hcx => exact ⟨mkAssign x a, .head _, hcx.symm⟩
    | inr hcw => exact ⟨mkAssign w a.dual, .tail _ (.head _), hcw.symm⟩
  | cut Γ' Δ' x a p q hp hq ihp ihq =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_filter, bne_iff_ne,
               CPProc.freeChans, List.mem_append] at hc
    cases hc.1 with
    | inl hcp =>
      obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append] at htaΓ
      cases htaΓ with
      | inl htaΓ' => exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      | inr htax =>
        simp only [List.mem_singleton] at htax
        rw [htax] at htac
        exact absurd htac.symm hc.2
    | inr hcq =>
      obtain ⟨ta, htaΔ, htac⟩ := ihq c hcq
      simp only [List.mem_append] at htaΔ
      cases htaΔ with
      | inl htaΔ' => exact ⟨ta, List.mem_append_right _ htaΔ', htac⟩
      | inr htax =>
        simp only [List.mem_singleton] at htax
        rw [htax] at htac
        exact absurd htac.symm hc.2
  | tensorR Γ' Δ' x y a b p q hp hq ihp ihq =>
    intro c hc
    -- freeChans of .out x y p q is now [x] ++ filter (· != y) p.freeChans ++ q.freeChans
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, bne_iff_ne, or_assoc] at hc
    -- hc : c = x ∨ (c ∈ p.freeChans ∧ c ≠ y) ∨ c ∈ q.freeChans
    rcases hc with hcx | ⟨hcp, hcney⟩ | hcq
    · exact ⟨mkAssign x (.tensor a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · -- c ∈ p.freeChans and c ≠ y
      obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      rcases htaΓ with htaΓ' | htay
      · exact ⟨ta, List.mem_append_left _ (List.mem_append_left _ htaΓ'), htac⟩
      · -- ta = mkAssign y a, so c = y, but hcney says c ≠ y - contradiction
        rw [htay] at htac
        exact absurd htac.symm hcney
    · obtain ⟨ta, htaΔ, htac⟩ := ihq c hcq
      simp only [List.mem_append, List.mem_singleton] at htaΔ
      rcases htaΔ with htaΔ' | htax
      · exact ⟨ta, List.mem_append_left _ (List.mem_append_right _ htaΔ'), htac⟩
      · rw [htax] at htac
        exact ⟨mkAssign x (.tensor a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | parR Γ' x y a b p hp ihp =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, bne_iff_ne] at hc
    rcases hc with hcx | ⟨hcp, hcney⟩
    · exact ⟨mkAssign x (.par a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at htaΓ
      rcases htaΓ with htaΓ' | htay | htax
      · exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      · rw [htay] at htac; exact absurd htac.symm hcney
      · rw [htax] at htac
        exact ⟨mkAssign x (.par a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | addConjR Γ' x a b p q hp hq ihp ihq =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               or_assoc] at hc
    rcases hc with hcx | hcp | hcq
    · exact ⟨mkAssign x (.addConj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      rcases htaΓ with htaΓ' | htax
      · exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      · rw [htax] at htac
        exact ⟨mkAssign x (.addConj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihq c hcq
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      rcases htaΓ with htaΓ' | htax
      · exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      · rw [htax] at htac
        exact ⟨mkAssign x (.addConj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | addDisjR1 Γ' x a b p hp ihp =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hcx | hcp
    · exact ⟨mkAssign x (.addDisj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      cases htaΓ with
      | inl htaΓ' => exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      | inr htax =>
        rw [htax] at htac
        exact ⟨mkAssign x (.addDisj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | addDisjR2 Γ' x a b p hp ihp =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hcx | hcp
    · exact ⟨mkAssign x (.addDisj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      simp only [List.mem_append, List.mem_singleton] at htaΓ
      cases htaΓ with
      | inl htaΓ' => exact ⟨ta, List.mem_append_left _ htaΓ', htac⟩
      | inr htax =>
        rw [htax] at htac
        exact ⟨mkAssign x (.addDisj a b), List.mem_append_right _ (List.mem_singleton.mpr rfl), htac⟩
  | oneR x =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_cons, List.not_mem_nil, or_false] at hc
    exact ⟨mkAssign x .one, List.mem_singleton.mpr rfl, hc.symm⟩
  | botR Γ' x p hp ihp =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hcx | hcp
    · exact ⟨mkAssign x .bot, List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      exact ⟨ta, List.mem_append_left _ htaΓ, htac⟩
  | topR Γ' x p =>
    -- topR types any process without constraining it, so we cannot prove
    -- that all free channels are in the context. This is a fundamental limitation.
    intro c hc
    by_cases hcx : c = x
    · exact ⟨mkAssign x .top, List.mem_append_right _ (List.mem_singleton.mpr rfl), hcx.symm⟩
    · sorry
  | mix Γ' Δ' p q hp hq ihp ihq =>
    intro c hc
    simp only [CPProc.freeChans, List.mem_append] at hc
    cases hc with
    | inl hcp =>
      obtain ⟨ta, htaΓ, htac⟩ := ihp c hcp
      exact ⟨ta, List.mem_append_left _ htaΓ, htac⟩
    | inr hcq =>
      obtain ⟨ta, htaΔ, htac⟩ := ihq c hcq
      exact ⟨ta, List.mem_append_right _ htaΔ, htac⟩

/-- Corollary: if a channel is not in any context assignment, it's not free in the process.
    Note: This relies on freeChans_subset_context which has a sorry in the topR case. -/
theorem CPTyped.not_in_context_not_free (h : CPTyped Γ p)
    (hnotctx : ∀ ta ∈ Γ, ta.chan ≠ c) : c ∉ p.freeChans := by
  intro hfree
  obtain ⟨ta, htaΓ, htac⟩ := h.freeChans_subset_context c hfree
  exact hnotctx ta htaΓ htac

/-! ## Normal Forms

A process is in normal form if it cannot reduce further. In CP calculus,
normal forms are nil or parallel compositions of normal forms. -/

/-- Process normal form predicate. A process is a normal form if it is:
    - nil (terminated)
    - par of two normal forms (parallel threads both terminated) -/
def CPProc.isNormalForm : CPProc → Prop
  | .nil => True
  | .par p q => p.isNormalForm ∧ q.isNormalForm
  | _ => False

/-- nil is a normal form -/
theorem CPProc.nil_isNormalForm : CPProc.nil.isNormalForm := trivial

/-- par of normal forms is a normal form -/
theorem CPProc.par_isNormalForm (hp : p.isNormalForm) (hq : q.isNormalForm) :
    (CPProc.par p q).isNormalForm := ⟨hp, hq⟩

/-! ## Reduction (Communication)

Process reduction corresponds to cut elimination.
-/

/-- Structural congruence for processes -/
inductive CPCong : CPProc → CPProc → Prop where
  | refl (p : CPProc) : CPCong p p
  | symm (p q : CPProc) : CPCong p q → CPCong q p
  | trans (p q r : CPProc) : CPCong p q → CPCong q r → CPCong p r
  -- Scope extrusion rules would go here

/-- One-step reduction -/
inductive CPReduce : CPProc → CPProc → Prop where
  /-- β-tensor/par: (νx:A⊗B)(x[y].(P|Q) | x(z).R) → (νy:A)(P | R[y/z]) | Q
      Principal cut for tensor ⊗ and par ⅋. The tensor side sends channel y,
      the par side receives and binds z, which gets substituted by y. -/
  | beta_tensor_par (x y z : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.tensor a b)
          (.par (.out x y p q) (.inp x z r)))
        (.par (.nu y a (.par p (r.subst y z))) q)

  /-- β-par/tensor: symmetric case -/
  | beta_par_tensor (x y z : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.par a b)
          (.par (.inp x y p) (.out x z q r)))
        (.par (.nu y a (.par p (q.subst y z))) r)

  /-- β-addDisj-l/addConj: (νx:A⊕B)(x.inl;P | x.case(Q,R)) → (νx:A)(P | Q)
      The ⊕ side selects left, the & side provides the left branch. -/
  | beta_addDisj_l (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addDisj a b)
          (.par (.inl x p) (.case x q r)))
        (.nu x a (.par p q))

  /-- β-addDisj-r/addConj: (νx:A⊕B)(x.inr;P | x.case(Q,R)) → (νx:B)(P | R) -/
  | beta_addDisj_r (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addDisj a b)
          (.par (.inr x p) (.case x q r)))
        (.nu x b (.par p r))

  /-- β-addConj-l/addDisj: (νx:A&B)(x.case(P,Q) | x.inl;R) → (νx:A)(P | R)
      Symmetric case where conjunction is on the left. -/
  | beta_addConj_l (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addConj a b)
          (.par (.case x p q) (.inl x r)))
        (.nu x a (.par p r))

  /-- β-addConj-r/addDisj: (νx:A&B)(x.case(P,Q) | x.inr;R) → (νx:B)(Q | R)
      Symmetric case where conjunction is on the left, right branch selected. -/
  | beta_addConj_r (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addConj a b)
          (.par (.case x p q) (.inr x r)))
        (.nu x b (.par q r))

  /-- β-one/bot: (νx:1)(x[] | x().P) → P
      Unit/counit interaction. -/
  | beta_one_bot (x : Chan) (p : CPProc) :
      CPReduce
        (.nu x .one (.par (.emptyOut x) (.emptyInp x p)))
        p

  /-- β-bot/one: symmetric case -/
  | beta_bot_one (x : Chan) (p : CPProc) :
      CPReduce
        (.nu x .bot (.par (.emptyInp x p) (.emptyOut x)))
        p

  /-- Congruence: reduction under restriction -/
  | cong_nu (x : Chan) (a : CLLProp) (p p' : CPProc)
      (hred : CPReduce p p') :
      CPReduce (.nu x a p) (.nu x a p')

  /-- Congruence: reduction in left of parallel -/
  | cong_par_l (p p' q : CPProc)
      (hred : CPReduce p p') :
      CPReduce (.par p q) (.par p' q)

  /-- Congruence: reduction in right of parallel -/
  | cong_par_r (p q q' : CPProc)
      (hred : CPReduce q q') :
      CPReduce (.par p q) (.par p q')

/-! ## Properties -/

/-! ### Inversion Lemmas

    These lemmas characterize the possible typing derivations for specific process forms.
    They are needed to handle dependent elimination in the principal cut cases. -/

/-- Inversion for .emptyOut: only oneR or topR can type it -/
lemma CPTyped.emptyOut_inv (Γ : Context) (x : Chan) (h : CPTyped Γ (.emptyOut x)) :
    (Γ = [mkAssign x .one]) ∨
    (∃ Γ' y, Γ = Γ' ++ [mkAssign y .top]) := by
  cases h with
  | oneR x' => left; rfl
  | topR Γ' y _ => right; exact ⟨Γ', y, rfl⟩

/-- Inversion for .emptyInp: only botR or topR can type it -/
lemma CPTyped.emptyInp_inv (Γ : Context) (x : Chan) (p : CPProc)
    (h : CPTyped Γ (.emptyInp x p)) :
    (∃ Δ, Γ = Δ ++ [mkAssign x .bot] ∧ CPTyped Δ p) ∨
    (∃ Γ' y, Γ = Γ' ++ [mkAssign y .top]) := by
  cases h with
  | botR Δ x' p' hp => left; exact ⟨Δ, rfl, hp⟩
  | topR Γ' y _ => right; exact ⟨Γ', y, rfl⟩

/-- Inversion for .out (tensor output): only tensorR or topR can type it -/
lemma CPTyped.out_inv (Γctx : Context) (x y : Chan) (p q : CPProc)
    (h : CPTyped Γctx (.out x y p q)) :
    (∃ Γ Δ a b, Γctx = Γ ++ Δ ++ [mkAssign x (.tensor a b)] ∧
                CPTyped (Γ ++ [mkAssign y a]) p ∧
                CPTyped (Δ ++ [mkAssign x b]) q) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | tensorR Γ Δ x' y' a b p' q' hp hq =>
    left; exact ⟨Γ, Δ, a, b, rfl, hp, hq⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .inp (par input): only parR or topR can type it -/
lemma CPTyped.inp_inv (Γctx : Context) (x y : Chan) (p : CPProc)
    (h : CPTyped Γctx (.inp x y p)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.par a b)] ∧
              CPTyped (Γ ++ [mkAssign y a, mkAssign x b]) p) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | parR Γ x' y' a b p' hp => left; exact ⟨Γ, a, b, rfl, hp⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .case (additive conjunction): only addConjR or topR can type it -/
lemma CPTyped.case_inv (Γctx : Context) (x : Chan) (p q : CPProc)
    (h : CPTyped Γctx (.case x p q)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.addConj a b)] ∧
              CPTyped (Γ ++ [mkAssign x a]) p ∧
              CPTyped (Γ ++ [mkAssign x b]) q) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | addConjR Γ x' a b p' q' hp hq => left; exact ⟨Γ, a, b, rfl, hp, hq⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .inl (additive left): only addDisjR1 or topR can type it -/
lemma CPTyped.inl_inv (Γctx : Context) (x : Chan) (p : CPProc)
    (h : CPTyped Γctx (.inl x p)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.addDisj a b)] ∧
              CPTyped (Γ ++ [mkAssign x a]) p) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | addDisjR1 Γ x' a b p' hp => left; exact ⟨Γ, a, b, rfl, hp⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .inr (additive right): only addDisjR2 or topR can type it -/
lemma CPTyped.inr_inv (Γctx : Context) (x : Chan) (p : CPProc)
    (h : CPTyped Γctx (.inr x p)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.addDisj a b)] ∧
              CPTyped (Γ ++ [mkAssign x b]) p) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | addDisjR2 Γ x' a b p' hp => left; exact ⟨Γ, a, b, rfl, hp⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-! ### Impossibility Lemmas for Certain Contexts

    Key insight: The only singleton contexts directly derivable (without cut/mix) are:
    - [x:1] via oneR
    - [x:⊤] via topR (with Γ = [])

    For empty context [], we'd need to cut matching singletons [x:a] and [x:a.dual].
    But 1.dual = ⊥ and ⊤.dual = 0, and neither ⊥ nor 0 is directly derivable.

    This creates mutual impossibility:
    - CPTyped [] impossible: any cut needs ⊥ or 0 singleton
    - CPTyped [x:⊥] impossible: botR needs CPTyped []
    - CPTyped [x:0] impossible: no direct rule, cut/mix recurse

    The full proof requires analyzing 2-element contexts for cuts on singleton bad contexts,
    showing that contexts like [x:⊥, y:a] are never derivable for any a (the ending type
    constrains which rules apply, and none can have ⊥ or 0 in non-final position except
    via topR which ends in ⊤). This is tracked as future work. -/

/-! ### Context-Based Inversion for Singleton Contexts

    These lemmas determine process structure from typing on singleton contexts.
    For singleton [x:τ], only specific typing rules apply based on τ. -/

/-- If CPTyped [x:1] p then p = .emptyOut x OR p is a cut/mix that can reduce.
    For the progress theorem, we need to know the process structure to identify
    principal cuts. This lemma provides the key case split. -/
lemma CPTyped.singleton_one_cases (x : Chan) (p : CPProc)
    (h : CPTyped [mkAssign x .one] p) :
    (p = .emptyOut x) ∨
    (∃ y a q, p = .nu y a q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x .one] = ctx at h
  cases h with
  | oneR x' =>
    simp only [mkAssign] at hctx
    left
    cases hctx; rfl
  | topR Γ' y p' =>
    -- Type ⊤ ≠ 1, contradiction
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact absurd this.2 (by decide)
  | ax x' w a =>
    -- Length 2 ≠ 1
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | cut Γ' Δ' x' a' p' q' _ _ =>
    -- p = .nu x' a' (.par p' q')
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    -- p = .par p' q'
    right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:⊥] p then p = .emptyInp x p' for some p', OR p is a cut/mix. -/
lemma CPTyped.singleton_bot_cases (x : Chan) (p : CPProc)
    (h : CPTyped [mkAssign x .bot] p) :
    (∃ p', p = .emptyInp x p' ∧ CPTyped [] p') ∨
    (∃ y a q, p = .nu y a q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x .bot] = ctx at h
  cases h with
  | botR Γ' x' p' hp =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ, hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, _⟩ := hAssign
    subst hΓ hchan
    left
    exact ⟨p', rfl, hp⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:A⊗B] p then p = .out x y p' q' (tensor output), OR p is a cut/mix. -/
lemma CPTyped.singleton_tensor_cases (x : Chan) (a b : CLLProp) (p : CPProc)
    (h : CPTyped [mkAssign x (.tensor a b)] p) :
    (∃ y p' q', p = .out x y p' q' ∧ CPTyped [mkAssign y a] p' ∧ CPTyped [mkAssign x b] q') ∨
    (∃ y c q, p = .nu y c q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x (.tensor a b)] = ctx at h
  cases h with
  | tensorR Γ' Δ' x' y' a' b' p' q' hp hq =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓΔ, hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan
    have hΓ'_nil := List.append_eq_nil_iff.mp hΓΔ.symm |>.1
    have hΔ'_nil := List.append_eq_nil_iff.mp hΓΔ.symm |>.2
    subst hΓ'_nil hΔ'_nil
    left
    simp only [List.nil_append] at hp hq
    exact ⟨y', p', q', rfl, hp, hq⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a' =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:A⅋B] p then p = .inp x y p' (par input), OR p is a cut/mix. -/
lemma CPTyped.singleton_par_cases (x : Chan) (a b : CLLProp) (p : CPProc)
    (h : CPTyped [mkAssign x (.par a b)] p) :
    (∃ y p', p = .inp x y p' ∧ CPTyped [mkAssign y a, mkAssign x b] p') ∨
    (∃ y c q, p = .nu y c q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x (.par a b)] = ctx at h
  cases h with
  | parR Γ' x' y' a' b' p' hp =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ', hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan hΓ'
    left
    simp only [List.nil_append] at hp
    exact ⟨y', p', rfl, hp⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a' =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:A⊕B] p then p = .inl x p' or .inr x p' (additive selection), OR p is a cut/mix. -/
lemma CPTyped.singleton_addDisj_cases (x : Chan) (a b : CLLProp) (p : CPProc)
    (h : CPTyped [mkAssign x (.addDisj a b)] p) :
    (∃ p', p = .inl x p' ∧ CPTyped [mkAssign x a] p') ∨
    (∃ p', p = .inr x p' ∧ CPTyped [mkAssign x b] p') ∨
    (∃ y c q, p = .nu y c q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x (.addDisj a b)] = ctx at h
  cases h with
  | addDisjR1 Γ' x' a' b' p' hp =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ', hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan hΓ'
    left
    simp only [List.nil_append] at hp
    exact ⟨p', rfl, hp⟩
  | addDisjR2 Γ' x' a' b' p' hp =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ', hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan hΓ'
    right; left
    simp only [List.nil_append] at hp
    exact ⟨p', rfl, hp⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a' =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:A&B] p then p = .case x p' q' (additive branching), OR p is a cut/mix. -/
lemma CPTyped.singleton_addConj_cases (x : Chan) (a b : CLLProp) (p : CPProc)
    (h : CPTyped [mkAssign x (.addConj a b)] p) :
    (∃ p' q', p = .case x p' q' ∧ CPTyped [mkAssign x a] p' ∧ CPTyped [mkAssign x b] q') ∨
    (∃ y c q, p = .nu y c q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x (.addConj a b)] = ctx at h
  cases h with
  | addConjR Γ' x' a' b' p' q' hp hq =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ', hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan hΓ'
    left
    simp only [List.nil_append] at hp hq
    exact ⟨p', q', rfl, hp, hq⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a' =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right
    exact ⟨p', q', rfl⟩


/-! ### Impossible Context Lemmas via Depth Induction

These lemmas prove that certain singleton contexts cannot be typed.
The proofs use strong induction on derivation depth via CPTypedD.

Key insight: 0 CAN appear in non-final positions (via topR's arbitrary prefix),
and even at the END in 2-element contexts (ax with a=top gives [x:top,w:0]).
But SINGLETON [x:0] is provably impossible via length/type mismatches.

The proof requires mutual analysis of singleton and 2-element contexts:
- Singleton [x:0]: cut case with a=1 produces hq:[x:0,y:bot], needs 2-element lemma
- 2-element [x:0,y:bot]: botR case has premise [x:0], needs singleton lemma

This is resolved by strong induction on derivation depth. -/

/-- Helper: No derivation produces empty context [].
    All base rules produce non-empty contexts. cut/mix need analysis. -/
private theorem CPTypedD.no_empty_context (n : Nat)
    (ih_sing : ∀ m < n, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p) :
    ∀ p, ¬ CPTypedD n [] p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p h
    generalize hctx : ([] : Context) = ctx at h
    cases h with
    | ax _ _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_cons, List.length_nil] at hlen; omega
    | oneR _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_cons, List.length_nil] at hlen; omega
    | botR _ Γ' _ _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
    | topR Γ' _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
    | tensorR _ _ _ _ _ _ _ _ _ _ _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
    | parR _ _ _ _ _ _ _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
    | addConjR _ _ _ _ _ _ _ _ _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
    | addDisjR1 _ _ _ _ _ _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
    | addDisjR2 _ _ _ _ _ _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
    | cut np nq Γ' Δ' z a _ _ hp hq =>
      -- Γ' ++ Δ' = []. So Γ' = Δ' = [].
      have hlen := congrArg List.length hctx
      simp only [List.length_append, List.length_nil] at hlen
      match Γ', Δ' with
      | [], [] =>
        simp only [List.nil_append] at hp hq
        -- hp : [z:a] singleton, hq : [z:a.dual] singleton
        cases ha : a with
        | top =>
          simp only [ha, CLLProp.dual] at hq
          exact ih_sing nq (by omega) z _ hq
        | one =>
          -- hq : [z:bot] singleton. Only botR produces this.
          simp only [ha, CLLProp.dual] at hq
          -- botR with Γ = [] needs premise at depth nq-1 with context [].
          -- By IH, [] is not derivable at depth < n.
          generalize hctx' : [mkAssign z CLLProp.bot] = ctx' at hq
          cases hq with
          | botR n' Γ' _ _ hp' =>
            -- Γ' ++ [z:bot] = [z:bot], so Γ' = []
            have hlen' := congrArg List.length hctx'
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
            match Γ' with
            | [] =>
              -- hp' : CPTypedD n' [] _
              have ih_sing' : ∀ m < n', ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
                fun m hm => ih_sing m (by omega)
              exact ih n' (by omega) ih_sing' _ hp'
            | _::_ => simp only [List.length_cons] at hlen'; omega
          | ax _ _ _ =>
            have hlen' := congrArg List.length hctx'
            simp only [List.length_cons, List.length_nil] at hlen'; omega
          | oneR _ =>
            have hprop := congrArg (·[0]?) hctx'
            simp only [List.getElem?_cons_zero] at hprop
            have hprop' := congrArg TypeAssign.prop (Option.some.inj hprop)
            simp only [mkAssign] at hprop'
            exact nomatch hprop'  -- 1 ≠ bot
          | topR Γ' _ _ =>
            have hlen' := congrArg List.length hctx'
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
            match Γ' with
            | [] =>
              simp only [List.nil_append] at hctx'
              have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
              simp only [mkAssign] at hprop
              exact nomatch hprop  -- top ≠ bot
            | _::_ => simp only [List.length_cons] at hlen'; omega
          | tensorR _ _ Γ' Δ' _ _ _ _ _ _ _ _ =>
            have hlen' := congrArg List.length hctx'
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
            match Γ', Δ' with
            | [], [] =>
              simp only [List.nil_append] at hctx'
              have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
              simp only [mkAssign] at hprop
              exact nomatch hprop  -- tensor ≠ bot
            | _, _::_ | _::_, _ => simp only [List.length_cons] at hlen'; omega
          | parR _ Γ' _ _ _ _ _ _ =>
            have hlen' := congrArg List.length hctx'
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
            match Γ' with
            | [] =>
              simp only [List.nil_append] at hctx'
              have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
              simp only [mkAssign] at hprop
              exact nomatch hprop  -- par ≠ bot
            | _::_ => simp only [List.length_cons] at hlen'; omega
          | addConjR _ _ Γ' _ _ _ _ _ _ _ =>
            have hlen' := congrArg List.length hctx'
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
            match Γ' with
            | [] =>
              simp only [List.nil_append] at hctx'
              have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
              simp only [mkAssign] at hprop
              exact nomatch hprop
            | _::_ => simp only [List.length_cons] at hlen'; omega
          | addDisjR1 _ Γ' _ _ _ _ _ | addDisjR2 _ Γ' _ _ _ _ _ =>
            have hlen' := congrArg List.length hctx'
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
            match Γ' with
            | [] =>
              simp only [List.nil_append] at hctx'
              have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
              simp only [mkAssign] at hprop
              exact nomatch hprop
            | _::_ => simp only [List.length_cons] at hlen'; omega
          | cut _ _ Γ'' Δ'' _ _ _ _ _ _ =>
            -- cut producing [z:bot] singleton: Γ'' ++ Δ'' = [z:bot], so |Γ''|+|Δ''|=1
            have hlen'' := congrArg List.length hctx'
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen''
            match Γ'', Δ'' with
            | [], [_] | [_], [] =>
              -- One premise is singleton, one has 2 elements
              -- The singleton premise needs type analysis
              sorry  -- Needs singleton type analysis
            | [], [] => simp only [List.length_nil] at hlen''; omega
            | _::_, _::_ => simp only [List.length_cons] at hlen''; omega
            | _::_::_, _ => simp only [List.length_cons] at hlen''; omega
            | _, _::_::_ => simp only [List.length_cons] at hlen''; omega
          | mix n'' m'' Γ'' Δ'' _ _ hp'' hq'' =>
            -- mix producing [z:bot] has Γ''++Δ'' = [z:bot]
            have hlen'' := congrArg List.length hctx'
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen''
            match Γ'', Δ'' with
            | [_], [] =>
              -- Δ'' = [], hq'' : [] at depth m'' < n
              have ih_sing'' : ∀ m < m'', ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
                fun m hm => ih_sing m (by omega)
              exact ih m'' (by omega) ih_sing'' _ hq''
            | [], [_] =>
              -- Γ'' = [], hp'' : [] at depth n'' < n
              have ih_sing'' : ∀ m < n'', ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
                fun m hm => ih_sing m (by omega)
              exact ih n'' (by omega) ih_sing'' _ hp''
            | [], [] => simp only [List.length_nil] at hlen''; omega
            | _::_, _::_ => simp only [List.length_cons] at hlen''; omega
            | _::_::_, _ => simp only [List.length_cons] at hlen''; omega
            | _, _::_::_ => simp only [List.length_cons] at hlen''; omega
        | _ =>
          -- For a ∉ {0, 1, top}: [z:a] not derivable as singleton
          -- Only oneR (type 1) and topR (type top) produce derivable singletons
          sorry
      | _::_, _ => simp only [List.length_cons] at hlen; omega
      | _, _::_ => simp only [List.length_cons] at hlen; omega
    | mix np nq Γ' Δ' _ _ hp hq =>
      -- Γ' ++ Δ' = []. So Γ' = Δ' = [].
      have hlen := congrArg List.length hctx
      simp only [List.length_append, List.length_nil] at hlen
      match Γ', Δ' with
      | [], [] =>
        -- Restrict ih_sing to work for depth < np
        have ih_sing' : ∀ m < np, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
          fun m hm => ih_sing m (by omega)
        exact ih np (by omega) ih_sing' _ hp
      | _::_, _ => simp only [List.length_cons] at hlen; omega
      | _, _::_ => simp only [List.length_cons] at hlen; omega

/-- Helper: No derivation produces 2-element context [x:0, y:0].
    Both elements have type zero; ax would need a=0 and a.dual=0, but 0.dual=top. -/
private theorem CPTypedD.no_two_elem_zero_zero (n : Nat)
    (ih_sing : ∀ m < n, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p) :
    ∀ x y p, ¬ CPTypedD n [mkAssign x .zero, mkAssign y .zero] p := by
  intro x y p h
  generalize hctx : [mkAssign x .zero, mkAssign y .zero] = ctx at h
  cases h with
  | ax x' w' a' =>
    -- ax produces [x':a', w':a'.dual]. For [x:0, y:0]: a'=0, a'.dual=0. But 0.dual=top.
    have heq := hctx.symm
    have h1 : mkAssign x' a' = mkAssign x .zero := by
      have := congrArg (·[0]?) heq; simp only [List.getElem?_cons_zero] at this
      exact Option.some.inj this
    have hprop1 := congrArg TypeAssign.prop h1
    simp only [mkAssign] at hprop1
    have h2 : mkAssign w' a'.dual = mkAssign y .zero := by
      have := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
      exact Option.some.inj this
    have hprop2 := congrArg TypeAssign.prop h2
    simp only [mkAssign, hprop1, CLLProp.dual] at hprop2
    exact nomatch hprop2  -- top = 0 is impossible
  | botR _ Γ' _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop  -- bot = 0 is impossible
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | topR Γ' _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop  -- top = 0 is impossible
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | oneR _ =>
    have hlen := congrArg List.length hctx.symm
    simp only [List.length_cons, List.length_nil] at hlen; omega
  | tensorR _ _ Γ' Δ' _ _ _ _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ', Δ' with
    | [], [_] | [_], [] =>
      have h2 := congrArg (·[1]?) heq
      simp only [List.nil_append, List.singleton_append, List.getElem?_cons_succ,
                 List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop  -- tensor _ _ = 0 impossible
    | [], [] => simp only [List.length_nil] at hlen; omega
    | _::_, _::_ => simp only [List.length_cons] at hlen; omega
    | _::_::_, [] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | [], _::_::_ => simp only [List.length_cons, List.length_nil] at hlen; omega
  | parR _ Γ' _ _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop  -- par _ _ = 0 impossible
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | addConjR _ _ Γ' _ _ _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | addDisjR1 _ Γ' _ _ _ _ _ | addDisjR2 _ Γ' _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | cut np nq Γ' Δ' z a _ _ hp hq =>
    -- cut produces Γ' ++ Δ' = [x:0, y:0]. Premises are Γ' ++ [z:a] and Δ' ++ [z:a.dual].
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ', hΔ : Δ' with
    | [], [_, _] =>
      -- hp : [] ++ [z:a] = [z:a] singleton. If a = 0, ih_sing applies.
      simp only [List.nil_append] at hp
      cases ha : a with
      | zero =>
        simp only [ha] at hp
        exact ih_sing np (by omega) z _ hp
      | _ => sorry  -- Complex: hq has 3 elements, need deeper analysis
    | [g], [d] =>
      -- Both premises have 2 elements: hp : [g, z:a], hq : [d, z:a.dual]
      -- From heq: g = x:0, d = y:0
      have hg : g = mkAssign x .zero := by
        have := congrArg (·[0]?) heq; simp only [List.singleton_append,
          List.getElem?_cons_zero] at this
        exact Option.some.inj this
      have hd : d = mkAssign y .zero := by
        have := congrArg (·[1]?) heq; simp only [List.singleton_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero] at this
        exact Option.some.inj this
      subst hg hd
      -- hp : CPTypedD np [x:0, z:a], hq : CPTypedD nq [y:0, z:a.dual]
      have ih_sing_np : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
        fun m hm => ih_sing m (by omega)
      have ih_sing_nq : ∀ m < nq, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
        fun m hm => ih_sing m (by omega)
      cases ha : a with
      | zero =>
        -- hp : [x:0, z:0]
        simp only [ha] at hp
        exact no_two_elem_zero_zero np ih_sing_np x z _ hp
      | top =>
        -- a.dual = 0, hq : [y:0, z:0]
        simp only [ha, CLLProp.dual] at hq
        exact no_two_elem_zero_zero nq ih_sing_nq y z _ hq
      | _ => sorry  -- one/bot need forward refs to no_two_elem_zero_one/bot (mutual recursion)
    | [_, _], [] =>
      -- hq : [] ++ [z:a.dual] = [z:a.dual] singleton. If a.dual = 0 (a = top), ih_sing applies.
      simp only [List.nil_append] at hq
      cases ha : a with
      | top =>
        simp only [ha, CLLProp.dual] at hq
        exact ih_sing nq (by omega) z _ hq
      | _ => sorry  -- Complex: hp has 3 elements
    | [], [] => simp only [List.length_nil] at hlen; omega
    | [], [_] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | [_], [] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | _::_::_::_, _ => simp only [List.length_cons] at hlen; omega
    | _, _::_::_::_ => simp only [List.length_cons] at hlen; omega
  | mix np nq Γ' Δ' _ _ hp hq =>
    -- mix produces Γ' ++ Δ' = [x:0, y:0]. Premises are Γ' and Δ'.
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ', hΔ : Δ' with
    | [g], [d] =>
      -- Both are singletons. Check if either is [_:0].
      have hg : g = mkAssign x .zero := by
        have := congrArg (·[0]?) heq; simp only [hΓ, hΔ, List.singleton_append,
          List.getElem?_cons_zero] at this
        exact Option.some.inj this
      subst hg
      exact ih_sing np (by omega) x _ hp
    | [], [_, _] =>
      -- Γ' = [], hp : []. Empty context not derivable.
      have ih_sing' : ∀ m < np, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
        fun m hm => ih_sing m (by omega)
      exact no_empty_context np ih_sing' _ hp
    | [_, _], [] =>
      -- Δ' = [], hq : []. Empty context not derivable.
      have ih_sing' : ∀ m < nq, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
        fun m hm => ih_sing m (by omega)
      exact no_empty_context nq ih_sing' _ hq
    | [], [] => simp only [List.length_nil] at hlen; omega
    | [], [_] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | [_], [] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | _::_::_::_, _ => simp only [List.length_cons] at hlen; omega
    | _, _::_::_::_ => simp only [List.length_cons] at hlen; omega
    | _::_, _::_::_ => simp only [List.length_cons] at hlen; omega
    | _::_::_, _::_ => simp only [List.length_cons] at hlen; omega

/-- Helper: No derivation produces 2-element context [x:0, y:1].
    oneR produces singleton [y:1], not 2-element. ax needs a=0, a.dual=1, but 0.dual=top. -/
private theorem CPTypedD.no_two_elem_zero_one (n : Nat)
    (ih_sing : ∀ m < n, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p) :
    ∀ x y p, ¬ CPTypedD n [mkAssign x .zero, mkAssign y .one] p := by
  intro x y p h
  generalize hctx : [mkAssign x .zero, mkAssign y .one] = ctx at h
  cases h with
  | ax x' w' a' =>
    have heq := hctx.symm
    have h1 : mkAssign x' a' = mkAssign x .zero := by
      have := congrArg (·[0]?) heq; simp only [List.getElem?_cons_zero] at this
      exact Option.some.inj this
    have hprop1 := congrArg TypeAssign.prop h1
    simp only [mkAssign] at hprop1
    have h2 : mkAssign w' a'.dual = mkAssign y .one := by
      have := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
      exact Option.some.inj this
    have hprop2 := congrArg TypeAssign.prop h2
    simp only [mkAssign, hprop1, CLLProp.dual] at hprop2
    exact nomatch hprop2  -- top = 1 impossible
  | oneR _ =>
    have hlen := congrArg List.length hctx.symm
    simp only [List.length_cons, List.length_nil] at hlen; omega
  | botR _ Γ' _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | topR Γ' _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | tensorR _ _ Γ' Δ' _ _ _ _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ', Δ' with
    | [], [_] | [_], [] =>
      have h2 := congrArg (·[1]?) heq
      simp only [List.nil_append, List.singleton_append, List.getElem?_cons_succ,
                 List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [], [] => simp only [List.length_nil] at hlen; omega
    | _::_, _::_ => simp only [List.length_cons] at hlen; omega
    | _::_::_, [] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | [], _::_::_ => simp only [List.length_cons, List.length_nil] at hlen; omega
  | parR _ Γ' _ _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | addConjR _ _ Γ' _ _ _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | addDisjR1 _ Γ' _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | addDisjR2 _ Γ' _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | cut np nq Γ' Δ' z a _ _ hp hq =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ', hΔ : Δ' with
    | [], [_, _] =>
      simp only [List.nil_append] at hp
      cases ha : a with
      | zero =>
        simp only [ha] at hp
        exact ih_sing np (by omega) z _ hp
      | _ => sorry
    | [g], [d] =>
      -- Both 2-element: hp : [g, z:a], hq : [d, z:a.dual]. g=x:0, d=y:1.
      have hg : g = mkAssign x .zero := by
        have := congrArg (·[0]?) heq; simp only [List.singleton_append,
          List.getElem?_cons_zero] at this
        exact Option.some.inj this
      have hd : d = mkAssign y .one := by
        have := congrArg (·[1]?) heq; simp only [List.singleton_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero] at this
        exact Option.some.inj this
      subst hg hd
      have ih_sing_np : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
        fun m hm => ih_sing m (by omega)
      cases ha : a with
      | zero =>
        simp only [ha] at hp
        exact no_two_elem_zero_zero np ih_sing_np x z _ hp
      | _ => sorry  -- top/one/bot/compound need mutual recursion or more helpers
    | [_, _], [] =>
      simp only [List.nil_append] at hq
      cases ha : a with
      | top =>
        simp only [ha, CLLProp.dual] at hq
        exact ih_sing nq (by omega) z _ hq
      | _ => sorry
    | [], [] => simp only [List.length_nil] at hlen; omega
    | [], [_] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | [_], [] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | _::_::_::_, _ => simp only [List.length_cons] at hlen; omega
    | _, _::_::_::_ => simp only [List.length_cons] at hlen; omega
  | mix np nq Γ' Δ' _ _ hp hq =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ', hΔ : Δ' with
    | [g], [_] =>
      have hg : g = mkAssign x .zero := by
        have := congrArg (·[0]?) heq; simp only [List.singleton_append,
          List.getElem?_cons_zero] at this
        exact Option.some.inj this
      subst hg
      exact ih_sing np (by omega) x _ hp
    | [], [_, _] =>
      have ih_sing' : ∀ m < np, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
        fun m hm => ih_sing m (by omega)
      exact no_empty_context np ih_sing' _ hp
    | [_, _], [] =>
      have ih_sing' : ∀ m < nq, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
        fun m hm => ih_sing m (by omega)
      exact no_empty_context nq ih_sing' _ hq
    | [], [] => simp only [List.length_nil] at hlen; omega
    | [], [_] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | [_], [] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | _::_::_::_, _ => simp only [List.length_cons] at hlen; omega
    | _, _::_::_::_ => simp only [List.length_cons] at hlen; omega
    | _::_, _::_::_ => simp only [List.length_cons] at hlen; omega
    | _::_::_, _::_ => simp only [List.length_cons] at hlen; omega

/-- Helper: No derivation produces 2-element context [x:0, y:bot].
    Uses the same strong induction as the singleton lemma. -/
private theorem CPTypedD.no_two_elem_zero_bot (n : Nat)
    (ih_sing : ∀ m < n, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p) :
    ∀ x y p, ¬ CPTypedD n [mkAssign x .zero, mkAssign y .bot] p := by
  intro x y p h
  generalize hctx : [mkAssign x .zero, mkAssign y .bot] = ctx at h
  cases h with
  | ax x' w' a' =>
    -- ax produces [x':a', w':a'.dual]. For [x:0, y:bot]:
    -- First: a' = 0, Second: a'.dual = bot. But 0.dual = top ≠ bot.
    have heq := hctx.symm
    have h1 : mkAssign x' a' = mkAssign x .zero := by
      have := congrArg (·[0]?) heq
      simp only [List.getElem?_cons_zero] at this
      exact Option.some.inj this
    have hprop1 := congrArg TypeAssign.prop h1
    simp only [mkAssign] at hprop1
    have h2 : mkAssign w' a'.dual = mkAssign y .bot := by
      have := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
      exact Option.some.inj this
    have hprop2 := congrArg TypeAssign.prop h2
    simp only [mkAssign, hprop1, CLLProp.dual] at hprop2
    -- hprop2 : top = bot, contradiction
    exact nomatch hprop2
  | botR n' Γ' y' p' hp' =>
    -- botR produces Γ' ++ [y':bot]. For [x:0, y:bot]: Γ' = [x:0].
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length] at hlen
    -- Γ'.length + 1 = 2, so Γ'.length = 1
    match hΓ' : Γ' with
    | [g'] =>
      simp only [hΓ', List.singleton_append] at heq
      have hg' : g' = mkAssign x .zero := by
        have := congrArg (·[0]?) heq
        simp only [List.getElem?_cons_zero] at this
        exact Option.some.inj this
      subst hg' hΓ'
      -- hp' : CPTypedD n' [mkAssign x .zero] p'
      -- By ih_sing (n' < n), contradiction.
      exact ih_sing n' (by omega) x p' hp'
    | [] => simp only [List.length] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | topR Γ' y' _ =>
    -- topR produces Γ' ++ [y':top]. Ends in top ≠ bot.
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length] at hlen
    match hΓ' : Γ' with
    | [g'] =>
      simp only [hΓ', List.singleton_append] at heq
      have h2 : mkAssign y' .top = mkAssign y .bot := by
        have := congrArg (·[1]?) heq
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
        exact Option.some.inj this
      have hprop := congrArg TypeAssign.prop h2
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length, List.nil_append] at hlen; omega
    | _::_::_ => simp only [List.length_cons, List.length_append, List.length] at hlen; omega
  | cut np nq Γ' Δ' z a _ _ hp hq =>
    -- cut produces Γ' ++ Δ' = [x:0, y:bot].
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ', hΔ : Δ' with
    | [], [_, _] =>
      simp only [List.nil_append] at hp
      cases ha : a with
      | zero =>
        simp only [ha] at hp
        exact ih_sing np (by omega) z _ hp
      | _ => sorry
    | [g], [d] =>
      -- Both 2-element: hp : [g, z:a], hq : [d, z:a.dual]. g=x:0, d=y:bot.
      have hg : g = mkAssign x .zero := by
        have := congrArg (·[0]?) heq; simp only [List.singleton_append,
          List.getElem?_cons_zero] at this
        exact Option.some.inj this
      have hd : d = mkAssign y .bot := by
        have := congrArg (·[1]?) heq; simp only [List.singleton_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero] at this
        exact Option.some.inj this
      subst hg hd
      have ih_sing_np : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
        fun m hm => ih_sing m (by omega)
      cases ha : a with
      | zero =>
        simp only [ha] at hp
        exact no_two_elem_zero_zero np ih_sing_np x z _ hp
      | _ => sorry  -- top/one/bot/compound need mutual recursion or more helpers
    | [_, _], [] =>
      simp only [List.nil_append] at hq
      cases ha : a with
      | top =>
        simp only [ha, CLLProp.dual] at hq
        exact ih_sing nq (by omega) z _ hq
      | _ => sorry
    | [], [] => simp only [List.length_nil] at hlen; omega
    | [], [_] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | [_], [] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | _::_::_::_, _ => simp only [List.length_cons] at hlen; omega
    | _, _::_::_::_ => simp only [List.length_cons] at hlen; omega
  | mix np nq Γ' Δ' _ _ hp hq =>
    -- mix produces Γ' ++ Δ' = [x:0, y:bot].
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ', hΔ : Δ' with
    | [g], [_] =>
      have hg : g = mkAssign x .zero := by
        have := congrArg (·[0]?) heq; simp only [List.singleton_append,
          List.getElem?_cons_zero] at this
        exact Option.some.inj this
      subst hg
      exact ih_sing np (by omega) x _ hp
    | [], [_, _] =>
      have ih_sing' : ∀ m < np, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
        fun m hm => ih_sing m (by omega)
      exact no_empty_context np ih_sing' _ hp
    | [_, _], [] =>
      have ih_sing' : ∀ m < nq, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p :=
        fun m hm => ih_sing m (by omega)
      exact no_empty_context nq ih_sing' _ hq
    | [], [] => simp only [List.length_nil] at hlen; omega
    | [], [_] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | [_], [] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | _::_::_::_, _ => simp only [List.length_cons] at hlen; omega
    | _, _::_::_::_ => simp only [List.length_cons] at hlen; omega
    | _::_, _::_::_ => simp only [List.length_cons] at hlen; omega
    | _::_::_, _::_ => simp only [List.length_cons] at hlen; omega
  | tensorR _ _ Γ' Δ' x' _ a b _ _ _ _ =>
    -- tensorR produces Γ' ++ Δ' ++ [x':a⊗b]. Last element has type tensor.
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    -- |Γ'| + |Δ'| + 1 = 2, so |Γ'| + |Δ'| = 1
    match hΓ : Γ', hΔ : Δ' with
    | [], [_] =>
      -- [d, x':a⊗b] = [x:0, y:bot], so a⊗b = bot - impossible
      simp only [List.nil_append, List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [_], [] =>
      -- [g, x':a⊗b] = [x:0, y:bot], so a⊗b = bot - impossible
      simp only [List.singleton_append, List.nil_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [], [] =>
      -- [x':a⊗b] has length 1 ≠ 2
      simp only [List.length_nil] at hlen; omega
    | _::_, _::_ =>
      -- |Γ'| + |Δ'| >= 2, so total >= 3 > 2
      simp only [List.length_cons] at hlen; omega
    | _::_::_, [] =>
      simp only [List.length_cons, List.length_nil] at hlen; omega
    | [], _::_::_ =>
      simp only [List.length_cons, List.length_nil] at hlen; omega
  | parR _ Γ' _ _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | addConjR _ _ Γ' _ _ _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | addDisjR1 _ Γ' _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | addDisjR2 _ Γ' _ _ _ _ _ =>
    have heq := hctx.symm
    have hlen := congrArg List.length heq
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    match hΓ : Γ' with
    | [_] =>
      simp only [List.singleton_append] at heq
      have h2 := congrArg (·[1]?) heq
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
      have hprop := congrArg TypeAssign.prop (Option.some.inj h2)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | [] => simp only [List.length_nil] at hlen; omega
    | _::_::_ => simp only [List.length_cons] at hlen; omega
  | oneR _ =>
    have hlen := congrArg List.length hctx.symm
    simp only [List.length_cons, List.length_nil] at hlen
    omega

/-- No derivation produces singleton context [x:atom s] for any atom.
    Atoms only appear via ax which produces 2-element context. -/
private theorem CPTypedD.no_singleton_atom (n : Nat)
    (ih_sing : ∀ m < n, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p) :
    ∀ s x p, ¬ CPTypedD n [mkAssign x (.atom s)] p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s x p h
    generalize hctx : [mkAssign x (.atom s)] = ctx at h
    cases h with
    | ax _ _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    | oneR _ =>
      have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx.symm)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | topR Γ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | botR _ Γ _ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | tensorR _ _ Γ Δ _ _ _ _ _ _ _ _ =>
      have hctx' := hctx.symm
      match Γ, Δ with
      | [], [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _, _::_ | _::_, _ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | parR _ Γ _ _ _ _ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | addConjR _ _ Γ _ _ _ _ _ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | addDisjR1 _ Γ _ _ _ _ _ | addDisjR2 _ Γ _ _ _ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | cut np nq Γ' Δ' z a pp qq hp hq =>
      have hGD : Γ' ++ Δ' = [mkAssign x (.atom s)] := hctx.symm
      have hlen := congrArg List.length hGD
      simp only [List.length_append, List.length_singleton] at hlen
      match Γ', Δ' with
      | [], [d] =>
        have hd : d = mkAssign x (.atom s) := by simpa using hGD
        simp only [List.nil_append] at hp
        have ih_sing_np : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
          fun m hm => ih_sing m (by omega)
        cases ha : a with
        | atom t =>
          simp only [ha] at hp
          exact ih np (by omega) ih_sing_np t z pp hp
        | zero =>
          simp only [ha] at hp
          exact ih_sing np (by omega) z pp hp
        | _ => sorry  -- atomDual, bot, top, one, compounds: need forward-defined helpers
      | [g], [] =>
        have hg : g = mkAssign x (.atom s) := by simpa using hGD
        simp only [List.nil_append] at hq
        have ih_sing_nq : ∀ m < nq, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
          fun m hm => ih_sing m (by omega)
        cases ha : a with
        | atomDual t =>
          simp only [ha, CLLProp.dual] at hq
          exact ih nq (by omega) ih_sing_nq t z qq hq
        | top =>
          simp only [ha, CLLProp.dual] at hq
          exact ih_sing nq (by omega) z qq hq
        | _ => sorry  -- atom, one, bot, zero, compounds: need forward-defined helpers or 2-elem
      | [], [] => simp only [List.length_nil] at hlen; omega
      | _::_::_, _ => simp only [List.length_cons] at hlen; omega
      | _, _::_::_ => simp only [List.length_cons] at hlen; omega
      | _::_, _::_ => simp only [List.length_cons] at hlen; omega
    | mix np nq Γ' Δ' _ _ hp hq =>
      have hGD : Γ' ++ Δ' = [mkAssign x (.atom s)] := hctx.symm
      have hlen := congrArg List.length hGD
      simp only [List.length_append, List.length_singleton] at hlen
      match Γ', Δ' with
      | [], [_] =>
        have ih_sing' : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
          fun m hm => ih_sing m (by omega)
        exact no_empty_context np ih_sing' _ hp
      | [_], [] =>
        have ih_sing' : ∀ m < nq, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
          fun m hm => ih_sing m (by omega)
        exact no_empty_context nq ih_sing' _ hq
      | [], [] => simp only [List.length_nil] at hlen; omega
      | _::_::_, _ => simp only [List.length_cons] at hlen; omega
      | _, _::_::_ => simp only [List.length_cons] at hlen; omega
      | _::_, _::_ => simp only [List.length_cons] at hlen; omega

/-- No derivation produces singleton context [x:atomDual s]. Symmetric to no_singleton_atom. -/
private theorem CPTypedD.no_singleton_atomDual (n : Nat)
    (ih_sing : ∀ m < n, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p) :
    ∀ s x p, ¬ CPTypedD n [mkAssign x (.atomDual s)] p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s x p h
    generalize hctx : [mkAssign x (.atomDual s)] = ctx at h
    cases h with
    | ax _ _ _ =>
      have hlen := congrArg List.length hctx
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    | oneR _ =>
      have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx.symm)
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | topR Γ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | botR _ Γ _ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | tensorR _ _ Γ Δ _ _ _ _ _ _ _ _ =>
      have hctx' := hctx.symm
      match Γ, Δ with
      | [], [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _, _::_ | _::_, _ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | parR _ Γ _ _ _ _ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | addConjR _ _ Γ _ _ _ _ _ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | addDisjR1 _ Γ _ _ _ _ _ | addDisjR2 _ Γ _ _ _ _ _ =>
      have hctx' := hctx.symm
      match Γ with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
    | cut np nq Γ' Δ' z a pp qq hp hq =>
      have hGD : Γ' ++ Δ' = [mkAssign x (.atomDual s)] := hctx.symm
      have hlen := congrArg List.length hGD
      simp only [List.length_append, List.length_singleton] at hlen
      match Γ', Δ' with
      | [], [d] =>
        have hd : d = mkAssign x (.atomDual s) := by simpa using hGD
        simp only [List.nil_append] at hp
        have ih_sing_np : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
          fun m hm => ih_sing m (by omega)
        cases ha : a with
        | atomDual t =>
          simp only [ha] at hp
          exact ih np (by omega) ih_sing_np t z pp hp
        | atom t =>
          simp only [ha] at hp
          exact no_singleton_atom np ih_sing_np t z pp hp
        | zero =>
          simp only [ha] at hp
          exact ih_sing np (by omega) z pp hp
        | _ => sorry  -- bot, top, one, compounds: need forward helpers
      | [g], [] =>
        have hg : g = mkAssign x (.atomDual s) := by simpa using hGD
        simp only [List.nil_append] at hq
        have ih_sing_nq : ∀ m < nq, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
          fun m hm => ih_sing m (by omega)
        cases ha : a with
        | atom t =>
          simp only [ha, CLLProp.dual] at hq
          exact ih nq (by omega) ih_sing_nq t z qq hq
        | atomDual t =>
          simp only [ha, CLLProp.dual] at hq
          exact no_singleton_atom nq ih_sing_nq t z qq hq
        | top =>
          simp only [ha, CLLProp.dual] at hq
          exact ih_sing nq (by omega) z qq hq
        | _ => sorry  -- one, zero, bot, compounds: need forward helpers
      | [], [] => simp only [List.length_nil] at hlen; omega
      | _::_::_, _ => simp only [List.length_cons] at hlen; omega
      | _, _::_::_ => simp only [List.length_cons] at hlen; omega
      | _::_, _::_ => simp only [List.length_cons] at hlen; omega
    | mix np nq Γ' Δ' _ _ hp hq =>
      have hGD : Γ' ++ Δ' = [mkAssign x (.atomDual s)] := hctx.symm
      have hlen := congrArg List.length hGD
      simp only [List.length_append, List.length_singleton] at hlen
      match Γ', Δ' with
      | [], [_] =>
        have ih_sing' : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
          fun m hm => ih_sing m (by omega)
        exact no_empty_context np ih_sing' _ hp
      | [_], [] =>
        have ih_sing' : ∀ m < nq, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
          fun m hm => ih_sing m (by omega)
        exact no_empty_context nq ih_sing' _ hq
      | [], [] => simp only [List.length_nil] at hlen; omega
      | _::_::_, _ => simp only [List.length_cons] at hlen; omega
      | _, _::_::_ => simp only [List.length_cons] at hlen; omega
      | _::_, _::_ => simp only [List.length_cons] at hlen; omega

/-- No derivation produces singleton context [x:bot].
    botR with singleton output requires [] premise, which is not derivable. -/
private theorem CPTypedD.no_singleton_bot (n : Nat)
    (ih_sing : ∀ m < n, ∀ x p, ¬ CPTypedD m [mkAssign x .zero] p) :
    ∀ x p, ¬ CPTypedD n [mkAssign x .bot] p := by
  intro x p h
  generalize hctx : [mkAssign x .bot] = ctx at h
  cases h with
  | ax _ _ _ =>
    have hlen := congrArg List.length hctx
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  | oneR _ =>
    have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx.symm)
    simp only [mkAssign] at hprop
    exact nomatch hprop
  | topR Γ _ _ =>
    have hctx' := hctx.symm
    match Γ with
    | [] =>
      simp only [List.nil_append] at hctx'
      have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | _::_ =>
      have hlen := congrArg List.length hctx'
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | botR np Γ _ pp hp =>
    have hctx' := hctx.symm
    match Γ with
    | [] =>
      -- hp : CPTypedD np [] pp. Empty context not derivable!
      simp only [List.nil_append] at hctx' hp
      have ih_sing' : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
        fun m hm => ih_sing m (by omega)
      exact no_empty_context np ih_sing' pp hp
    | _::_ =>
      have hlen := congrArg List.length hctx'
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | tensorR _ _ Γ Δ _ _ _ _ _ _ _ _ =>
    have hctx' := hctx.symm
    match Γ, Δ with
    | [], [] =>
      simp only [List.nil_append] at hctx'
      have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | _, _::_ | _::_, _ =>
      have hlen := congrArg List.length hctx'
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | parR _ Γ _ _ _ _ _ _ =>
    have hctx' := hctx.symm
    match Γ with
    | [] =>
      simp only [List.nil_append] at hctx'
      have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | _::_ =>
      have hlen := congrArg List.length hctx'
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | addConjR _ _ Γ _ _ _ _ _ _ _ =>
    have hctx' := hctx.symm
    match Γ with
    | [] =>
      simp only [List.nil_append] at hctx'
      have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | _::_ =>
      have hlen := congrArg List.length hctx'
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | addDisjR1 _ Γ _ _ _ _ _ | addDisjR2 _ Γ _ _ _ _ _ =>
    have hctx' := hctx.symm
    match Γ with
    | [] =>
      simp only [List.nil_append] at hctx'
      have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | _::_ =>
      have hlen := congrArg List.length hctx'
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
  | cut np nq Γ' Δ' z a pp qq hp hq =>
    have hGD : Γ' ++ Δ' = [mkAssign x .bot] := hctx.symm
    have hlen := congrArg List.length hGD
    simp only [List.length_append, List.length_singleton] at hlen
    match Γ', Δ' with
    | [], [_] =>
      simp only [List.nil_append] at hp
      have ih_sing_np : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
        fun m hm => ih_sing m (by omega)
      cases ha : a with
      | zero =>
        simp only [ha] at hp
        exact ih_sing np (by omega) z pp hp
      | bot =>
        simp only [ha] at hp
        exact no_singleton_bot np ih_sing_np z pp hp
      | atom t =>
        simp only [ha] at hp
        exact no_singleton_atom np ih_sing_np t z pp hp
      | atomDual t =>
        simp only [ha] at hp
        exact no_singleton_atomDual np ih_sing_np t z pp hp
      | _ => sorry  -- top, one, compounds: hp may be derivable, need 2-elem for hq
    | [_], [] =>
      simp only [List.nil_append] at hq
      have ih_sing_nq : ∀ m < nq, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
        fun m hm => ih_sing m (by omega)
      cases ha : a with
      | top =>
        simp only [ha, CLLProp.dual] at hq
        exact ih_sing nq (by omega) z qq hq
      | one =>
        simp only [ha, CLLProp.dual] at hq
        exact no_singleton_bot nq ih_sing_nq z qq hq
      | atom t =>
        simp only [ha, CLLProp.dual] at hq
        exact no_singleton_atomDual nq ih_sing_nq t z qq hq
      | atomDual t =>
        simp only [ha, CLLProp.dual] at hq
        exact no_singleton_atom nq ih_sing_nq t z qq hq
      | _ => sorry  -- zero, bot, compounds: hq may be derivable
    | [], [] => simp only [List.length_nil] at hlen; omega
    | _::_::_, _ => simp only [List.length_cons] at hlen; omega
    | _, _::_::_ => simp only [List.length_cons] at hlen; omega
    | _::_, _::_ => simp only [List.length_cons] at hlen; omega
  | mix np nq Γ' Δ' _ _ hp hq =>
    have hGD : Γ' ++ Δ' = [mkAssign x .bot] := hctx.symm
    have hlen := congrArg List.length hGD
    simp only [List.length_append, List.length_singleton] at hlen
    match Γ', Δ' with
    | [], [_] =>
      have ih_sing' : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
        fun m hm => ih_sing m (by omega)
      exact no_empty_context np ih_sing' _ hp
    | [_], [] =>
      have ih_sing' : ∀ m < nq, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
        fun m hm => ih_sing m (by omega)
      exact no_empty_context nq ih_sing' _ hq
    | [], [] => simp only [List.length_nil] at hlen; omega
    | _::_::_, _ => simp only [List.length_cons] at hlen; omega
    | _, _::_::_ => simp only [List.length_cons] at hlen; omega
    | _::_, _::_ => simp only [List.length_cons] at hlen; omega

/-- No derivation produces singleton context [x:0].
    Zero is the additive false with no introduction rule. -/
private theorem CPTypedD.no_singleton_zero (n : Nat) :
    forall x p, Not (CPTypedD n [mkAssign x .zero] p) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x p h
    generalize hctx : [mkAssign x .zero] = ctx at h
    cases h with
    | ax x' w a =>
      -- ax produces [x':a, w:a.dual], length 2 != 1
      have hlen := congrArg List.length hctx
      simp at hlen
    | cut np nq G' D' y a pp qq hp hq =>
      -- cut produces G' ++ D' = [mkAssign x .zero] (singleton)
      have hGD : G' ++ D' = [mkAssign x .zero] := hctx.symm
      have hlen := congrArg List.length hGD
      simp only [List.length_append, List.length_singleton] at hlen
      -- |G'| + |D'| = 1, so one is [] and other is singleton
      match G', D' with
      | [], [d] =>
        -- G' = [], D' = [d] where d = mkAssign x .zero
        have hd : d = mkAssign x .zero := by simpa using hGD
        simp only [List.nil_append] at hp
        -- hp : CPTypedD np [mkAssign y a] pp
        -- For hp to be derivable singleton, a ∈ {0, 1, top}.
        -- a = 0: IH. a = 1: oneR. a = top: topR.
        cases ha : a with
        | zero =>
          simp only [ha] at hp
          exact ih np (by omega) y pp hp
        | top =>
          -- a = top, hp : [y:top] derivable via topR.
          -- hq : D' ++ [y:a.dual] = [x:0] ++ [y:0] = [x:0, y:0]
          -- Need to show [x:0, y:0] not derivable.
          simp only [ha, CLLProp.dual] at hq
          subst hd
          -- hq : CPTypedD nq [x:0, y:0]
          exact no_two_elem_zero_zero nq (fun m hm x' p' => ih m (by omega) x' p') x y qq hq
        | one =>
          -- a = 1, hp : [y:1] derivable via oneR.
          -- hq : [x:0, y:bot]. Need to show this not derivable.
          simp only [ha, CLLProp.dual] at hq
          subst hd
          -- hq : CPTypedD nq [mkAssign x .zero, mkAssign y .bot] qq
          -- Use helper with restricted IH (nq < n from cut structure)
          exact no_two_elem_zero_bot nq (fun m hm x' p' => ih m (by omega) x' p') x y qq hq
        | bot =>
          -- a = bot. hp : [y:bot] requires botR with empty prefix, which needs [] derivable.
          -- hq : [x:0, y:1]. Let's show this is not derivable.
          simp only [ha, CLLProp.dual] at hq
          subst hd
          -- hq : CPTypedD nq [mkAssign x .zero, mkAssign y .one] qq
          exact no_two_elem_zero_one nq (fun m hm x' p' => ih m (by omega) x' p') x y qq hq
        | tensor _ _ | par _ _ | addConj _ _ | addDisj _ _ | ofCourse _ | whyNot _ =>
          -- Compound types: the corresponding rule produces singleton only with empty prefix,
          -- but the type at the end would be compound ≠ 0.
          -- No rule produces singleton [y:compound_type] directly.
          sorry  -- Exotic cases: compound type singletons
        | atom t =>
          -- hp : [y:atom t] singleton. Use no_singleton_atom.
          simp only [ha] at hp
          have ih_sing_np : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
            fun m hm => ih m (by omega)
          exact no_singleton_atom np ih_sing_np t y pp hp
        | atomDual t =>
          -- hp : [y:atomDual t] singleton. Use no_singleton_atomDual.
          simp only [ha] at hp
          have ih_sing_np : ∀ m < np, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
            fun m hm => ih m (by omega)
          exact no_singleton_atomDual np ih_sing_np t y pp hp
      | [g], [] =>
        -- G' = [g], D' = []
        have hg : g = mkAssign x .zero := by simpa using hGD
        simp only [List.nil_append] at hq
        -- hq : CPTypedD nq [mkAssign y a.dual] qq
        -- For hq to be derivable singleton, a.dual ∈ {0, 1, top}.
        -- a.dual = 0 ⟺ a = top: IH. a.dual = 1 ⟺ a = bot. a.dual = top ⟺ a = 0.
        cases ha : a with
        | top =>
          simp only [ha, CLLProp.dual] at hq
          exact ih nq (by omega) y qq hq
        | zero =>
          -- a = 0, a.dual = top. hq : [y:top] derivable via topR.
          -- hp : [x:0, y:0]. Need to show this not derivable.
          simp only [ha, CLLProp.dual] at hp
          subst hg
          exact no_two_elem_zero_zero np (fun m hm x' p' => ih m (by omega) x' p') x y pp hp
        | bot =>
          -- a = bot, a.dual = 1. hq : [y:1] derivable via oneR.
          -- hp : [x:0, y:bot]. Need to show this not derivable.
          simp only [ha, CLLProp.dual] at hq hp
          subst hg
          -- hp : CPTypedD np [mkAssign x .zero, mkAssign y .bot] pp
          exact no_two_elem_zero_bot np (fun m hm x' p' => ih m (by omega) x' p') x y pp hp
        | one =>
          -- a = 1, a.dual = bot. hq : [y:bot] singleton.
          -- hp : [x:0, y:1]. Need to show this not derivable.
          simp only [ha, CLLProp.dual] at hp hq
          subst hg
          exact no_two_elem_zero_one np (fun m hm x' p' => ih m (by omega) x' p') x y pp hp
        | tensor _ _ | par _ _ | addConj _ _ | addDisj _ _ | ofCourse _ | whyNot _ =>
          -- a.dual is compound. hq : [y:a.dual] singleton not derivable.
          sorry  -- Exotic cases
        | atom t =>
          -- a = atom t, a.dual = atomDual t. hq : [y:atomDual t] singleton.
          simp only [ha, CLLProp.dual] at hq
          have ih_sing_nq : ∀ m < nq, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
            fun m hm => ih m (by omega)
          exact no_singleton_atomDual nq ih_sing_nq t y qq hq
        | atomDual t =>
          -- a = atomDual t, a.dual = atom t. hq : [y:atom t] singleton.
          simp only [ha, CLLProp.dual] at hq
          have ih_sing_nq : ∀ m < nq, ∀ x' p', ¬ CPTypedD m [mkAssign x' .zero] p' :=
            fun m hm => ih m (by omega)
          exact no_singleton_atom nq ih_sing_nq t y qq hq
      | [], [] => simp at hlen
      | _::_::_, _ => simp only [List.length_cons] at hlen; omega
      | _, _::_::_ => simp only [List.length_cons] at hlen; omega
      | _::_, _::_ => simp only [List.length_cons] at hlen; omega
    | tensorR np nq G' D' x' y' a b pp qq hp hq =>
      -- tensorR produces G' ++ D' ++ [x':a⊗b], length >= 1. But RHS is [x:0], length 1.
      -- If equal, last element types must match: a⊗b = 0, impossible.
      have hctx' : G' ++ D' ++ [mkAssign x' (.tensor a b)] = [mkAssign x .zero] := hctx.symm
      match G', D' with
      | [], [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _, _::_ | _::_, _ =>
        have hlen := congrArg List.length hctx'
        simp only [List.length_append, List.length] at hlen
        omega
    | parR np G' x' y' a b pp hp =>
      have hctx' : G' ++ [mkAssign x' (.par a b)] = [mkAssign x .zero] := hctx.symm
      match G' with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp at hlen
    | addConjR np nq G' x' a b pp qq hp hq =>
      have hctx' : G' ++ [mkAssign x' (.addConj a b)] = [mkAssign x .zero] := hctx.symm
      match G' with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp at hlen
    | addDisjR1 np G' x' a b pp hp =>
      have hctx' : G' ++ [mkAssign x' (.addDisj a b)] = [mkAssign x .zero] := hctx.symm
      match G' with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp at hlen
    | addDisjR2 np G' x' a b pp hp =>
      have hctx' : G' ++ [mkAssign x' (.addDisj a b)] = [mkAssign x .zero] := hctx.symm
      match G' with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp at hlen
    | oneR x' =>
      have hctx' : [mkAssign x' .one] = [mkAssign x .zero] := hctx.symm
      have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
      simp only [mkAssign] at hprop
      exact nomatch hprop
    | botR np G' x' pp hp =>
      have hctx' : G' ++ [mkAssign x' .bot] = [mkAssign x .zero] := hctx.symm
      match G' with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp at hlen
    | topR G' x' pp =>
      have hctx' : G' ++ [mkAssign x' .top] = [mkAssign x .zero] := hctx.symm
      match G' with
      | [] =>
        simp only [List.nil_append] at hctx'
        have hprop := congrArg TypeAssign.prop (List.singleton_injective hctx')
        simp only [mkAssign] at hprop
        exact nomatch hprop
      | _::_ =>
        have hlen := congrArg List.length hctx'
        simp at hlen
    | mix np nq G' D' pp qq hp hq =>
      have hGD : G' ++ D' = [mkAssign x .zero] := hctx.symm
      have hlen := congrArg List.length hGD
      simp only [List.length_append, List.length_singleton] at hlen
      match G', D' with
      | [], [d] =>
        have hd : d = mkAssign x .zero := by simpa using hGD
        subst hd
        exact ih nq (by omega) x qq hq
      | [g], [] =>
        have hg : g = mkAssign x .zero := by simpa using hGD
        subst hg
        exact ih np (by omega) x pp hp
      | [], [] => simp at hlen
      | _::_::_, _ => simp only [List.length_cons] at hlen; omega
      | _, _::_::_ => simp only [List.length_cons] at hlen; omega
      | _::_, _::_ => simp only [List.length_cons] at hlen; omega

/-- No typing rule produces singleton context with type zero (0).
    Zero is the additive unit with no introduction rule. -/
lemma CPTyped.singleton_zero_impossible (x : Chan) (p : CPProc)
    (h : CPTyped [mkAssign x .zero] p) : False := by
  obtain ⟨n, hn⟩ := h.toCPTypedD
  exact CPTypedD.no_singleton_zero n x p hn

/-- Auxiliary: old proof structure preserved for reference.
    The cut case requires showing [x:0] cannot appear in ANY position in a derivable context.
    Key insight: no typing rule introduces 0 into the context at any position. -/
private lemma singleton_zero_aux (x : Chan) (p : CPProc)
    (h : CPTyped [mkAssign x .zero] p) : False := by
  generalize hctx : [mkAssign x .zero] = ctx at h
  cases h with
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' hp hq =>
    -- Context Γ' ++ Δ' = [x:0]. Requires mutual impossibility proof.
    -- INTRODUCES zero in the context, but no such rule exists.
    -- Strong induction on derivation depth would prove this.
    sorry
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' hp hq =>
    sorry

/-- No typing rule produces singleton context with atom type.
    Atoms have no introduction rule in CLL. -/
lemma CPTyped.singleton_atom_impossible (x : Chan) (τ : String) (p : CPProc)
    (h : CPTyped [mkAssign x (.atom τ)] p) : False := by
  generalize hctx : [mkAssign x (.atom τ)] = ctx at h
  cases h with
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' hp hq => sorry
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' hp hq => sorry

/-- No typing rule produces singleton context with atomDual type. -/
lemma CPTyped.singleton_atomDual_impossible (x : Chan) (τ : String) (p : CPProc)
    (h : CPTyped [mkAssign x (.atomDual τ)] p) : False := by
  generalize hctx : [mkAssign x (.atomDual τ)] = ctx at h
  cases h with
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' hp hq => sorry
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' hp hq => sorry

/-- Helper: substitute channel in context assignment list -/
def Context.substChan (ctx : Context) (y z : Chan) : Context :=
  ctx.map fun a => ⟨if a.chan == z then y else a.chan, a.prop⟩

/-- Channel substitution preserves typing (renaming lemma).
    If Γ, z:A ⊢ P and y is fresh, then Γ, y:A ⊢ P[y/z].

    This is a key lemma for cut elimination in CLL / session types.
    The proof is by induction on the typing derivation.

    Preconditions:
    - y fresh in Γ (doesn't appear)
    - z fresh in Γ (linearity: z only appears in the final position) -/
theorem CPTyped.subst_typing (Γ : Context) (y z : Chan) (a : CLLProp) (p : CPProc)
    (h : CPTyped (Γ ++ [mkAssign z a]) p)
    (hyfresh : ∀ ta ∈ Γ, ta.chan ≠ y)
    (hzfresh : ∀ ta ∈ Γ, ta.chan ≠ z) :
    CPTyped (Γ ++ [mkAssign y a]) (p.subst y z) := by
  -- Handle trivial case where y = z (substitution is identity)
  by_cases hyz : y = z
  · rw [hyz, CPProc.subst_self]; exact h
  -- The key insight is that for z to be the typed channel in context Γ ++ [z:a],
  -- the typing derivation must end with a rule that provides that channel.
  -- We generalize z and a so the IH applies at different types in rule premises.
  generalize hctx : Γ ++ [mkAssign z a] = ctx at h
  induction h generalizing Γ z a with
  | ax x w a' =>
    -- ax gives context [x:a', w:a'.dual]
    -- This must equal Γ ++ [z:a], so z=w, a=a'.dual, and Γ=[x:a']
    simp only [CPProc.subst]
    -- Context equality: [mkAssign x a', mkAssign w a'.dual] = Γ ++ [mkAssign z a]
    -- This forces Γ = [mkAssign x a'], z = w, a = a'.dual
    cases Γ with
    | nil =>
      -- Γ = [], so [mkAssign z a] = [mkAssign x a', mkAssign w a'.dual]
      simp only [List.nil_append] at hctx
      -- Length 1 ≠ length 2, contradiction
      have hlen := congrArg List.length hctx
      simp at hlen
    | cons hd tl =>
      cases tl with
      | nil =>
        -- Γ = [hd], context is [hd, mkAssign z a] = [mkAssign x a', mkAssign w a'.dual]
        simp only [List.cons_append, List.nil_append] at hctx
        have h1 := List.cons.inj hctx
        have h2 := List.cons.inj h1.2
        -- h1.1 : hd = mkAssign x a'
        -- h2.1 : mkAssign z a = mkAssign w a'.dual
        have hd_chan : hd.chan = x := by rw [h1.1]; rfl
        have hd_prop : hd.prop = a' := by rw [h1.1]; rfl
        have z_eq_w : z = w := congrArg TypeAssign.chan h2.1
        have a_eq : a = a'.dual := congrArg TypeAssign.prop h2.1
        -- After subst: the goal involves substituting y for z in .link x w
        -- .link x w becomes .link (if x == z then y else x) (if w == z then y else w)
        -- Since z = w, this is .link (if x == w then y else x) y
        rw [z_eq_w]
        simp only [beq_self_eq_true, ↓reduceIte]
        -- Now (if x == w then y else x)
        by_cases hxw : x = w
        · -- x = w: impossible by linearity (z appears twice in original context)
          -- If x = w, then z = w = x, so hd.chan = x = z
          -- But hd ∈ Γ and hzfresh says channels in Γ ≠ z. Contradiction.
          have hxz : x = z := hxw.trans z_eq_w.symm
          have hd_in_Γ : hd ∈ [hd] := List.mem_singleton_self hd
          have := hzfresh hd hd_in_Γ
          rw [hd_chan, hxz] at this
          exact absurd rfl this
        · -- x ≠ w: normal case
          have hne : (x == w) = false := beq_eq_false_iff_ne.mpr hxw
          simp only [hne]
          -- Goal: CPTyped ([hd] ++ [mkAssign y a'.dual]) (.link x y)
          -- Context is [mkAssign x a', mkAssign y a'.dual]
          have hhd : hd = mkAssign x a' := by
            cases hd; simp only [mkAssign] at *; congr
          rw [hhd, a_eq]
          exact CPTyped.ax x y a'
      | cons hd2 tl2 =>
        -- Γ has at least 2 elements, but ax context has exactly 2
        simp only [List.cons_append] at hctx
        have hlen := congrArg List.length hctx
        simp at hlen
  | cut Γ' Δ' x' a' p' q' hp hq ihp ihq =>
    -- cut produces context Γ' ++ Δ' (x' is the cut channel, not in conclusion)
    -- hctx: Γ ++ [z:a] = Γ' ++ Δ'. So z:a is at the end of Γ' ++ Δ'.
    simp only [CPProc.subst]
    -- STRUCTURAL ISSUE: The IH expects context ending with [z:a], but cut premises
    -- have form Γ' ++ [x':a'] and Δ' ++ [x':a'.dual]. Channel z may be buried inside
    -- Γ' or Δ', not at the end after x'. This requires either:
    -- 1. A more general renaming lemma for arbitrary channel positions, or
    -- 2. Commutation lemmas to swap channel positions in context
    -- For now, use sorry and document the structural gap.
    sorry
  | tensorR Γ' Δ' x' y' a' b' p' q' hp hq ihp ihq =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ Δ' ++ [mkAssign x' (a'.tensor b')]
    -- By list equality, the last elements must match: z = x', a = a'.tensor b'
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' ++ Δ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.tensor b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    -- After subst: x' → z, Γ → Γ' ++ Δ', a → a'.tensor b'
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Goal: CPTyped ((Γ' ++ Δ') ++ [mkAssign y (a'.tensor b')])
    --         (if (y' == z) then .out y y' p' (q'.subst y z) else .out y y' (p'.subst y z) (q'.subst y z))
    by_cases hy'z : y' = z
    · -- y' = z: the output's bound variable happens to equal the substituted channel.
      -- subst's `.out` clause uses `if w == z then .out (s x) w p1 (p2.subst y z)`, so
      -- p' is NOT substituted (z is bound in p') and the outer x' becomes y.
      -- After y' = z: hp : CPTyped (Γ' ++ [mkAssign z a']) p' which matches tensorR's
      -- bound-side premise directly, and ihq discharges the outer side.
      -- `subst hzy'` with `hzy' : z = y'` eliminates the RHS free var y',
      -- replacing every y' with z. So after subst, hp : CPTyped (Γ' ++ [mkAssign z a']) p'.
      have hzy' : z = y' := hy'z.symm
      subst hzy'
      simp only [beq_self_eq_true, ↓reduceIte]
      have hyfreshΔ : ∀ ta ∈ Δ', ta.chan ≠ y := fun ta hta =>
        hyfresh ta (List.mem_append_right Γ' hta)
      have hzfreshΔ : ∀ ta ∈ Δ', ta.chan ≠ z := fun ta hta =>
        hzfresh ta (List.mem_append_right Γ' hta)
      have hIHq := ihq Δ' z b' hyfreshΔ hzfreshΔ hyz rfl
      -- hIHq : CPTyped (Δ' ++ [mkAssign y b']) (q'.subst y z)
      -- Apply tensorR with outer channel y, bound channel z:
      --   hp : CPTyped (Γ' ++ [mkAssign z a']) p'
      --   hIHq : CPTyped (Δ' ++ [mkAssign y b']) (q'.subst y z)
      exact CPTyped.tensorR Γ' Δ' y z a' b' p' (q'.subst y z) hp hIHq
    · -- y' ≠ z: normal case
      have hne : (y' == z) = false := beq_eq_false_iff_ne.mpr hy'z
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      -- Goal: CPTyped ((Γ' ++ Δ') ++ [mkAssign y (a'.tensor b')]) (.out y y' (p'.subst y z) (q'.subst y z))
      -- For tensorR with outer channel y, bound channel y', we need:
      --   (1) CPTyped (Γ' ++ [mkAssign y' a']) (p'.subst y z)
      --   (2) CPTyped (Δ' ++ [mkAssign y b']) (q'.subst y z)
      -- For (2): ihq applies directly
      have hyfreshΔ : ∀ ta ∈ Δ', ta.chan ≠ y := fun ta hta =>
        hyfresh ta (List.mem_append_right Γ' hta)
      have hzfreshΔ : ∀ ta ∈ Δ', ta.chan ≠ z := fun ta hta =>
        hzfresh ta (List.mem_append_right Γ' hta)
      have hIHq := ihq Δ' z b' hyfreshΔ hzfreshΔ hyz rfl
      -- hIHq : CPTyped (Δ' ++ [mkAssign y b']) (q'.subst y z)
      -- For (1): z is not in Γ' ++ [mkAssign y' a'], so p'.subst y z = p'
      -- z is only at the end of the original context, not in Γ' or Δ' proper
      -- Since hy'z : y' ≠ z, we need z ∉ Γ'
      -- The original context was Γ' ++ Δ' ++ [z:...], so z only appears at the end
      -- By linear structure, z ∉ Γ' and z ∉ Δ' (z is the suffix, not in prefix)
      -- We derive: z not in hp's context Γ' ++ [y':a']
      have hz_not_in_hp_ctx : ∀ ta ∈ Γ' ++ [mkAssign y' a'], ta.chan ≠ z := by
        intro ta hta
        simp only [List.mem_append, List.mem_singleton] at hta
        cases hta with
        | inl hΓ' =>
          -- ta ∈ Γ' ⊆ Γ' ++ Δ' = Γ, so hzfresh applies
          exact hzfresh ta (List.mem_append_left Δ' hΓ')
        | inr heq =>
          rw [heq]; simp only [mkAssign]
          exact hy'z
      have hp' := CPTyped.not_in_context_not_free hp hz_not_in_hp_ctx
      have hp_subst : p'.subst y z = p' := CPProc.subst_not_free p' y z hp'
      rw [hp_subst]
      exact CPTyped.tensorR Γ' Δ' y y' a' b' p' (q'.subst y z) hp hIHq
  | parR Γ' x' y' a' b' p' hp ihp =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ [mkAssign x' (a'.par b')]
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.par b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    -- After subst: x' becomes z, Γ' becomes Γ
    -- hp : CPTyped (Γ ++ [mkAssign y' a', mkAssign z b']) p'
    -- Goal: CPTyped (Γ ++ [mkAssign y (a'.par b')]) (if (y' == z) then .inp z y' p' else .inp y y' (p'.subst y z))
    by_cases hy'z : y' = z
    · -- y' = z: impossible by linearity - hp's context becomes Γ ++ [z:a', z:b']
      -- which has z appearing twice, contradicting CPTyped.context_linear.
      -- `subst hzy'` with `hzy' : z = y'` eliminates y', replacing every y' with z.
      exfalso
      have hzy' : z = y' := hy'z.symm
      subst hzy'
      have hlin := hp.context_linear
      -- hlin : (Γ ++ [mkAssign z a', mkAssign z b']).linear
      -- Reassociate: Γ ++ [z:a', z:b'] = (Γ ++ [z:a']) ++ [z:b']
      have hrw : Γ ++ [mkAssign z a', mkAssign z b']
               = (Γ ++ [mkAssign z a']) ++ [mkAssign z b'] := by
        rw [List.append_assoc]; rfl
      rw [hrw] at hlin
      have hend := Context.end_not_in_prefix (Γ ++ [mkAssign z a']) (mkAssign z b') hlin
      -- hend : (mkAssign z b').chan ∉ (Γ ++ [mkAssign z a']).chans
      -- But z = (mkAssign z b').chan = (mkAssign z a').chan is in the prefix.
      apply hend
      simp [Context.chans, mkAssign]
    · -- y' ≠ z: normal case
      have hne : (y' == z) = false := beq_eq_false_iff_ne.mpr hy'z
      simp only [hne, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, ↓reduceIte]
      -- Goal: CPTyped (Γ ++ [mkAssign y (a'.par b')]) (.inp y y' (p'.subst y z))
      -- TODO: Need y ≠ y' to prove freshness for IH. This requires strengthening
      -- the theorem's freshness hypothesis to cover bound variables in derivation.
      sorry
  | addConjR Γ' x' a' b' p' q' hp hq ihp ihq =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ [mkAssign x' (a'.addConj b')]
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.addConj b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Apply addConjR with both IH results
    have hIHp := ihp Γ z a' hyfresh hzfresh hyz rfl
    have hIHq := ihq Γ z b' hyfresh hzfresh hyz rfl
    exact CPTyped.addConjR Γ y a' b' (p'.subst y z) (q'.subst y z) hIHp hIHq
  | addDisjR1 Γ' x' a' b' p' hp ihp =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ [mkAssign x' (a'.addDisj b')]
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.addDisj b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    -- After subst: Γ' → Γ, x' → z
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Apply addDisjR1 with channel y
    have hIH := ihp Γ z a' hyfresh hzfresh hyz rfl
    exact CPTyped.addDisjR1 Γ y a' b' (p'.subst y z) hIH
  | addDisjR2 Γ' x' a' b' p' hp ihp =>
    simp only [CPProc.subst]
    -- hctx: Γ ++ [mkAssign z a] = Γ' ++ [mkAssign x' (a'.addDisj b')]
    have heq := List.append_singleton_inj.mp hctx
    have hΓ : Γ = Γ' := heq.1
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hzx' : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = a'.addDisj b' := congrArg TypeAssign.prop hassign
    subst hΓ hzx' ha
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Apply addDisjR2 with channel y (premise uses b', not a')
    have hIH := ihp Γ z b' hyfresh hzfresh hyz rfl
    exact CPTyped.addDisjR2 Γ y a' b' (p'.subst y z) hIH
  | oneR x' =>
    -- oneR context is [x':1], process is .emptyOut x'
    -- [x':1] = Γ ++ [z:a], so Γ = [] and z = x' and a = .one
    simp only [CPProc.subst]
    cases Γ with
    | nil =>
      simp only [List.nil_append] at hctx
      have hz := List.singleton_injective hctx
      simp only [mkAssign] at hz
      have hzchan : z = x' := congrArg TypeAssign.chan hz
      have haprop : a = .one := congrArg TypeAssign.prop hz
      subst hzchan haprop
      simp only [beq_self_eq_true, ↓reduceIte, List.nil_append]
      exact CPTyped.oneR y
    | cons hd tl =>
      simp only [List.cons_append] at hctx
      have hlen := congrArg List.length hctx
      simp at hlen
  | botR Γ' x' p' hp ihp =>
    -- botR context is Γ' ++ [x':⊥], process is .emptyInp x' p'
    simp only [CPProc.subst]
    -- hctx: Γ ++ [z:a] = Γ' ++ [x':⊥]
    have heq := List.append_singleton_inj.mp hctx
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hx : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = CLLProp.bot := congrArg TypeAssign.prop hassign
    rw [heq.1, hx, ha]
    simp only [beq_self_eq_true, ↓reduceIte]
    -- Goal: CPTyped (Γ' ++ [mkAssign y .bot]) (.emptyInp y (p'.subst y x'))
    -- hp : CPTyped Γ' p'. By hzfresh (z = x' not in Γ = Γ'), x' ∉ p'.freeChans.
    have hx'_fresh : ∀ ta ∈ Γ', ta.chan ≠ x' := fun ta hta => by
      have := hzfresh ta (heq.1 ▸ hta)
      simp only [hx] at this
      exact this
    have hx'_not_free : x' ∉ p'.freeChans := CPTyped.not_in_context_not_free hp hx'_fresh
    rw [CPProc.subst_not_free p' y x' hx'_not_free]
    exact CPTyped.botR Γ' y p' hp
  | topR Γ' x' p' =>
    -- topR context is Γ' ++ [x':⊤], types any process p'
    -- hctx: Γ ++ [z:a] = Γ' ++ [x':⊤]
    have heq := List.append_singleton_inj.mp hctx
    -- heq.1 : Γ = Γ', heq.2 : mkAssign z a = mkAssign x' .top
    have hassign := heq.2
    simp only [mkAssign] at hassign
    have hx : z = x' := congrArg TypeAssign.chan hassign
    have ha : a = CLLProp.top := congrArg TypeAssign.prop hassign
    -- Rewrite goal using equalities
    rw [heq.1, hx, ha]
    -- Goal: CPTyped (Γ' ++ [mkAssign y .top]) (p'.subst y x')
    exact CPTyped.topR Γ' y (p'.subst y x')
  | mix Γ' Δ' p' q' hp hq ihp ihq =>
    simp only [CPProc.subst]
    -- hctx : Γ ++ [mkAssign z a] = Γ' ++ Δ'
    -- Case split: z is in Γ' (Δ' = []) or z is in Δ' (Δ' ends with z)
    -- The last element of LHS is mkAssign z a, so it must be the last of RHS
    cases hΔ' : Δ' with
    | nil =>
      -- Δ' = [], so Γ' = Γ ++ [mkAssign z a]
      simp only [hΔ', List.append_nil] at hctx
      -- hctx : Γ ++ [mkAssign z a] = Γ'
      have hIHp := ihp Γ z a hyfresh hzfresh hyz hctx
      -- hq : CPTyped [] q', need to show q'.subst y z = q'
      -- Since z is not in the empty context, z ∉ q'.freeChans
      -- For CPTyped [] q', freeChans ⊆ [] means freeChans = []
      simp only [hΔ'] at hq
      have hz_not_free : z ∉ q'.freeChans := by
        intro hmem
        have ⟨ta, hta, _⟩ := hq.freeChans_subset_context z hmem
        exact List.not_mem_nil hta
      rw [CPProc.subst_not_free q' y z hz_not_free]
      have hmix := CPTyped.mix (Γ ++ [mkAssign y a]) [] (p'.subst y z) q' hIHp hq
      simp only [List.append_nil] at hmix
      exact hmix
    | cons hd tl =>
      -- Δ' = hd :: tl, non-empty, so z is in Δ'
      -- The last element of Γ' ++ (hd :: tl) is the last of (hd :: tl)
      -- Since hctx says this equals mkAssign z a, we have Δ' ends with mkAssign z a
      have hΔ'_ne : Δ' ≠ [] := by simp only [hΔ']; exact List.cons_ne_nil hd tl
      -- Use getLast? to avoid proof-relevant non-emptiness issues
      have hLHS_last : (Γ ++ [mkAssign z a]).getLast? = some (mkAssign z a) := by
        simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ []),
                   List.getLast?_singleton]
      have hRHS_last : (Γ' ++ Δ').getLast? = Δ'.getLast? := by
        exact List.getLast?_append_of_ne_nil Γ' hΔ'_ne
      -- From hctx: getLast? equal
      have hLast_eq : Δ'.getLast? = some (mkAssign z a) := by
        have heq : List.getLast? (Γ' ++ Δ') = List.getLast? (Γ ++ [mkAssign z a]) := by
          rw [hctx]
        rw [hRHS_last, hLHS_last] at heq
        exact heq
      -- Extract: Δ'.getLast = mkAssign z a
      -- `a ∈ l.getLast?` means `some a = l.getLast?`
      have hmem : mkAssign z a ∈ Δ'.getLast? := by
        rw [hLast_eq]; rfl
      have hΔ'_decomp : Δ' = Δ'.dropLast ++ [mkAssign z a] :=
        (List.dropLast_append_getLast? (mkAssign z a) hmem).symm
      -- Rewrite hctx using this decomposition
      rw [hΔ'_decomp] at hctx
      -- hctx : Γ ++ [mkAssign z a] = Γ' ++ (Δ'.dropLast ++ [mkAssign z a])
      --      = (Γ' ++ Δ'.dropLast) ++ [mkAssign z a]
      rw [← List.append_assoc] at hctx
      have hΓ_eq : Γ = Γ' ++ Δ'.dropLast := List.append_cancel_right hctx
      -- hp : CPTyped Γ' p', need z ∉ Γ' to show p'.subst y z = p'
      -- hq : CPTyped Δ' q' = CPTyped (Δ'.dropLast ++ [mkAssign z a]) q'
      rw [hΔ'_decomp] at hq
      -- Apply ihq to hq
      have hyfreshΔ : ∀ ta ∈ Δ'.dropLast, ta.chan ≠ y := by
        intro ta hta
        have hta' : ta ∈ Γ := by
          rw [hΓ_eq]
          exact List.mem_append_right Γ' hta
        exact hyfresh ta hta'
      have hzfreshΔ : ∀ ta ∈ Δ'.dropLast, ta.chan ≠ z := by
        intro ta hta
        have hta' : ta ∈ Γ := by
          rw [hΓ_eq]
          exact List.mem_append_right Γ' hta
        exact hzfresh ta hta'
      have hIHq := ihq Δ'.dropLast z a hyfreshΔ hzfreshΔ hyz hΔ'_decomp.symm
      -- For p'.subst y z = p', need z ∉ p'.freeChans
      -- z ∉ Γ' because ta ∈ Γ' → ta ∈ Γ' ++ Δ'.dropLast = Γ → ta.chan ≠ z
      have hzfreshΓ' : ∀ ta ∈ Γ', ta.chan ≠ z := fun ta hta =>
        hzfresh ta (hΓ_eq ▸ List.mem_append_left Δ'.dropLast hta)
      have hz_not_free : z ∉ p'.freeChans := CPTyped.not_in_context_not_free hp hzfreshΓ'
      rw [CPProc.subst_not_free p' y z hz_not_free]
      -- Now construct the result: mix (p' with context Γ') and (q'.subst y z with context Δ'.dropLast ++ [y:a])
      have hmix := CPTyped.mix Γ' (Δ'.dropLast ++ [mkAssign y a]) p' (q'.subst y z) hp hIHq
      -- Need to show: Γ' ++ (Δ'.dropLast ++ [mkAssign y a]) = Γ ++ [mkAssign y a]
      -- By hΓ_eq: Γ = Γ' ++ Δ'.dropLast
      rw [hΓ_eq, List.append_assoc]
      exact hmix

/-- Type preservation (subject reduction)

    The proof proceeds by case analysis on the reduction rule.
    Each reduction corresponds to a cut elimination step in linear logic.

    Key cases:
    - β-tensor/par: tensor elimination with par introduction
    - β-plus/with: additive disjunction elimination with conjunction introduction

    The proof requires showing that the type derivation can be restructured
    after each communication step. -/
theorem CPTyped.preservation (Γ : Context) (p p' : CPProc)
    (htp : CPTyped Γ p) (hred : CPReduce p p') :
    CPTyped Γ p' := by
  -- Proof by case analysis on the reduction rule.
  -- Each principal cut (beta reduction) corresponds to cut elimination in CLL.
  -- The topR rule (⊤) provides a uniform escape: it types ANY process.
  cases hred with
  | beta_tensor_par x y z a b pp qq rr =>
    -- Principal cut for ⊗/⅋: tensor output meets par input
    -- Before: (νx:A⊗B)(x[y].(P|Q) | x(z).R)
    -- After: (νy:A)(P | R[y/z]) | Q
    --
    -- This is the most complex principal cut case. Key issues:
    -- 1. tensorR splits context: Γ' = Γ₁ ++ Γ₂ where
    --    - CPTyped (Γ₁ ++ [y:A]) pp
    --    - CPTyped (Γ₂ ++ [x:B]) qq
    -- 2. parR: CPTyped (Δ' ++ [z:A⊥, x:B⊥]) rr
    -- 3. Result mixes contexts differently:
    --    - (νy:A)(pp | rr.subst y z) uses Γ₁ ++ (Δ' without x:B⊥)
    --    - qq uses Γ₂ without x:B
    -- 4. Requires: channel substitution lemma for typing
    -- 5. Requires: context manipulation to eliminate x from both sides
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- TODO: Prove using out_inv, inp_inv, channel substitution lemma,
      -- and careful context manipulation to construct result with mix + cut
      sorry
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.par (.nu y a (.par pp (rr.subst y z))) qq)
  | beta_par_tensor x y z a b pp qq rr =>
    -- Symmetric principal cut for ⅋/⊗
    -- Before: (νx:A⅋B)(x(y).P | x[z].(Q|R))
    -- After: (νy:A)(P | Q[y/z]) | R
    -- Symmetric to beta_tensor_par
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- TODO: Symmetric to beta_tensor_par
      sorry
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.par (.nu y a (.par pp (qq.subst y z))) rr)
  | beta_addDisj_l x a b pp qq rr =>
    -- Principal cut for ⊕/&: left selection meets case
    -- Before: (νx:A⊕B)(x.inl;P | x.case(Q,R)) → (νx:A)(P | Q)
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- hleft : CPTyped (Γ' ++ [mkAssign x (.addDisj a b)]) (.inl x pp)
      -- hright : CPTyped (Δ' ++ [mkAssign x (.addConj a.dual b.dual)]) (.case x qq rr)
      have hdual : (CLLProp.addDisj a b).dual = .addConj a.dual b.dual := rfl
      rw [hdual] at hright
      have hinv_l := CPTyped.inl_inv _ _ _ hleft
      have hinv_r := CPTyped.case_inv _ _ _ _ hright
      cases hinv_l with
      | inl hinl =>
        obtain ⟨Γ, a', b', heqL, hpL⟩ := hinl
        cases hinv_r with
        | inl hcase =>
          obtain ⟨Δ, a'', b'', heqR, hqR, _hrR⟩ := hcase
          -- heqL: Γ' ++ [mkAssign x (.addDisj a b)] = Γ ++ [mkAssign x (.addDisj a' b')]
          -- heqR: Δ' ++ [mkAssign x (.addConj a.dual b.dual)] = Δ ++ [mkAssign x (.addConj a'' b'')]
          -- Extract: Γ' = Γ, a' = a, b' = b, Δ' = Δ, a'' = a.dual, b'' = b.dual
          have ⟨hΓ, hAssignL⟩ := List.append_singleton_inj.mp heqL
          have hTypeL := congrArg TypeAssign.prop hAssignL
          simp only [mkAssign] at hTypeL
          -- hTypeL : .addDisj a b = .addDisj a' b'
          have ha : a = a' := by injection hTypeL
          have ⟨hΔ, hAssignR⟩ := List.append_singleton_inj.mp heqR
          have hTypeR := congrArg TypeAssign.prop hAssignR
          simp only [mkAssign] at hTypeR
          -- hTypeR : .addConj a.dual b.dual = .addConj a'' b''
          have ha' : a.dual = a'' := by injection hTypeR
          -- Now construct the result. After subst, Γ→Γ', Δ→Δ', a'→a, a''→a.dual
          subst hΓ hΔ ha ha'
          -- Goal: CPTyped (Γ' ++ Δ') (.nu x a (.par pp qq))
          -- We have: hpL : CPTyped (Γ' ++ [mkAssign x a]) pp
          --          hqR : CPTyped (Δ' ++ [mkAssign x a.dual]) qq
          exact CPTyped.cut Γ' Δ' x a pp qq hpL hqR
        | inr htopR =>
          -- hright was topR, contradiction: .addConj ≠ .top
          obtain ⟨Γ'', z, heq⟩ := htopR
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          -- hprop : .addConj a.dual b.dual = .top, contradiction
          cases hprop
      | inr htopL =>
        -- hleft was topR, contradiction: .addDisj ≠ .top
        obtain ⟨Γ'', z, heq⟩ := htopL
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        -- hprop : .addDisj a b = .top, contradiction
        cases hprop
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.nu x a (.par pp qq))
  | beta_addDisj_r x a b pp qq rr =>
    -- Principal cut for ⊕/&: right selection meets case
    -- Before: (νx:A⊕B)(x.inr;P | x.case(Q,R)) → (νx:B)(P | R)
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- hleft : CPTyped (Γ' ++ [mkAssign x (.addDisj a b)]) (.inr x pp)
      -- hright : CPTyped (Δ' ++ [mkAssign x (.addConj a.dual b.dual)]) (.case x qq rr)
      have hdual : (CLLProp.addDisj a b).dual = .addConj a.dual b.dual := rfl
      rw [hdual] at hright
      have hinv_l := CPTyped.inr_inv _ _ _ hleft
      have hinv_r := CPTyped.case_inv _ _ _ _ hright
      cases hinv_l with
      | inl hinr =>
        obtain ⟨Γ, a', b', heqL, hpL⟩ := hinr
        cases hinv_r with
        | inl hcase =>
          obtain ⟨Δ, a'', b'', heqR, _hqR, hrR⟩ := hcase
          -- Extract context and type equalities
          have ⟨hΓ, hAssignL⟩ := List.append_singleton_inj.mp heqL
          have hTypeL := congrArg TypeAssign.prop hAssignL
          simp only [mkAssign] at hTypeL
          -- hTypeL : .addDisj a b = .addDisj a' b'
          have hb : b = b' := by injection hTypeL
          have ⟨hΔ, hAssignR⟩ := List.append_singleton_inj.mp heqR
          have hTypeR := congrArg TypeAssign.prop hAssignR
          simp only [mkAssign] at hTypeR
          -- hTypeR : .addConj a.dual b.dual = .addConj a'' b''
          have hb' : b.dual = b'' := by injection hTypeR
          -- Now construct the result
          subst hΓ hΔ hb hb'
          -- Goal: CPTyped (Γ' ++ Δ') (.nu x b (.par pp rr))
          -- We have: hpL : CPTyped (Γ' ++ [mkAssign x b]) pp
          --          hrR : CPTyped (Δ' ++ [mkAssign x b.dual]) rr
          exact CPTyped.cut Γ' Δ' x b pp rr hpL hrR
        | inr htopR =>
          -- hright was topR, contradiction: .addConj ≠ .top
          obtain ⟨Γ'', z, heq⟩ := htopR
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          cases hprop
      | inr htopL =>
        -- hleft was topR, contradiction: .addDisj ≠ .top
        obtain ⟨Γ'', z, heq⟩ := htopL
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        cases hprop
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.nu x b (.par pp rr))
  | beta_addConj_l x a b pp qq rr =>
    -- Principal cut for &/⊕: case meets left selection (symmetric to addDisj)
    -- Before: (νx:A&B)(x.case(P,Q) | x.inl;R) → (νx:A)(P | R)
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      have hdual : (CLLProp.addConj a b).dual = .addDisj a.dual b.dual := rfl
      rw [hdual] at hright
      have hinv_l := CPTyped.case_inv _ _ _ _ hleft
      have hinv_r := CPTyped.inl_inv _ _ _ hright
      cases hinv_l with
      | inl hcase =>
        obtain ⟨Γ, a', b', heqL, hpL, _hqL⟩ := hcase
        cases hinv_r with
        | inl hinl =>
          obtain ⟨Δ, a'', b'', heqR, hrR⟩ := hinl
          have ⟨hΓ, hAssignL⟩ := List.append_singleton_inj.mp heqL
          have hTypeL := congrArg TypeAssign.prop hAssignL
          simp only [mkAssign] at hTypeL
          have ha : a = a' := by injection hTypeL
          have ⟨hΔ, hAssignR⟩ := List.append_singleton_inj.mp heqR
          have hTypeR := congrArg TypeAssign.prop hAssignR
          simp only [mkAssign] at hTypeR
          have ha' : a.dual = a'' := by injection hTypeR
          subst hΓ hΔ ha ha'
          exact CPTyped.cut Γ' Δ' x a pp rr hpL hrR
        | inr htopR =>
          obtain ⟨Γ'', z, heq⟩ := htopR
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          cases hprop
      | inr htopL =>
        obtain ⟨Γ'', z, heq⟩ := htopL
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        cases hprop
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.nu x a (.par pp rr))
  | beta_addConj_r x a b pp qq rr =>
    -- Principal cut for &/⊕: case meets right selection
    -- Before: (νx:A&B)(x.case(P,Q) | x.inr;R) → (νx:B)(Q | R)
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      have hdual : (CLLProp.addConj a b).dual = .addDisj a.dual b.dual := rfl
      rw [hdual] at hright
      have hinv_l := CPTyped.case_inv _ _ _ _ hleft
      have hinv_r := CPTyped.inr_inv _ _ _ hright
      cases hinv_l with
      | inl hcase =>
        obtain ⟨Γ, a', b', heqL, _hpL, hqL⟩ := hcase
        cases hinv_r with
        | inl hinr =>
          obtain ⟨Δ, a'', b'', heqR, hrR⟩ := hinr
          have ⟨hΓ, hAssignL⟩ := List.append_singleton_inj.mp heqL
          have hTypeL := congrArg TypeAssign.prop hAssignL
          simp only [mkAssign] at hTypeL
          have hb : b = b' := by injection hTypeL
          have ⟨hΔ, hAssignR⟩ := List.append_singleton_inj.mp heqR
          have hTypeR := congrArg TypeAssign.prop hAssignR
          simp only [mkAssign] at hTypeR
          have hb' : b.dual = b'' := by injection hTypeR
          subst hΓ hΔ hb hb'
          exact CPTyped.cut Γ' Δ' x b qq rr hqL hrR
        | inr htopR =>
          obtain ⟨Γ'', z, heq⟩ := htopR
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          cases hprop
      | inr htopL =>
        obtain ⟨Γ'', z, heq⟩ := htopL
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        cases hprop
    | topR Γ' x' _ =>
      exact CPTyped.topR Γ' x' (.nu x b (.par qq rr))
  | beta_one_bot xChan pCont =>
    -- Principal cut for 1/⊥: unit output meets unit input
    -- Before: (νx:1)(x[].0 | x().P)  →  P
    -- After: P
    cases htp with
    | cut Γ' Δ' x a left right hleft hright =>
      -- Typing is via cut: Γ ++ Δ ⊢ (νx:1)(emptyOut x | emptyInp x P)
      -- hleft: CPTyped (Γ' ++ [mkAssign xChan .one]) (.emptyOut xChan)
      -- hright: CPTyped (Δ' ++ [mkAssign xChan .bot]) (.emptyInp xChan pCont)
      -- By emptyOut_inv, hleft is oneR, so Γ' = []
      -- By emptyInp_inv, hright is botR, giving CPTyped Δ' pCont
      have hinv_l := CPTyped.emptyOut_inv _ _ hleft
      -- Note: .one.dual = .bot
      have hdual : CLLProp.one.dual = CLLProp.bot := rfl
      rw [hdual] at hright
      have hinv_r := CPTyped.emptyInp_inv _ _ _ hright
      cases hinv_l with
      | inl hone =>
        -- hleft is oneR, so Γ' = []
        have hGamma_nil : Γ' = [] := by
          have heq := hone
          -- Γ' ++ [mkAssign xChan .one] = [mkAssign xChan .one]
          cases Γ' with
          | nil => rfl
          | cons h t =>
            simp only [List.cons_append] at heq
            exact absurd heq (by simp)
        cases hinv_r with
        | inl hbot =>
          -- hright is botR, giving CPTyped Δ'' pCont where Δ' = Δ''
          obtain ⟨Δ'', heq, hp⟩ := hbot
          -- heq: Δ' ++ [mkAssign xChan .bot] = Δ'' ++ [mkAssign xChan .bot]
          have hDelta_eq : Δ' = Δ'' := (List.append_singleton_inj.mp heq).1
          subst hDelta_eq hGamma_nil
          simp only [List.nil_append]
          exact hp
        | inr htop =>
          -- hright is topR - but then .bot ≠ .top, contradiction
          obtain ⟨Γ'', y, heq⟩ := htop
          -- heq: Δ' ++ [mkAssign xChan .bot] = Γ'' ++ [mkAssign y .top]
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          exact absurd hprop (by decide)
      | inr htop =>
        -- hleft is topR - but then .one ≠ .top, contradiction
        obtain ⟨Γ'', y, heq⟩ := htop
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        exact absurd hprop (by decide)
    | topR Γ' xTop _ =>
      -- p' is the target process (unified with constructor's p parameter)
      exact CPTyped.topR Γ' xTop p'
  | beta_bot_one xChan _ =>
    -- Symmetric principal cut for ⊥/1
    -- Before: (νx:⊥)(x().P | x[].0)  →  P
    -- After: P
    cases htp with
    | cut Γ' Δ' x a left right hleft hright =>
      -- hleft: CPTyped (Γ' ++ [mkAssign xChan .bot]) (.emptyInp xChan p')
      -- hright: CPTyped (Δ' ++ [mkAssign xChan .one]) (.emptyOut xChan)
      -- By emptyInp_inv, hleft is botR, giving CPTyped Γ' p'
      -- By emptyOut_inv, hright is oneR, so Δ' = []
      have hdual : CLLProp.bot.dual = CLLProp.one := rfl
      rw [hdual] at hright
      have hinv_l := CPTyped.emptyInp_inv _ _ _ hleft
      have hinv_r := CPTyped.emptyOut_inv _ _ hright
      cases hinv_r with
      | inl hone =>
        -- hright is oneR, so Δ' = []
        have hDelta_nil : Δ' = [] := by
          have heq := hone
          cases Δ' with
          | nil => rfl
          | cons h t =>
            simp only [List.cons_append] at heq
            exact absurd heq (by simp)
        cases hinv_l with
        | inl hbot =>
          -- hleft is botR, giving CPTyped Γ'' p' where Γ' = Γ''
          obtain ⟨Γ'', heq, hp⟩ := hbot
          have hGamma_eq : Γ' = Γ'' := (List.append_singleton_inj.mp heq).1
          subst hGamma_eq hDelta_nil
          simp only [List.append_nil]
          exact hp
        | inr htop =>
          -- hleft is topR - but then .bot ≠ .top, contradiction
          obtain ⟨Γ'', y, heq⟩ := htop
          have heq' := (List.append_singleton_inj.mp heq).2
          have hprop := congrArg TypeAssign.prop heq'
          simp only [mkAssign] at hprop
          exact absurd hprop (by decide)
      | inr htop =>
        -- hright is topR - but then .one ≠ .top, contradiction
        obtain ⟨Γ'', y, heq⟩ := htop
        have heq' := (List.append_singleton_inj.mp heq).2
        have hprop := congrArg TypeAssign.prop heq'
        simp only [mkAssign] at hprop
        exact absurd hprop (by decide)
    | topR Γ' xTop _ =>
      exact CPTyped.topR Γ' xTop p'
  | cong_nu x a pp pp' hred' =>
    -- Congruence under restriction: if body reduces, result reduces
    cases htp with
    | cut Γ' Δ' x' a' left right hleft hright =>
      -- The cut body (.par left right) reduces to pp'
      -- Case on how the parallel reduces
      match hred' with
      | .cong_par_l _ newLeft _ hredL =>
        -- left -> newLeft, so pp' = .par newLeft right
        have ih := preservation (Γ' ++ [mkAssign x a]) left newLeft hleft hredL
        exact CPTyped.cut Γ' Δ' x a newLeft right ih hright
      | .cong_par_r _ _ newRight hredR =>
        -- right -> newRight, so pp' = .par left newRight
        have ih := preservation (Δ' ++ [mkAssign x a.dual]) right newRight hright hredR
        exact CPTyped.cut Γ' Δ' x a left newRight hleft ih
    | topR Γ' x' _ => exact CPTyped.topR Γ' x' (.nu x a pp')
  | cong_par_l pp pp' qq hred' =>
    -- Congruence in left of parallel
    cases htp with
    | mix Γ' Δ' left right hp hq =>
      have ih := preservation Γ' pp pp' hp hred'
      exact CPTyped.mix Γ' Δ' pp' qq ih hq
    | topR Γ' x' _ => exact CPTyped.topR Γ' x' (.par pp' qq)
  | cong_par_r pp qq qq' hred' =>
    -- Congruence in right of parallel
    cases htp with
    | mix Γ' Δ' left right hp hq =>
      have ih := preservation Δ' qq qq' hq hred'
      exact CPTyped.mix Γ' Δ' pp qq' hp ih
    | topR Γ' x' _ => exact CPTyped.topR Γ' x' (.par pp qq')

/-- Helper: When one side of a cut on singleton context is itself a cut,
    the whole process can reduce via congruence.

    This consolidates all cut/mix sub-cases in the progress theorem.
    The proof requires strong induction on derivation depth because
    the inner cut has a strictly smaller derivation than the outer cut.

    Key insight: A cut nu y B (par p q) typed on [x:a] means B and a are
    related (the cut channel y binds types B and B.dual, while x:a persists).
    The inner cut can always fire a principal reduction eventually. -/
private theorem cut_sub_reduces (x : Chan) (a : CLLProp) (left right : CPProc)
    (hleft : CPTyped [mkAssign x a] left)
    (hright : CPTyped [mkAssign x a.dual] right)
    (hinner : (∃ y B body, left = .nu y B body) ∨ (∃ p q, left = .par p q) ∨
              (∃ y B body, right = .nu y B body) ∨ (∃ p q, right = .par p q)) :
    ∃ r, CPReduce (.nu x a (.par left right)) r := by
  -- This requires well-founded induction on the total derivation size.
  -- The inner cut/mix has strictly smaller sub-derivations, and eventually
  -- we reach base cases (oneR, topR) that form principal cuts.
  --
  -- Full proof sketch:
  -- 1. If left is a cut nu y B (par p q), analyze the typing of p and q
  -- 2. Either p/q form a principal cut on y (reduce inner), or recurse
  -- 3. Inner reduction gives outer reduction via cong_nu and cong_par_l
  -- 4. Similar for mix cases using cong_par_l/cong_par_r
  --
  -- The termination argument uses derivation depth, which decreases at each step.
  sorry

/-- Progress: well-typed closed processes are either values or can step

    A process with empty typing context has no free channels, meaning
    all channels are bound by ν. Such processes are either:
    - Terminated (nil)
    - Can reduce via internal communication

    Note: The empty context case is very restrictive. Analysis:
    - ax: context = [x:A, w:A⊥] - non-empty
    - cut: context = Γ ++ Δ - can be empty if Γ = Δ = []
    - tensorR, parR, addConjR, addDisjR1/R2: context = ... ++ [x:T] - non-empty
    - oneR: context = [x:1] - non-empty
    - botR: context = Γ ++ [x:⊥] - non-empty
    - topR: context = Γ ++ [x:⊤] - non-empty

    So the ONLY way to get CPTyped [] p is via cut with Γ = Δ = [].
    The cut produces .nu x a (.par p q) which can reduce if p and q
    are complementary on x (principal cut). -/
theorem CPTyped.progress (p : CPProc)
    (htp : CPTyped [] p) :
    p.isNormalForm ∨ ∃ p', CPReduce p p' := by
  -- Most typing rules produce non-empty contexts
  -- Only cut/mix with Γ = Δ = [] can produce empty context
  -- We generalize the context to handle the equation
  generalize hctx : ([] : Context) = ctx at htp
  induction htp with
  | ax x w a =>
    -- Context [x:a, w:a.dual] = [], impossible (length mismatch)
    exact absurd hctx.symm (List.cons_ne_nil _ _)
  | cut Γ' Δ' x a left right hleft hright _ihleft _ihright =>
    -- Context Γ' ++ Δ' = []
    have hboth := List.append_eq_nil_iff.mp hctx.symm
    have hΓ'_nil : Γ' = [] := hboth.1
    have hΔ'_nil : Δ' = [] := hboth.2
    subst hΓ'_nil hΔ'_nil
    -- hleft : CPTyped [x:a] left, hright : CPTyped [x:a.dual] right
    -- The cut body is .nu x a (.par left right)
    -- Case on a to determine left/right structure, then show principal cut
    -- Note: For most cases, we show a reduction exists (right disjunct)
    right
    -- Analyze by type a - each case has specific process shapes
    cases a with
    | one =>
      -- hleft : CPTyped [x:one] left, hright : CPTyped [x:bot] right
      -- Use inversion lemmas to determine process structure
      rcases singleton_one_cases x left hleft with hleft_ready | ⟨y, B, body, hleft_cut⟩ | ⟨p1, p2, hleft_mix⟩
      · -- left = emptyOut x
        rcases singleton_bot_cases x right hright with ⟨r, hright_ready, hr_typed⟩ | ⟨y, B, body, hright_cut⟩ | ⟨q1, q2, hright_mix⟩
        · -- right = emptyInp x r, apply beta_one_bot
          subst hleft_ready hright_ready
          exact ⟨r, .beta_one_bot x r⟩
        · -- right is a cut
          subst hleft_ready hright_cut
          exact cut_sub_reduces x .one (.emptyOut x) (.nu y B body) hleft hright
            (Or.inr (Or.inr (Or.inl ⟨y, B, body, rfl⟩)))
        · -- right is a mix
          subst hleft_ready hright_mix
          exact cut_sub_reduces x .one (.emptyOut x) (.par q1 q2) hleft hright
            (Or.inr (Or.inr (Or.inr ⟨q1, q2, rfl⟩)))
      · -- left is a cut
        subst hleft_cut
        exact cut_sub_reduces x .one (.nu y B body) right hleft hright
          (Or.inl ⟨y, B, body, rfl⟩)
      · -- left is a mix
        subst hleft_mix
        exact cut_sub_reduces x .one (.par p1 p2) right hleft hright
          (Or.inr (Or.inl ⟨p1, p2, rfl⟩))
    | bot =>
      -- hleft : CPTyped [x:bot] left, hright : CPTyped [x:one] right (since bot.dual = one)
      -- Symmetric to one case
      rcases singleton_bot_cases x left hleft with ⟨p', hleft_ready, hp'_typed⟩ | ⟨y, B, body, hleft_cut⟩ | ⟨p1, p2, hleft_mix⟩
      · -- left = emptyInp x p'
        rcases singleton_one_cases x right hright with hright_ready | ⟨y, B, body, hright_cut⟩ | ⟨q1, q2, hright_mix⟩
        · -- right = emptyOut x, apply beta_bot_one
          subst hleft_ready hright_ready
          exact ⟨p', .beta_bot_one x p'⟩
        · subst hleft_ready hright_cut
          exact cut_sub_reduces x .bot (.emptyInp x p') (.nu y B body) hleft hright
            (Or.inr (Or.inr (Or.inl ⟨y, B, body, rfl⟩)))
        · subst hleft_ready hright_mix
          exact cut_sub_reduces x .bot (.emptyInp x p') (.par q1 q2) hleft hright
            (Or.inr (Or.inr (Or.inr ⟨q1, q2, rfl⟩)))
      · subst hleft_cut
        exact cut_sub_reduces x .bot (.nu y B body) right hleft hright
          (Or.inl ⟨y, B, body, rfl⟩)
      · subst hleft_mix
        exact cut_sub_reduces x .bot (.par p1 p2) right hleft hright
          (Or.inr (Or.inl ⟨p1, p2, rfl⟩))
    | tensor t1 t2 =>
      -- hleft : CPTyped [x:tensor t1 t2] left, hright : CPTyped [x:par t1.dual t2.dual] right
      -- Principal cut: .out x y p q meets .inp x z r → beta_tensor_par
      have hdual : (CLLProp.tensor t1 t2).dual = .par t1.dual t2.dual := rfl
      rw [hdual] at hright
      rcases singleton_tensor_cases x t1 t2 left hleft with ⟨y, p, q, hleft_ready, hp, hq⟩ | ⟨y', B, body, hleft_cut⟩ | ⟨p1, p2, hleft_mix⟩
      · -- left = .out x y p q
        rcases singleton_par_cases x t1.dual t2.dual right hright with ⟨z, r, hright_ready, hr⟩ | ⟨y'', B', body', hright_cut⟩ | ⟨q1, q2, hright_mix⟩
        · -- right = .inp x z r, apply beta_tensor_par
          subst hleft_ready hright_ready
          exact ⟨.par (.nu y t1 (.par p (r.subst y z))) q, .beta_tensor_par x y z t1 t2 p q r⟩
        · subst hleft_ready hright_cut
          exact cut_sub_reduces x (.tensor t1 t2) (.out x y p q) (.nu y'' B' body') hleft hright
            (Or.inr (Or.inr (Or.inl ⟨y'', B', body', rfl⟩)))
        · subst hleft_ready hright_mix
          exact cut_sub_reduces x (.tensor t1 t2) (.out x y p q) (.par q1 q2) hleft hright
            (Or.inr (Or.inr (Or.inr ⟨q1, q2, rfl⟩)))
      · subst hleft_cut
        exact cut_sub_reduces x (.tensor t1 t2) (.nu y' B body) right hleft hright
          (Or.inl ⟨y', B, body, rfl⟩)
      · subst hleft_mix
        exact cut_sub_reduces x (.tensor t1 t2) (.par p1 p2) right hleft hright
          (Or.inr (Or.inl ⟨p1, p2, rfl⟩))
    | par t1 t2 =>
      -- hleft : CPTyped [x:par t1 t2] left, hright : CPTyped [x:tensor t1.dual t2.dual] right
      -- Symmetric to tensor
      have hdual : (CLLProp.par t1 t2).dual = .tensor t1.dual t2.dual := rfl
      rw [hdual] at hright
      rcases singleton_par_cases x t1 t2 left hleft with ⟨y, p, hleft_ready, hp⟩ | ⟨y', B, body, hleft_cut⟩ | ⟨p1, p2, hleft_mix⟩
      · -- left = .inp x y p
        rcases singleton_tensor_cases x t1.dual t2.dual right hright with ⟨z, q, r, hright_ready, hq, hr⟩ | ⟨y'', B', body', hright_cut⟩ | ⟨q1, q2, hright_mix⟩
        · -- right = .out x z q r, apply beta_par_tensor
          subst hleft_ready hright_ready
          exact ⟨.par (.nu y t1 (.par p (q.subst y z))) r, .beta_par_tensor x y z t1 t2 p q r⟩
        · subst hleft_ready hright_cut
          exact cut_sub_reduces x (.par t1 t2) (.inp x y p) (.nu y'' B' body') hleft hright
            (Or.inr (Or.inr (Or.inl ⟨y'', B', body', rfl⟩)))
        · subst hleft_ready hright_mix
          exact cut_sub_reduces x (.par t1 t2) (.inp x y p) (.par q1 q2) hleft hright
            (Or.inr (Or.inr (Or.inr ⟨q1, q2, rfl⟩)))
      · subst hleft_cut
        exact cut_sub_reduces x (.par t1 t2) (.nu y' B body) right hleft hright
          (Or.inl ⟨y', B, body, rfl⟩)
      · subst hleft_mix
        exact cut_sub_reduces x (.par t1 t2) (.par p1 p2) right hleft hright
          (Or.inr (Or.inl ⟨p1, p2, rfl⟩))
    | addDisj t1 t2 =>
      -- hleft : CPTyped [x:addDisj t1 t2] left, hright : CPTyped [x:addConj t1.dual t2.dual] right
      -- Principal cut: .inl/.inr x p meets .case x q r → beta_addDisj_l/r
      have hdual : (CLLProp.addDisj t1 t2).dual = .addConj t1.dual t2.dual := rfl
      rw [hdual] at hright
      rcases singleton_addDisj_cases x t1 t2 left hleft with ⟨p, hleft_inl, hp⟩ | ⟨p, hleft_inr, hp⟩ | ⟨y', B, body, hleft_cut⟩ | ⟨p1, p2, hleft_mix⟩
      · -- left = .inl x p
        rcases singleton_addConj_cases x t1.dual t2.dual right hright with ⟨q, r, hright_ready, hq, hr⟩ | ⟨y'', B', body', hright_cut⟩ | ⟨q1, q2, hright_mix⟩
        · -- right = .case x q r, apply beta_addDisj_l
          subst hleft_inl hright_ready
          exact ⟨.nu x t1 (.par p q), .beta_addDisj_l x t1 t2 p q r⟩
        · subst hleft_inl hright_cut
          exact cut_sub_reduces x (.addDisj t1 t2) (.inl x p) (.nu y'' B' body') hleft hright
            (Or.inr (Or.inr (Or.inl ⟨y'', B', body', rfl⟩)))
        · subst hleft_inl hright_mix
          exact cut_sub_reduces x (.addDisj t1 t2) (.inl x p) (.par q1 q2) hleft hright
            (Or.inr (Or.inr (Or.inr ⟨q1, q2, rfl⟩)))
      · -- left = .inr x p
        rcases singleton_addConj_cases x t1.dual t2.dual right hright with ⟨q, r, hright_ready, hq, hr⟩ | ⟨y'', B', body', hright_cut⟩ | ⟨q1, q2, hright_mix⟩
        · -- right = .case x q r, apply beta_addDisj_r
          subst hleft_inr hright_ready
          exact ⟨.nu x t2 (.par p r), .beta_addDisj_r x t1 t2 p q r⟩
        · subst hleft_inr hright_cut
          exact cut_sub_reduces x (.addDisj t1 t2) (.inr x p) (.nu y'' B' body') hleft hright
            (Or.inr (Or.inr (Or.inl ⟨y'', B', body', rfl⟩)))
        · subst hleft_inr hright_mix
          exact cut_sub_reduces x (.addDisj t1 t2) (.inr x p) (.par q1 q2) hleft hright
            (Or.inr (Or.inr (Or.inr ⟨q1, q2, rfl⟩)))
      · subst hleft_cut
        exact cut_sub_reduces x (.addDisj t1 t2) (.nu y' B body) right hleft hright
          (Or.inl ⟨y', B, body, rfl⟩)
      · subst hleft_mix
        exact cut_sub_reduces x (.addDisj t1 t2) (.par p1 p2) right hleft hright
          (Or.inr (Or.inl ⟨p1, p2, rfl⟩))
    | addConj t1 t2 =>
      -- hleft : CPTyped [x:addConj t1 t2] left, hright : CPTyped [x:addDisj t1.dual t2.dual] right
      -- Symmetric: .case x p q meets .inl/.inr x r → beta_addConj_l/r
      have hdual : (CLLProp.addConj t1 t2).dual = .addDisj t1.dual t2.dual := rfl
      rw [hdual] at hright
      rcases singleton_addConj_cases x t1 t2 left hleft with ⟨p, q, hleft_ready, hp, hq⟩ | ⟨y', B, body, hleft_cut⟩ | ⟨p1, p2, hleft_mix⟩
      · -- left = .case x p q
        rcases singleton_addDisj_cases x t1.dual t2.dual right hright with ⟨r, hright_inl, hr⟩ | ⟨r, hright_inr, hr⟩ | ⟨y'', B', body', hright_cut⟩ | ⟨q1, q2, hright_mix⟩
        · -- right = .inl x r, apply beta_addConj_l
          subst hleft_ready hright_inl
          exact ⟨.nu x t1 (.par p r), .beta_addConj_l x t1 t2 p q r⟩
        · -- right = .inr x r, apply beta_addConj_r
          subst hleft_ready hright_inr
          exact ⟨.nu x t2 (.par q r), .beta_addConj_r x t1 t2 p q r⟩
        · subst hleft_ready hright_cut
          exact cut_sub_reduces x (.addConj t1 t2) (.case x p q) (.nu y'' B' body') hleft hright
            (Or.inr (Or.inr (Or.inl ⟨y'', B', body', rfl⟩)))
        · subst hleft_ready hright_mix
          exact cut_sub_reduces x (.addConj t1 t2) (.case x p q) (.par q1 q2) hleft hright
            (Or.inr (Or.inr (Or.inr ⟨q1, q2, rfl⟩)))
      · subst hleft_cut
        exact cut_sub_reduces x (.addConj t1 t2) (.nu y' B body) right hleft hright
          (Or.inl ⟨y', B, body, rfl⟩)
      · subst hleft_mix
        exact cut_sub_reduces x (.addConj t1 t2) (.par p1 p2) right hleft hright
          (Or.inr (Or.inl ⟨p1, p2, rfl⟩))
    | top =>
      -- a = ⊤, a.dual = 0. hright : CPTyped [x:zero] right is impossible.
      have hzero_dual : CLLProp.top.dual = .zero := rfl
      rw [hzero_dual] at hright
      exact False.elim (singleton_zero_impossible x right hright)
    | zero =>
      -- a = 0, a.dual = ⊤. hleft : CPTyped [x:zero] left is impossible.
      exact False.elim (singleton_zero_impossible x left hleft)
    | atom τ =>
      -- hleft : CPTyped [x:atom τ] left is impossible (no intro rule for atoms)
      exact False.elim (singleton_atom_impossible x τ left hleft)
    | atomDual τ =>
      -- hleft : CPTyped [x:atomDual τ] left is impossible
      exact False.elim (singleton_atomDual_impossible x τ left hleft)
    | ofCourse t =>
      -- Exponentials not in minimal CP
      sorry
    | whyNot t =>
      sorry
  | tensorR Γ' Δ' x y a b pp qq hp hq _ihp _ihq =>
    -- [] = Γ' ++ Δ' ++ [x:tensor], impossible
    have h : Γ' ++ Δ' ++ [mkAssign x (.tensor a b)] ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
    exact absurd hctx.symm h
  | parR Γ' x y a b pp hp _ihp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | addConjR Γ' x a b pp qq hp hq _ihp _ihq =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | addDisjR1 Γ' x a b pp hp _ihp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | addDisjR2 Γ' x a b pp hp _ihp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | oneR x =>
    exact absurd hctx.symm (List.cons_ne_nil _ _)
  | botR Γ' x pp hp _ihp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | topR Γ' x pp =>
    exact absurd hctx.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | mix Γ' Δ' pp qq hp hq ihp ihq =>
    -- Context Γ' ++ Δ' = [], so both empty
    have hboth := List.append_eq_nil_iff.mp hctx.symm
    have hΓ'_nil : Γ' = [] := hboth.1
    have hΔ'_nil : Δ' = [] := hboth.2
    subst hΓ'_nil hΔ'_nil
    -- hp : CPTyped [] pp, hq : CPTyped [] qq
    -- By IH on the derivations
    rcases ihp rfl with hpp_nf | ⟨pp', hpp_red⟩
    · rcases ihq rfl with hqq_nf | ⟨qq', hqq_red⟩
      · -- Both normal forms: .par pp qq is also a normal form
        left
        exact CPProc.par_isNormalForm hpp_nf hqq_nf
      · -- pp is normal form, qq reduces
        right; exact ⟨.par pp qq', .cong_par_r pp qq qq' hqq_red⟩
    · -- pp reduces
      right; exact ⟨.par pp' qq, .cong_par_l pp pp' qq hpp_red⟩

/-! ## Examples -/

/-- Example: identity process (forwarder) -/
def idProc (x w : Chan) : CPProc := .link x w

/-- Identity is well-typed -/
example (x w : Chan) (a : CLLProp) :
    CPTyped [mkAssign x a, mkAssign w a.dual] (idProc x w) :=
  CPTyped.ax x w a

end Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi
