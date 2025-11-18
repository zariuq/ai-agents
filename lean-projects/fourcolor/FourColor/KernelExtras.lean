import FourColor.Triangulation

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false


namespace FourColor

open scoped BigOperators
open Classical

noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- chainDot is bilinear: zero on the left. -/
@[simp] lemma chainDot_zero_left (y : E → Color) :
    Color.chainDot (0 : E → Color) y = 0 := by
  classical
  unfold Color.chainDot
  simp [Color.dot_zero_left]

/-- chainDot is bilinear: zero on the right. -/
@[simp] lemma chainDot_zero_right (x : E → Color) :
    Color.chainDot x (0 : E → Color) = 0 := by
  classical
  unfold Color.chainDot
  simp [Color.dot_zero_right']

/-- chainDot distributes over addition on the left. -/
lemma chainDot_add_left (x y z : E → Color) :
    Color.chainDot (x + y) z = Color.chainDot x z + Color.chainDot y z := by
  classical
  unfold Color.chainDot
  simp [Color.dot_add_left, Finset.sum_add_distrib]

/-- chainDot distributes over addition on the right. -/
lemma chainDot_add_right (x y z : E → Color) :
    Color.chainDot x (y + z) = Color.chainDot x y + Color.chainDot x z := by
  classical
  unfold Color.chainDot
  simp [Color.dot_add_right, Finset.sum_add_distrib]

/-- If z is orthogonal to every term in a finite family, it is orthogonal to the sum. -/
lemma chainDot_sum_right_vanish {α : Type*} [Fintype α] [DecidableEq α]
    (z : E → Color) (f : α → E → Color) (S : Finset α)
    (h : ∀ a ∈ S, Color.chainDot z (f a) = 0) :
    Color.chainDot z (∑ a ∈ S, f a) = 0 := by
  classical
  induction S using Finset.induction with
  | empty => simp [chainDot_zero_right]
  | @insert a T haT ih =>
    have hz : Color.chainDot z (f a) = 0 := h a (Finset.mem_insert_self a T)
    have hT : ∀ b ∈ T, Color.chainDot z (f b) = 0 := fun b hb =>
      h b (Finset.mem_insert_of_mem hb)
    calc Color.chainDot z (∑ c ∈ insert a T, f c)
        = Color.chainDot z (f a + ∑ b ∈ T, f b) := by simp [Finset.sum_insert haT]
      _ = Color.chainDot z (f a) + Color.chainDot z (∑ b ∈ T, f b) :=
          chainDot_add_right z (f a) (∑ b ∈ T, f b)
      _ = 0 + Color.chainDot z (∑ b ∈ T, f b) := by rw [hz]
      _ = 0 + 0 := by rw [ih hT]
      _ = 0 := by simp

/-- If x is orthogonal to every term in a finite family, it is orthogonal to the sum. -/
lemma chainDot_sum_left_vanish {α : Type*} [Fintype α] [DecidableEq α]
    (z : E → Color) (f : α → E → Color) (S : Finset α)
    (h : ∀ a ∈ S, Color.chainDot (f a) z = 0) :
    Color.chainDot (∑ a ∈ S, f a) z = 0 := by
  classical
  induction S using Finset.induction with
  | empty => simp [chainDot_zero_left]
  | @insert a T haT ih =>
    have hz : Color.chainDot (f a) z = 0 := h a (Finset.mem_insert_self a T)
    have hT : ∀ b ∈ T, Color.chainDot (f b) z = 0 := fun b hb =>
      h b (Finset.mem_insert_of_mem hb)
    calc Color.chainDot (∑ c ∈ insert a T, f c) z
        = Color.chainDot (f a + ∑ b ∈ T, f b) z := by simp [Finset.sum_insert haT]
      _ = Color.chainDot (f a) z + Color.chainDot (∑ b ∈ T, f b) z :=
          chainDot_add_left (f a) (∑ b ∈ T, f b) z
      _ = 0 + Color.chainDot (∑ b ∈ T, f b) z := by rw [hz]
      _ = 0 + 0 := by rw [ih hT]
      _ = 0 := by simp

end -- noncomputable section

end FourColor
