-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- The expression $10x^2-x-24$ can be written as $(Ax-8)(Bx+3),$ where $A$ and $B$ are integers. What is $AB + B$? Show that it is 12.-/
theorem mathd_algebra_276 (a b : ℤ)
    (h₀ : ∀ x : ℝ, 10 * x ^ 2 - x - 24 = (a * x - 8) * (b * x + 3)) : a * b + b = 12 := by


  have key : ∀ x : ℝ, 10 * x ^ 2 - x - 24 = (a * x - 8) * (b * x + 3) := h₀;
  have key2 : ∀ x : ℝ, 10 * x ^ 2 - x - 24 = 10 * x ^ 2 - 10 * x + 9 := by
    simp [sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub, sub_sub