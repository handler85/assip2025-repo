-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? Show that it is 8.-/
theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by


  calc
    f (g 2) = f (2 ^ 2 + 3) := by simp [h₁]
    _ = 2 ^ 2 + 4 := by simp [h₀, h₀]
    _ = 8 := by ring

end

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? Show that it is 8.-/
theorem mathd_algebra_143' (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  calc
    f (g 2) = f (2 ^ 2 + 3) := by simp [h₁]
    _ = 2 ^ 2 + 4 := by simp [h₀, h₀]
    _ = 8 := by ring

end

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? Show that it is 8.-/
theorem mathd_algebra_143'' (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  calc
    f (g 2) = f (2 ^ 2 + 3) := by simp [h₁]
    _ = 2 ^ 2 + 4 := by simp [h₀, h₀]
    _ = 8 := by ring

end

/-- If $f(x) = x + 1$ and $g(x) = x^2 + 3$, what is the value of $f(g(2))$? Show that it is 8.-/
theorem mathd_algebra_143''' (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  calc
    f