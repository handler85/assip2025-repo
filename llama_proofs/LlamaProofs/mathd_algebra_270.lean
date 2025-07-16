-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- If $f(x) = \dfrac{1}{x + 2},$ what is $f(f(1))$? Show that it is \dfrac{3}{7}.-/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by


  have f1 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f2 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f3 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f4 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f5 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f6 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f7 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f8 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f9 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f10 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f11 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f12 : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2) := λ x (_ : x ≠ -2), f x;
  have f13 : ∀ (x) (_ : x ≠ -2), f x = 