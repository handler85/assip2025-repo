-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Let $a$ be a positive real number and $f$ be a real function such that $\forall x \in \mathbb{R}, f(x+a)=\frac{1}{2}+\sqrt{f(x)-f(x)^2}$.
Show that there exists a positive real number $b$ such that $\forall x \in \mathbb{R}, f(x+b)=f(x)$.-/
theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by


-- Formal statement 
/-- Let $a$ be a positive real number and $f$ be a real function such that $\forall x \in \mathbb{R}, f(x+a)=\frac{1}{2}+\sqrt{f(x)-f(x)^2}$.
Show that there exists a positive real number $b$ such that $\forall x \in \mathbb{R}, f(x+b)=f(x)$.-/
theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  let b := a;
  have hb₀ : 0 < b := h₀;
  have hb₁ : ∀ x, f (x + b) = f x := by
    intro x;
    have h₂ : f (x + b) = f (x + a) := by
      have h₃ : x + b = x + a + a := by
        have h₄ : b = a + a := by
          have h₅ : b = a + a := rfl;
          assumption;
        assumption;
      have h₆ : f (x + b) = f (x + a) := by
        have h₇ : f (x + b) = f (x + a) := rfl;
        assumption;
      assumption;
    have h₈ : f (x + b) = f x := by
      have h₉ : f (x + b) = f (x + a) := h₂;
      have h₁₀ : f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2) := h₁;
      have h₁₁ : f (x + b) = f x := by
        have h₁₂ : f (x + b) = f (x + a) := h₉;
        have h₁₃ : f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2) := h₁₀;
        have h₁₄ : f (x + b) = f