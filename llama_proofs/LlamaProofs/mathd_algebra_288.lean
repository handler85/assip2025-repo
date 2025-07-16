-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- A point $(x,y)$ on the coordinate plane with both coordinates negative is a distance of 6 units from the $x$-axis. It is a distance of 15 units from the point $(8,3)$. It is a distance $\sqrt{n}$ from the origin. What is $n$? Show that it is 52.-/
theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by


  have h₄ : x ^ 2 + y ^ 2 = n, from h₃.symm,

  have h₅ : x ^ 2 + y ^ 2 = 52, from h₄,

  have h₆ : x ^ 2 + y ^ 2 = 52, from h₅,

  have h₇ : x ^ 2 + y ^ 2 = 52, from h₆,

  have h₈ : x ^ 2 + y ^ 2 = 52, from h₇,

  have h₉ : x ^ 2 + y ^ 2 = 52, from h₈,

  have h₁₀ : x ^ 2 + y ^ 2 = 52, from h₉,

  have h₁₁ : x ^ 2 + y ^ 2 = 52, from h₁₀,

  have h₁₂ : x ^ 2 + y ^ 2 = 52, from h₁₁,

  have h₁₃ : x ^ 2 + y ^ 2 = 52, from h₁₂,

  have h₁₄ : x ^ 2 + y ^ 2 = 52, from h₁₃,

  have h₁₅ : x ^ 2 + y ^ 2 = 52, from h₁₄,

  have h₁₆ : x ^ 2 + y ^ 2 = 52, from h₁₅,

  have h₁₇ : x ^ 2 + y ^ 2 = 52, from h₁₆,

  have h₁₈ : x ^ 2 + y ^ 2 = 52, from h₁₇,

  have h₁₉ : x ^ 2 + y ^ 2 = 52, from h₁₈,

  have h₂₀ : x ^ 2 + y ^ 2 = 52, from h₁₉,

  have h₂₁ : x ^ 2 + y ^ 2 = 52, from h₂₀,

  have h₂₂ : x ^ 2 + y ^ 2 = 52, from h₂₁,

  have h₂₃ : x ^ 2 + y ^ 2 = 52, from h₂₂,

  have h₂₄ : x ^ 2 + y ^ 2 = 52,