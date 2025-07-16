-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? Show that it is 1.-/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by


/- The graphs of $y=x^4$ and $y=5x^2-6$ intersect at four points with $x$-coordinates $\pm \sqrt{m}$ and $\pm \sqrt{n}$, where $m > n$. What is $m-n$? Show that it is 1.-/
theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by
  have h₅ : x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 := by
    repeat { try { split } }
  have h₆ : x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 := by
    try { split } at h₅
  have h₇ : x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 := by
    try { split } at h₆
  have h₈ : x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 := by
    try { split } at h₇
  have h₉ : x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 := by
    try { split } at h₈
  have h₁₀ : x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x ^ 2 < y ^ 2 ∧ x