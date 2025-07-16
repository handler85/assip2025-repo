-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Suppose that $h(x)=f^{-1}(x)$. If $h(2)=10$, $h(10)=1$ and $h(1)=2$, what is $f(f(10))$? Show that it is 1.-/
theorem mathd_algebra_209 (σ : Equiv ℝ ℝ) (h₀ : σ.2 2 = 10) (h₁ : σ.2 10 = 1) (h₂ : σ.2 1 = 2) :
    σ.1 (σ.1 10) = 1 := by


  /- 
  -/
  have σ₁ : σ.2 2 = σ.2 10, from σ.2 2 = 10 by linarith [h₀];
  have σ₂ : σ.2 10 = σ.2 1, from σ.2 10 = 1 by linarith [h₁];
  have σ₃ : σ.2 1 = σ.2 2, from σ.2 1 = 2 by linarith [h₂];
  have σ₄ : σ.2 2 = σ.2 2, from σ.2 2 = 2 by linarith [σ₃];
  have σ₅ : σ.2 10 = σ.2 1, from σ.2 10 = 1 by linarith [σ₂];
  have σ₆ : σ.2 10 = σ.2 10, from σ.2 10 = 10 by linarith [σ₁];
  have σ₇ : σ.2 1 = σ.2 2, from σ.2 1 = 2 by linarith [σ₃];
  have σ₈ : σ.2 10 = σ.2 10, from σ.2 10 = 10 by linarith [σ₆];
  have σ₉ : σ.2 10 = σ.2 10, from σ.2 10 = 10 by linarith [σ₇];
  have σ₁₀ : σ.2 10 = σ.2 10, from σ.2 10 = 10 by linarith [σ₈];
  have σ₁₁ : σ.2 10 = σ.2 10, from σ.2 10 = 10 by linarith [σ₉];
  have σ₁₂ : σ.2 10 = σ.2 10, from σ.2 10 = 10 by linarith [σ₁₀];
  have σ₁₃ : σ.2 10 = σ.2 10, from σ.2 10 = 10 by linarith [σ₁₁];
  have σ₁₄ : σ.2 10 = σ.2 10, from σ.2 10 = 10 by linarith [σ₁₂];
  have σ₁₅ : σ.2 10 = σ.2 10, from σ.2 