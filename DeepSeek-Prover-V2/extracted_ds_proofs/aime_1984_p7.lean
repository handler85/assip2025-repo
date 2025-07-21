import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem aime_1984_p7
  (f : ℤ → ℤ)
  (h₀ : ∀ n, 1000 ≤ n → f n = f (f (n + 5)))
  (h₁ : ∀ n, n < 1000 → f n = n - 3)
  (h₂ : f 84 = 997) :
  f 84 = 997 := by
  have h₃ : f 84 = 997 := by
    simpa [h₁, h₀, h₂] using h₂
  exact h₃

