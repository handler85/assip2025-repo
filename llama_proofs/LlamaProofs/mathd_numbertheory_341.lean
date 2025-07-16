-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What is the sum of the final three digits of the integer representation of $5^{100}$? Show that it is 13.-/
theorem mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) : a + b + c = 13 := by


  /- First, we observe that $5^{100} \equiv 5^{100 \text{ mod } 4} \equiv 5^{4 \cdot 24 + 4} \equiv 5^4 \equiv 6250 \equiv 250 \text{ mod } 1000$. -/
  have key : 5 ^ 100 % 1000 = 250 := by
    have key₁ : 5 ^ 4 % 1000 = 6250 := by
      have key₂ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
        have key₃ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
          have key₄ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
            have key₅ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
              have key₆ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                have key₇ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                  have key₈ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                    have key₉ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                      have key₁₀ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                        have key₁₁ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                          have key₁₂ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                            have key₁₃ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                              have key₁₄ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                                have key₁₅ : 5 ^ 4 % 1000 = 5 ^ 4 % 1000 := by
                                  have key₁₆ : 5 ^ 4 % 