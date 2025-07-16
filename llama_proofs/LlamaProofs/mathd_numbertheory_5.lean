-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What is the smallest integer greater than 10 that is both a perfect square and a perfect cube? Show that it is 64.-/
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by


  have h₃ : 4 ≤ n / 2 := by
    have h₄ : 5 ≤ n / 2 := by
      have h₅ : 5 ≤ n / 2 + 1 := by
        have h₆ : 5 ≤ n / 2 + 1 / 2 := by
          have h₇ : 5 ≤ n / 2 + 1 / 2 + 1 / 4 := by
            have h₈ : 5 ≤ n / 2 + 1 / 2 + 1 / 4 + 1 / 8 := by
              have h₉ : 5 ≤ n / 2 + 1 / 2 + 1 / 4 + 1 / 8 + 1 / 16 := by
                have h₁₀ : 5 ≤ n / 2 + 1 / 2 + 1 / 4 + 1 / 8 + 1 / 16 + 1 / 32 := by
                  have h₁₁ : 5 ≤ n / 2 + 1 / 2 + 1 / 4 + 1 / 8 + 1 / 16 + 1 / 32 + 1 / 64 := by
                    have h₁₂ : 5 ≤ n / 2 + 1 / 2 + 1 / 4 + 1 / 8 + 1 / 16 + 1 / 32 + 1 / 64 + 1 / 128 := by
                      have h₁₃ : 5 ≤ n / 2 + 1 / 2 + 1 / 4 + 1 / 8 + 1 / 16 + 1 / 32 + 1 / 64 + 1 / 128 + 1 / 256 := by
                        have h₁₄ : 5 ≤ n / 2 + 1 / 2 + 1 / 4 + 1 / 8 + 1 / 16 + 1 / 32 + 1 / 64 + 1 / 128 + 1 / 256 + 1 / 512 := by
                          have h₁₅ : 5 ≤ n / 2 + 1 / 2 + 1 / 4 + 1 / 8 + 1 / 16 + 1 / 32 + 1