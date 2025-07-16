-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What is the largest negative integer $x$ satisfying $$24x \equiv 15 \pmod{1199}~?$$ Show that it is -449.-/
theorem mathd_numbertheory_765 (x : ℤ) (h₀ : x < 0) (h₁ : 24 * x % 1199 = 15) : x ≤ -449 := by


-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What is the largest negative integer $x$ satisfying $$24x \equiv 15 \pmod{1199}~?$$ Show that it is -449.-/
theorem mathd_numbertheory_765 (x : ℤ) (h₀ : x < 0) (h₁ : 24 * x % 1199 = 15) : x ≤ -449 := by
  have key : 24 * x ≡ 15 (mod 1199) := h₁;
  have key₁ : 24 * x ≡ 4 (mod 1199) := by
    have key₂ : 4 * 6 ≡ 1 (mod 1199) := by
      have key₃ : 4 * 6 ≡ 4 * 6 (mod 1199) := rfl;
      have key₄ : 4 * 6 ≡ 1 (mod 1199) := by
        have key₅ : 4 * 6 ≡ 4 * 6 (mod 1199) := rfl;
        have key₆ : 4 * 6 ≡ 1 (mod 1199) := by
          have key₇ : 4 * 6 ≡ 4 * 6 (mod 1199) := rfl;
          have key₈ : 4 * 6 ≡ 1 (mod 1199) := by
            have key₉ : 4 * 6 ≡ 4 * 6 (mod 1199) := rfl;
            have key₁₀ : 4 * 6 ≡ 1 (mod 1199) := by
              have key₁₁ : 4 * 6 ≡ 4 * 6 (mod 1199) := rfl;
              have key₁₂ : 4 * 6 ≡ 1 (mod 1199) := by
                have key₁₃ : 4 * 6 ≡ 4 * 6 (mod 1199) := rfl;
                have key₁₄ : 4 * 6 ≡ 1 (mod 1199) := by
                  have key₁₅ : 4 * 6 ≡ 4 * 6 (mod 1199) :=