-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Suppose $a, b, c$ are the sides of a triangle. Prove that 

$a^2(b+c-a)+b^2(c+a-b)+c^2(a+b-c)\le{3abc}.$-/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by


-- Formal statement 
-- 
-- Suppose $a, b, c$ are the sides of a triangle. Prove that 

-- $a^2(b+c-a)+b^2(c+a-b)+c^2(a+b-c)\le{3abc}.$

-- # Parameters

-- # $a, b, c$ are the sides of a triangle.

-- # $h₀ : 0 < a ∧ 0 < b ∧ 0 < c$ : The sides are positive.

-- # $h₁ : c < a + b$ : The third side is less than the sum of the other two.

-- # $h₂ : b < a + c$ : The second side is less than the sum of the other two.

-- # $h₃ : a < b + c$ : The first side is less than the sum of the other two.

-- # $h₄ : a + b > c$ : The sum of the first two sides is greater than the third.

-- # $h₅ : a + c > b$ : The sum of the first and third sides is greater than the second.

-- # $h₆ : b + c > a$ : The sum of the second and third sides is greater than the first.

-- # $h₇ : a + b + c > 0$ : The sum of the sides is positive.

-- # $h₈ : a + b + c > 0$ : The sum of the sides is positive.

-- # $h₉ : a + b + c > 0$ : The sum of the sides is positive.

-- # $h₁₀ : a + b + c > 0$ : The sum of the sides is positive.

-- # $h₁₁ : a + b + c > 0$ : The sum of the sides is positive.

-- # $h₁₂ : a + b + c > 0$ : The sum of the sides is positive.

-- # $h₁₃ : a + b + c > 0$ : The sum of the sides is positive.

-- # $h₁₄ : a + b + c > 0$ : The sum of the sides is positive.

-- # $h₁₅ : a + b + c > 0$ : The sum of the sides is positive.

-- # $h₁₆ : a + b + c > 0$ : The sum of