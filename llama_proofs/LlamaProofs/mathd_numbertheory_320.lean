-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What integer $n$ satisfies $0\le n<{101}$ and $$123456\equiv n\pmod {101}~?$$ Show that it is 34.-/
theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by


-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What integer $n$ satisfies $0\le n<{101}$ and $$123456\equiv n\pmod {101}~?$$ Show that it is 34.-/
theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by
  have key : 123456 % 101 = 34 % 101 := by
    calc
      123456 % 101 = 123456 - 101 * (123456 / 101) % 101
     ... = 123456 - 12345 % 101
     ... = 123456 - 12345 + 1 % 101
     ... = 123457 % 101

  have key2 : 123457 % 101 = 34 % 101 := by
    calc
      123457 % 101 = 123457 - 101 * (123457 / 101) % 101
     ... = 123457 - 12345 % 101
     ... = 123457 - 12345 + 1 % 101
     ... = 123458 % 101

  have key3 : 123458 % 101 = 35 % 101 := by
    calc
      123458 % 101 = 123458 - 101 * (123458 / 101) % 101
     ... = 123458 - 12345 % 101
     ... = 123458 - 12345 + 1 % 101
     ... = 123459 % 101

  have key4 : 123459 % 101 = 0 % 101 := by
    calc
      123459 % 101 = 123459 - 101 * (123459 / 101) % 101
     ... = 123459 - 12345 % 101
     ... = 123459 - 12345 + 1 % 101
     ... = 123460 % 101

  have key5 : 123460 % 101 = 1 % 101 := by
    calc
      123460 % 101 = 123460 - 101 * (123