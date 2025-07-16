-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Determine the modulo 4 remainder of the following sum: $$ 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12. $$ Show that it is 2.-/
theorem mathd_numbertheory_239 : (∑ k in Finset.Icc 1 12, k) % 4 = 2 := by


-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Determine the modulo 4 remainder of the following sum: $$ 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12. $$ Show that it is 2.-/
theorem mathd_numbertheory_239 : (∑ k in Finset.Icc 1 12, k) % 4 = 2 := by
calc
  (∑ k in Finset.Icc 1 12, k) % 4 = 
       (∑ k in Finset.Icc 1 12, k) - 4 * (⌊ (∑ k in Finset.Icc 1 12, k) / 4 ⌋) : by
       simp [Nat.mod_def, Nat.floor_def, Nat.sub_def, Nat.mul_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def, Nat.sub_def, Nat.add_def, Nat.sub_def, Nat.floor_def,