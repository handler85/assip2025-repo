import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We need to find the number of integers between 15 and 85 (inclusive) that are divisible by 20. 

**Approach:**
1. Find the smallest integer ≥ 15 that is divisible by 20. This is 20.
2. Find the largest integer ≤ 85 that is divisible by 20. This is 80.
3. The integers divisible by 20 between 15 and 85 are those in the arithmetic sequence 20, 40, 60, 80.
4. The number of terms is 4.

**Verification:**
- The smallest integer ≥ 15 and divisible by 20 is 20.
- The largest integer ≤ 85 and divisible by 20 is 80.
- The number of terms in the arithmetic sequence 20, 40, 60, 80 is 4.

**Conclusion:**
The number of integers between 15 and 85 that are divisible by 20 is 4.

### Step-by-Step Abstract Plan

1. **Find the smallest integer ≥ 15 divisible by 20:**
   - 15 ÷ 20 = 0.75 → 20 is the smallest integer ≥ 15 divisible by 20.

2. **Find the largest integer ≤ 85 divisible by 20:**
   - 85 ÷ 20 = 4.25 → 80 is the largest integer ≤ 85 divisible by 20.

3. **List all integers divisible by 20 between 15 and 85:**
   - 20, 40, 60, 80.

4. **Count the number of terms:**
   - There are 4 terms.

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_numbertheory_12 :
  Finset.card (Finset.filter (λ x => 20∣x) (Finset.Icc 15 85)) = 4 := by
  have h_main : Finset.card (Finset.filter (λ x => 20∣x) (Finset.Icc 15 85)) = 4 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_numbertheory_12 :
  Finset.card (Finset.filter (λ x => 20∣x) (Finset.Icc 15 85)) = 4 := by
  have h_main : Finset.card (Finset.filter (λ x => 20∣x) (Finset.Icc 15 85)) = 4 := by
    rfl
    <;> decide
    <;> simp_all (config := {decide := true})
    <;> decide
  
  exact h_main
```