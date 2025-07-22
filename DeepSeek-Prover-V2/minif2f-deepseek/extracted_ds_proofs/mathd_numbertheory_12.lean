import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, we need to find all integers between 15 and 85 (inclusive) that are divisible by 20. 

1. **Understand the Problem**:
   - We are looking for integers `x` such that `15 ≤ x ≤ 85` and `20` divides `x` (i.e., `20 ∣ x`).
   - This means `x` is a multiple of `20` within the range `[15, 85]`.

2. **Find Multiples of 20 in the Range**:
   - The smallest multiple of `20` ≥ `15` is `20` itself.
   - The largest multiple of `20` ≤ `85` is `80` (since `80 = 20 * 4` and `100 > 85`).
   - The multiples of `20` in `[15, 85]` are `20, 40, 60, 80`.

3. **Count the Multiples**:
   - There are `4` multiples of `20` in the range `[15, 85]`.

4. **Verification**:
   - `20 / 20 = 1`
   - `40 / 20 = 2`
   - `60 / 20 = 3`
   - `80 / 20 = 4`
   - No other multiples of `20` are in the range.

### Step 1: Abstract Plan

1. **Find the smallest `x` such that `15 ≤ x` and `20 ∣ x`**:
   - The smallest `x` is `20`.

2. **Find the largest `x` such that `x ≤ 85` and `20 ∣ x`**:
   - The largest `x` is `80`.

3. **List all multiples of `20` in the range `[15, 85]`**:
   - `20, 40, 60, 80`.

4. **Count the number of multiples**:
   - There are `4` multiples.

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
  have h_main : Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
  have h_main : Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by
    rfl
    <;> decide
    <;> simp_all [Finset.filter_eq']
    <;> decide
  
  exact h_main
