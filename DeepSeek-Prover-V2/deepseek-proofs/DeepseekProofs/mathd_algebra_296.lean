import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof

**Problem Analysis:**
We need to find the absolute value of the difference between the new area and the original area of a square. The original square has side length 3491. The new dimensions are:
- Length: 3491 - 60 = 3431
- Width: 3491 + 60 = 3551

The original area is \( A_{\text{original}} = 3491^2 \). The new area is \( A_{\text{new}} = 3431 \times 3551 \).

We need to compute \( |A_{\text{new}} - A_{\text{original}}| \).

**Key Observations:**
1. \( 3431 = 3491 - 60 \)
2. \( 3551 = 3491 + 60 \)
3. \( A_{\text{new}} = 3431 \times 3551 = (3491 - 60)(3491 + 60) = 3491^2 - 60^2 \).

This is because:
\[
(3491 - 60)(3491 + 60) = 3491^2 - 60^2.
\]

Thus:
\[
A_{\text{new}} - A_{\text{original}} = (3491^2 - 60^2) - 3491^2 = -60^2 = -3600.
\]
Therefore:
\[
|A_{\text{new}} - A_{\text{original}}| = | -3600 | = 3600.
\]

**Verification:**
1. \( 3431 \times 3551 = (3491 - 60)(3491 + 60) = 3491^2 - 60^2 \).
2. \( 3491^2 - 60^2 - 3491^2 = -3600 \).
3. \( | -3600 | = 3600 \).

### Step 1: Abstract Plan

1. **Understand the Problem**:
   - We have a square with side length 3491.
   - The length is decreased by 60, and the width is increased by 60.
   - We need to find the change in area and show it is 3600.

2. **Calculate New Dimensions and Area**:
   - New length: \( 3491 - 60 = 3431 \).
   - New width: \( 3491 + 60 = 3551 \).
   - New area: \( 3431 \times 3551 \).

3. **Find the Difference in Area**:
   - Original area: \( 3491^2 \).
   - New area: \( 3431 \times 3551 = 3491^2 - 60^2 \).
   - Difference: \( (3491^2 - 60^2) - 3491^2 = -60^2 = -3600 \).

4. **Take Absolute Value**:
   - \( | -3600 | = 3600 \).

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by
  have h_main : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by
  have h_main : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 := by
    norm_num [abs_eq, Int.mul_emod, Int.sub_emod, Int.add_emod, pow_two]
    <;>
    (try decide) <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try omega)
    <;>
    aesop
  
  exact h_main
