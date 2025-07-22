import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem:** Expand \((x + 3)(2x - 6)\) and show that it is equal to \(2x^2 - 18\).

**Solution:**

1. **Expand the Product:**
   To expand \((x + 3)(2x - 6)\), we use the distributive property (FOIL method for binomials). Multiply each term in the first binomial by each term in the second binomial and then combine like terms.

   - Multiply \(x\) by \(2x\) and \(-6\):
     \[
     x \cdot 2x = 2x^2
     \]
     \[
     x \cdot (-6) = -6x
     \]
   - Multiply \(3\) by \(2x\) and \(-6\):
     \[
     3 \cdot 2x = 6x
     \]
     \[
     3 \cdot (-6) = -18
     \]
   - Combine all the results:
     \[
     2x^2 - 6x + 6x - 18
     \]
   - Simplify the expression:
     \[
     2x^2 - 6x + 6x - 18 = 2x^2 - 18
     \]

2. **Conclusion:**
   The expanded form of \((x + 3)(2x - 6)\) is \(2x^2 - 18\).

### Step-by-Step Abstract Plan

1. **Expand the Product:**
   - Multiply each term in the first binomial \((x + 3)\) by each term in the second binomial \((2x - 6)\).
   - This gives four products: \(x \cdot 2x\), \(x \cdot (-6)\), \(3 \cdot 2x\), and \(3 \cdot (-6)\).

2. **Combine the Results:**
   - Calculate each product:
     - \(x \cdot 2x = 2x^2\)
     - \(x \cdot (-6) = -6x\)
     - \(3 \cdot 2x = 6x\)
     - \(3 \cdot (-6) = -18\)
   - Write the sum of all products: \(2x^2 - 6x + 6x - 18\).

3. **Simplify the Expression:**
   - Combine like terms: \(-6x + 6x = 0\).
   - The expression simplifies to \(2x^2 - 18\).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_432 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by
  have h_main : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_432 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by
  have h_main : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by
    ring_nf
    <;>
    nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 3), sq_nonneg (2 * x - 6), sq_nonneg (2 * x + 6)]
  
  exact h_main
```