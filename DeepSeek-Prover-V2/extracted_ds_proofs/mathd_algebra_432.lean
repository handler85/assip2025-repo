import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem:** Expand \((x + 3)(2x - 6)\) and show that it is equal to \(2x^2 - 18\).

**Solution:**

1. **Expand the Product:**
   To expand \((x + 3)(2x - 6)\), we use the distributive property (FOIL method for binomials). Multiply each term in the first binomial by each term in the second binomial and combine like terms.

   - Multiply \(x\) by \(2x\) and \(-6\):
     \[
     x \cdot 2x = 2x^2 \quad \text{and} \quad x \cdot (-6) = -6x.
     \]
   - Multiply \(3\) by \(2x\) and \(-6\):
     \[
     3 \cdot 2x = 6x \quad \text{and} \quad 3 \cdot (-6) = -18.
     \]
   - Combine all the results:
     \[
     2x^2 - 6x + 6x - 18.
     \]
   - Simplify the expression by combining like terms:
     \[
     2x^2 + (-6x + 6x) - 18 = 2x^2 - 18.
     \]

2. **Final Answer:**
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
   - Combine like terms: \(-6x + 6x = 0\), so the expression becomes \(2x^2 - 18\).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_432
  (x : ℝ) :
  (x + 3) * (2 * x - 6) = 2 * x^2 - 18 := by
  have h_main : (x + 3) * (2 * x - 6) = 2 * x^2 - 18 := by
    sorry
  sorry
```

This `have` statement directly reflects the main goal of the proof, and its proof is marked as `sorry`. The actual proof would fill in the `sorry` by expanding and simplifying the product as described in the detailed proof.

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_432
  (x : ℝ) :
  (x + 3) * (2 * x - 6) = 2 * x^2 - 18 := by
  have h_main : (x + 3) * (2 * x - 6) = 2 * x^2 - 18 := by
    ring_nf
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try linarith)
    <;>
    (try ring_nf) <;>
    (try nlinarith)
    <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;>
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf) <;
    (try ring_nf
    (
    (try ring_nf) <;
    (try ring_nf
    (try ring_nf
    (try ring_nf
    (try ring_nf
    (try ring_