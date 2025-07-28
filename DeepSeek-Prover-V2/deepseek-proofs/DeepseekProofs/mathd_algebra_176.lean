import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof

**Problem:** Expand and simplify \((x + 1)^2 \cdot x\) to show that it equals \(x^3 + 2x^2 + x\).

**Approach:**
1. First, expand \((x + 1)^2\) using the binomial theorem:
   \[
   (x + 1)^2 = x^2 + 2x + 1.
   \]
2. Multiply the expanded form by \(x\):
   \[
   (x^2 + 2x + 1) \cdot x = x^3 + 2x^2 + x.
   \]
3. The result is the desired polynomial.

Alternatively, we can directly expand \((x + 1)^2 \cdot x\) using the distributive property:
\[
(x + 1)^2 \cdot x = (x^2 + 2x + 1) \cdot x = x^3 + 2x^2 + x.
\]

### Step-by-Step Abstract Plan

1. **Expand \((x + 1)^2\):**
   - Use the binomial theorem to get \(x^2 + 2x + 1\).

2. **Multiply by \(x\):**
   - Distribute \(x\) over the expanded form to get \(x^3 + 2x^2 + x\).

3. **Verify the result:**
   - Confirm that the simplified form matches the target polynomial.

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
  have h_main : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
  have h_main : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by
    -- Expand the square and then multiply by x
    have h1 : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
      ring
    rw [h1]
    -- Now multiply the expanded form by x
    ring
    <;>
    linarith
  
  exact h_main
