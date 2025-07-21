import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem:** Expand the product \((x + 1)^2 \cdot x\) and show that it is equal to \(x^3 + 2x^2 + x\).

**Solution:**

1. First, expand \((x + 1)^2\):
   \[
   (x + 1)^2 = x^2 + 2x + 1.
   \]
2. Multiply the expanded form by \(x\):
   \[
   (x^2 + 2x + 1) \cdot x = x^3 + 2x^2 + x.
   \]
3. The result is \(x^3 + 2x^2 + x\), as desired.

### Step-by-Step Abstract Plan

1. **Expand \((x + 1)^2\):**
   - Use the binomial square formula to get \(x^2 + 2x + 1\).

2. **Multiply by \(x\):**
   - Distribute \(x\) over the expanded form to get \(x^3 + 2x^2 + x\).

3. **Verify the result:**
   - The product \((x + 1)^2 \cdot x\) simplifies to \(x^3 + 2x^2 + x\).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_176
  (x : ℝ) :
  (x + 1)^2 * x = x^3 + 2 * x^2 + x := by
  have h_main : (x + 1)^2 * x = x^3 + 2 * x^2 + x := by
    sorry
  sorry
```

This `have` statement directly corresponds to the main goal of the proof. The `sorry` inside it can be replaced by the detailed expansion and multiplication steps outlined above. The final `sorry` is trivial because `h_main` is exactly the goal.

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_176
  (x : ℝ) :
  (x + 1)^2 * x = x^3 + 2 * x^2 + x := by
  have h_main : (x + 1)^2 * x = x^3 + 2 * x^2 + x := by
    -- Expand the square and multiply by x
    have h1 : (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
      ring
    rw [h1]
    -- Distribute x and simplify
    ring
    <;>
    linarith
  
  exact h_main
```