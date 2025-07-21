import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem:** Find the value of \(-a - b^2 + 3ab\) if \(a = -1\) and \(b = 5\). Show that it is \(-39\).

**Solution:**

1. Substitute \(a = -1\) and \(b = 5\) into the expression \(-a - b^2 + 3ab\):
   \[
   -a - b^2 + 3ab = -(-1) - (5)^2 + 3(-1)(5).
   \]
2. Simplify each term:
   - \(-a = -(-1) = 1\) (since \(a = -1\) and \(-(-1) = 1\)).
   - \(-b^2 = -(5)^2 = -25\).
   - \(3ab = 3(-1)(5) = -15\).
3. Combine the simplified terms:
   \[
   1 - 25 - 15 = 1 - 40 = -39.
   \]
Thus, the value of \(-a - b^2 + 3ab\) is \(-39\).

### Step-by-Step Abstract Plan

1. **Substitute the given values:**
   - Replace \(a\) with \(-1\) and \(b\) with \(5\) in the expression \(-a - b^2 + 3ab\).

2. **Simplify each term:**
   - Compute \(-a = 1\) (since \(a = -1\) and \(-(-1) = 1\)).
   - Compute \(-b^2 = -25\) (since \(b = 5\) and \(5^2 = 25\)).
   - Compute \(3ab = -15\) (since \(a = -1\) and \(b = 5\), so \(3 \cdot (-1) \cdot 5 = -15\)).

3. **Combine the simplified terms:**
   - Add the results: \(1 + (-25) + (-15) = 1 - 40 = -39\).

4. **Final result:**
   - The value of \(-a - b^2 + 3ab\) is \(-39\).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_419
  (a b : ℝ)
  (h₀ : a = -1)
  (h₁ : b = 5) :
  -a - b^2 + 3 * (a * b) = -39 := by
  have h_main : -a - b^2 + 3 * (a * b) = -39 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_419
  (a b : ℝ)
  (h₀ : a = -1)
  (h₁ : b = 5) :
  -a - b^2 + 3 * (a * b) = -39 := by
  have h_main : -a - b^2 + 3 * (a * b) = -39 := by
    subst_vars
    norm_num
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  exact h_main
```