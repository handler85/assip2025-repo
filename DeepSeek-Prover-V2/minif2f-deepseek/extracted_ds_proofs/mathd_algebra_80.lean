import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem:** Solve \(\frac{x - 9}{x + 1} = 2\) for \(x \neq -1\) and show that \(x = -11\).

**Solution:**

1. Start with the equation:
   \[
   \frac{x - 9}{x + 1} = 2.
   \]
2. Multiply both sides by \(x + 1\) (which is valid since \(x \neq -1\)):
   \[
   x - 9 = 2(x + 1).
   \]
3. Distribute the 2 on the right-hand side:
   \[
   x - 9 = 2x + 2.
   \]
4. Subtract \(x\) from both sides:
   \[
   -9 = x + 2.
   \]
5. Subtract 2 from both sides:
   \[
   -11 = x.
   \]
6. Thus, \(x = -11\) is the solution.

### Step-by-Step Abstract Plan

1. **Multiply both sides by \(x + 1\):**
   - Since \(x \neq -1\), \(x + 1 \neq 0\), and we can safely multiply both sides by \(x + 1\).

2. **Simplify the equation:**
   - The left-hand side becomes \(x - 9\).
   - The right-hand side becomes \(2(x + 1)\).

3. **Expand and rearrange:**
   - Distribute the 2 to get \(2x + 2\).
   - Subtract \(x\) from both sides to get \(-9 = x + 2\).

4. **Isolate \(x\):**
   - Subtract 2 from both sides to get \(-11 = x\).

5. **Verify the solution:**
   - Substitute \(x = -11\) back into the original equation to ensure it holds.

### Lean 4 `have` Statements

```lean4
theorem mathd_algebra_80
  (x : ℝ)
  (h₀ : x ≠ -1)
  (h₁ : (x - 9) / (x + 1) = 2) :
  x = -11 := by
  have h₂ : x + 1 ≠ 0 := by sorry
  have h₃ : x - 9 = 2 * (x + 1) := by sorry
  have h₄ : x = -11 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_80
  (x : ℝ)
  (h₀ : x ≠ -1)
  (h₁ : (x - 9) / (x + 1) = 2) :
  x = -11 := by
  have h₂ : x + 1 ≠ 0 := by
    intro h
    apply h₀
    linarith
  
  have h₃ : x - 9 = 2 * (x + 1) := by
    have h₄ : (x - 9) / (x + 1) = 2 := h₁
    have h₅ : x + 1 ≠ 0 := h₂
    field_simp at h₄
    linarith
  
  have h₄ : x = -11 := by
    have h₅ : x - 9 = 2 * (x + 1) := h₃
    -- Simplify the equation to isolate x
    linarith
  
  exact h₄
```