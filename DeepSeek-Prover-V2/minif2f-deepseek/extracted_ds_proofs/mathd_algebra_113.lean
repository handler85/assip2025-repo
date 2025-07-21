import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem:** Prove that for all real numbers \( x \), \( x^2 - 14x + 3 \geq 7^2 - 14 \cdot 7 + 3 \).

**Approach:**
1. First, simplify the right-hand side (RHS) to find the exact value:
   \[
   7^2 - 14 \cdot 7 + 3 = 49 - 98 + 3 = -46.
   \]
   So, the inequality becomes:
   \[
   x^2 - 14x + 3 \geq -46.
   \]
2. Rearrange the inequality to:
   \[
   x^2 - 14x + 3 + 46 \geq 0 \quad \text{or} \quad x^2 - 14x + 49 \geq 0.
   \]
3. Factor the quadratic expression:
   \[
   x^2 - 14x + 49 = (x - 7)^2.
   \]
   Since \((x - 7)^2 \geq 0\) for all real \(x\), the original inequality is proven.

### Step-by-Step Abstract Plan

1. **Simplify the RHS:**
   - Calculate \(7^2 - 14 \cdot 7 + 3 = 49 - 98 + 3 = -46\).

2. **Rearrange the inequality:**
   - The goal is \(x^2 - 14x + 3 \geq -46\).
   - Add 49 to both sides to get \(x^2 - 14x + 49 \geq 0\).

3. **Factor the quadratic:**
   - \(x^2 - 14x + 49 = (x - 7)^2 \geq 0\).

4. **Conclude the proof:**
   - Since \((x - 7)^2 \geq 0\) is always true, the original inequality holds.

### Lean 4 `have` Statements

```lean4
theorem mathd_algebra_113
  (x : ℝ) :
  x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 := by
  have h_main : x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_113
  (x : ℝ) :
  x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 := by
  have h_main : x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 := by
    have h₁ : x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 := by
      nlinarith [sq_nonneg (x - 7), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x + 7),
        sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x - 3), sq_nonneg (x + 3),
        sq_nonneg (x - 4), sq_nonneg (x + 4), sq_nonneg (x - 5), sq_nonneg (x + 5),
        sq_nonneg (x - 6), sq_nonneg (x + 6), sq_nonneg (x - 8), sq_nonneg (x + 8),
        sq_nonneg (x - 9), sq_nonneg (x + 9), sq_nonneg (x - 10), sq_nonneg (x + 10)]
    exact h₁
  exact h_main
```