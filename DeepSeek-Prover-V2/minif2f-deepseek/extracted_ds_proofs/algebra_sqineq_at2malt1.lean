import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/-
### Detailed Proof

**Problem:** Prove that for any real number \( a \), \( a(2 - a) \leq 1 \).

**Approach:**
We can rewrite the inequality as:
\[ a(2 - a) \leq 1 \]
\[ 2a - a^2 \leq 1 \]
\[ -a^2 + 2a - 1 \leq 0 \]
\[ a^2 - 2a + 1 \geq 0 \]

Notice that \( a^2 - 2a + 1 = (a - 1)^2 \geq 0 \) for all real \( a \), with equality when \( a = 1 \).

Thus, the original inequality \( a(2 - a) \leq 1 \) holds for all real \( a \).

**Proof:**
1. Start with the inequality \( a(2 - a) \leq 1 \).
2. Expand the left-hand side to get \( 2a - a^2 \leq 1 \).
3. Rearrange to \( -a^2 + 2a - 1 \leq 0 \).
4. Multiply by \(-1\) (and reverse the inequality) to get \( a^2 - 2a + 1 \geq 0 \).
5. Notice that \( a^2 - 2a + 1 = (a - 1)^2 \geq 0 \), which is always true.
6. Therefore, the original inequality holds for all real \( a \).

### Step-by-Step Abstract Plan

1. **Expand the Expression**:
   - Multiply \( a \) by \( (2 - a) \) to get \( 2a - a^2 \).

2. **Rearrange the Inequality**:
   - Move all terms to one side to form \( 2a - a^2 - 1 \leq 0 \).

3. **Complete the Square**:
   - Rewrite the quadratic as \( a^2 - 2a + 1 \geq 0 \).
   - Factor it as \( (a - 1)^2 \geq 0 \).

4. **Verify the Final Form**:
   - The square of any real number is always non-negative, so the inequality holds.

### Lean 4 `have` Statements

```lean4
theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h_main : a * (2 - a) ≤ 1 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h_main : a * (2 - a) ≤ 1 := by
    have h1 : a * (2 - a) = 2 * a - a ^ 2 := by ring
    rw [h1]
    have h2 : 2 * a - a ^ 2 ≤ 1 := by
      -- Use the fact that the square of any real number is non-negative to prove the inequality.
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 2), sq_nonneg (a + 1), sq_nonneg (a + 2)]
    exact h2
  exact h_main
