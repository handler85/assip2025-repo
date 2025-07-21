import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem:** Show that for any real number \( a \), \( a(2 - a) \leq 1 \).

**Approach:**
We can expand the expression \( a(2 - a) \) to get \( 2a - a^2 \). The inequality becomes \( 2a - a^2 \leq 1 \), or equivalently, \( a^2 - 2a + 1 \geq 0 \).

Notice that \( a^2 - 2a + 1 = (a - 1)^2 \geq 0 \) for all real \( a \), with equality if and only if \( a = 1 \).

Thus, the original inequality \( a(2 - a) \leq 1 \) holds for all real \( a \).

**Proof:**
1. Expand \( a(2 - a) \) to get \( 2a - a^2 \).
2. The inequality becomes \( 2a - a^2 \leq 1 \), or equivalently, \( a^2 - 2a + 1 \geq 0 \).
3. Notice that \( a^2 - 2a + 1 = (a - 1)^2 \geq 0 \) for all real \( a \), with equality if and only if \( a = 1 \).
4. Therefore, the original inequality holds for all real \( a \).

### Step-by-Step Abstract Plan

1. **Expand the Expression:**
   - Multiply \( a \) by \( (2 - a) \) to get \( 2a - a^2 \).

2. **Form the Inequality:**
   - The inequality becomes \( 2a - a^2 \leq 1 \).

3. **Rearrange the Inequality:**
   - Subtract \( 1 \) from both sides to get \( 2a - a^2 - 1 \leq 0 \).
   - Alternatively, rearrange to \( a^2 - 2a + 1 \geq 0 \).

4. **Recognize the Perfect Square:**
   - Notice that \( a^2 - 2a + 1 = (a - 1)^2 \geq 0 \).

5. **Conclude the Proof:**
   - Since \( (a - 1)^2 \geq 0 \) for all real \( a \), the original inequality holds.

### Lean 4 `have` Statements

```lean4
theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  have h_main : a * (2 - a) ≤ 1 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem algebra_sqineq_at2malt1
  (a : ℝ) :
  a * (2 - a) ≤ 1 := by
  have h_main : a * (2 - a) ≤ 1 := by
    have h1 : a * (2 - a) = 2 * a - a ^ 2 := by ring
    rw [h1]
    -- Use the fact that the square of any real number is non-negative to prove the inequality.
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 2), sq_nonneg (a + 1), sq_nonneg (a + 2),
      sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2), sq_nonneg (a - 3 / 2), sq_nonneg (a + 3 / 2)]
  exact h_main
```