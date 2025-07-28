import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/-
### Detailed Proof and Analysis

**Problem Analysis:**
We need to prove that for any real number \( x \), if \( |x - 1| + |x| + |x + 1| = x + 2 \), then \( 0 \leq x \leq 1 \).

**Key Observations:**
1. The expression \( |x - 1| + |x| + |x + 1| \) is piecewise linear in \( x \), and its behavior changes at the points where the expressions inside the absolute values are zero, i.e., at \( x = -1 \), \( x = 0 \), and \( x = 1 \).
2. The condition \( |x - 1| + |x| + |x + 1| = x + 2 \) can be analyzed by considering different intervals for \( x \):
   - \( x < -1 \)
   - \( -1 \leq x < 0 \)
   - \( 0 \leq x < 1 \)
   - \( x \geq 1 \)
3. The solution \( x \) must lie in the interval \([0, 1]\) because:
   - For \( x < 0 \), the left-hand side (LHS) is too small compared to the right-hand side (RHS).
   - For \( x > 1 \), the LHS is too large compared to the RHS.
   - The only interval where the LHS equals the RHS is \([0, 1]\).

**Proof Sketch:**
1. Assume \( x < 0 \). We will show that the LHS is less than the RHS.
2. Assume \( x > 1 \). We will show that the LHS is greater than the RHS.
3. Assume \( 0 \leq x \leq 1 \). We will show that the LHS equals the RHS.
4. The only interval where the LHS equals the RHS is \([0, 1]\).

**Detailed Proof:**

1. **Case \( x < 0 \):**
   - \( |x - 1| = 1 - x \) (since \( x < 0 < 1 \))
   - \( |x| = -x \) (since \( x < 0 \))
   - \( |x + 1| = -(x + 1) = -x - 1 \) (since \( x < -1 \))
   - The LHS becomes:
     \[
     (1 - x) + (-x) + (-x - 1) = 1 - x - x - x - 1 = -3x
     \]
   - The RHS is:
     \[
     x + 2
     \]
   - The equation becomes:
     \[
     -3x = x + 2
     \]
     \[
     -4x = 2
     \]
     \[
     x = -\frac{1}{2}
     \]
   - But \( x < 0 \), and \( x = -\frac{1}{2} \) is not less than \( 0 \). This is a contradiction. Hence, our assumption is false, and \( x \geq 0 \) must hold.

2. **Case \( x > 1 \):**
   - \( |x - 1| = x - 1 \) (since \( x > 1 \))
   - \( |x| = x \) (since \( x > 0 \))
   - \( |x + 1| = x + 1 \) (since \( x > -1 \))
   - The LHS becomes:
     \[
     (x - 1) + x + (x + 1) = 3x
     \]
   - The RHS is:
     \[
     x + 2
     \]
   - The equation becomes:
     \[
     3x = x + 2
     \]
     \[
     2x = 2
     \]
     \[
     x = 1
     \]
   - But \( x > 1 \), and \( x = 1 \) is not greater than \( 1 \). This is a contradiction. Hence, our assumption is false, and \( x \leq 1 \) must hold.

3. **Case \( 0 \leq x \leq 1 \):**
   - \( |x - 1| = 1 - x \) (since \( x \leq 1 \))
   - \( |x| = x \) (since \( x \geq 0 \))
   - \( |x + 1| = x + 1 \) (since \( x \geq -1 \))
   - The LHS becomes:
     \[
     (1 - x) + x + (x + 1) = 2 + x
     \]
   - The RHS is:
     \[
     x + 2
     \]
   - The equation becomes:
     \[
     2 + x = x + 2
     \]
     \[
     0 = 0
     \]
   - This is always true. Hence, \( 0 \leq x \leq 1 \) is the solution.

**Conclusion:**
The only real numbers \( x \) satisfying \( |x - 1| + |x| + |x + 1| = x + 2 \) are those in the interval \([0, 1]\).

### Step-by-Step Abstract Plan

1. **Understand the Problem:**
   - We need to find all real numbers \( x \) such that the sum of three absolute value expressions equals \( x + 2 \).

2. **Analyze the Absolute Values:**
   - The expressions inside the absolute values change their behavior at critical points: \( x = -1 \), \( x = 0 \), and \( x = 1 \).
   - These points divide the real line into four intervals: \( x < -1 \), \( -1 \leq x < 0 \), \( 0 \leq x < 1 \), and \( x \geq 1 \).

3. **Evaluate the Sum in Each Interval:**
   - For each interval, simplify the absolute value expressions and compute the sum.
   - Compare the result with \( x + 2 \).

4. **Find the Solution:**
   - The only interval where the sum equals \( x + 2 \) is \( 0 \leq x \leq 1 \).
   - Therefore, the solution is \( 0 \leq x \leq 1 \).

### Lean 4 `have` Statements

```lean4
theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  have h_main : 0 ≤ x ∧ x ≤ 1 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by
  have h_main : 0 ≤ x ∧ x ≤ 1 := by
    -- Consider different cases for the value of x
    cases' le_total 0 (x - 1) with h h <;>
    cases' le_total 0 x with h₂ h₂ <;>
    cases' le_total 0 (x + 1) with h₃ h₃ <;>
    -- Simplify the absolute values based on the cases
    simp_all only [abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos] <;>
    -- Construct the proof for each case
    (try { contradiction }) <;>
    (try { linarith }) <;>
    (try { exact ⟨by linarith, by linarith⟩ }) <;>
    (try { exact ⟨by linarith, by linarith⟩ })
  exact h_main
