import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We need to prove that for any real number \( x \), if \( |x - 1| + |x| + |x + 1| = x + 2 \), then \( 0 \leq x \leq 1 \).

**Key Observations:**
1. The expression \( |x - 1| + |x| + |x + 1| \) is piecewise linear in \( x \), and its behavior changes at the points where the expressions inside the absolute values are zero, i.e., at \( x = -1 \), \( x = 0 \), and \( x = 1 \).
2. The condition \( |x - 1| + |x| + |x + 1| = x + 2 \) can be analyzed by considering different cases based on the value of \( x \).

**Case Analysis:**
We consider the possible ranges of \( x \) based on the critical points \( x = -1 \), \( x = 0 \), and \( x = 1 \).

1. **Case \( x \leq -1 \):**
   - \( x - 1 \leq -2 < 0 \), so \( |x - 1| = 1 - x \).
   - \( x \leq -1 < 0 \), so \( |x| = -x \).
   - \( x + 1 \leq 0 \), so \( |x + 1| = -(x + 1) = -x - 1 \).
   - The left-hand side (LHS) becomes:
     \[
     |x - 1| + |x| + |x + 1| = (1 - x) + (-x) + (-x - 1) = 1 - x - x - x - 1 = -3x.
     \]
   - The right-hand side (RHS) is:
     \[
     x + 2.
     \]
   - The equation becomes:
     \[
     -3x = x + 2.
     \]
   - Solving:
     \[
     -3x - x = 2 \implies -4x = 2 \implies x = -\frac{1}{2}.
     \]
   - But \( x \leq -1 \) and \( x = -\frac{1}{2} \) is a contradiction. Hence, no solution in this case.

2. **Case \( -1 \leq x \leq 0 \):**
   - \( x - 1 \leq 0 \), so \( |x - 1| = 1 - x \).
   - \( x \leq 0 \), so \( |x| = -x \).
   - \( x + 1 \geq 0 \), so \( |x + 1| = x + 1 \).
   - The LHS becomes:
     \[
     |x - 1| + |x| + |x + 1| = (1 - x) + (-x) + (x + 1) = 1 - x - x + x + 1 = 2.
     \]
   - The RHS is:
     \[
     x + 2.
     \]
   - The equation becomes:
     \[
     2 = x + 2.
     \]
   - Solving:
     \[
     2 - 2 = x \implies x = 0.
     \]
   - Since \( x = 0 \) is within \( -1 \leq x \leq 0 \), this is a valid solution.

3. **Case \( 0 \leq x \leq 1 \):**
   - \( x - 1 \leq 0 \), so \( |x - 1| = 1 - x \).
   - \( x \geq 0 \), so \( |x| = x \).
   - \( x + 1 \geq 0 \), so \( |x + 1| = x + 1 \).
   - The LHS becomes:
     \[
     |x - 1| + |x| + |x + 1| = (1 - x) + x + (x + 1) = 1 - x + x + x + 1 = 2 + x.
     \]
   - The RHS is:
     \[
     x + 2.
     \]
   - The equation becomes:
     \[
     2 + x = x + 2.
     \]
   - This is always true, so all \( x \in [0, 1] \) are solutions.

4. **Case \( x \geq 1 \):**
   - \( x - 1 \geq 0 \), so \( |x - 1| = x - 1 \).
   - \( x \geq 0 \), so \( |x| = x \).
   - \( x + 1 \geq 0 \), so \( |x + 1| = x + 1 \).
   - The LHS becomes:
     \[
     |x - 1| + |x| + |x + 1| = (x - 1) + x + (x + 1) = x - 1 + x + x + 1 = 3x.
     \]
   - The RHS is:
     \[
     x + 2.
     \]
   - The equation becomes:
     \[
     3x = x + 2.
     \]
   - Solving:
     \[
     3x - x = 2 \implies 2x = 2 \implies x = 1.
     \]
   - Since \( x \geq 1 \) and \( x = 1 \) is within \( x \geq 1 \), this is a valid solution.

**Conclusion:**
The only solutions to the equation \( |x - 1| + |x| + |x + 1| = x + 2 \) are \( x = 0 \) and \( x = 1 \). Therefore, the condition \( 0 \leq x \leq 1 \) is necessary and sufficient.

### Step-by-Step Abstract Plan

1. **Understand the Problem:**
   - We need to find all real numbers \( x \) that satisfy \( |x - 1| + |x| + |x + 1| = x + 2 \).
   - The solution set is \( [0, 1] \).

2. **Break Down the Problem:**
   - The expression \( |x - 1| + |x| + |x + 1| \) is piecewise linear, and its behavior changes at \( x = -1 \), \( x = 0 \), and \( x = 1 \).
   - We can analyze the equation by considering different intervals for \( x \).

3. **Case Analysis:**
   - **Case 1:** \( x \leq -1 \)
     - Compute \( |x - 1| + |x| + |x + 1| \) and set it equal to \( x + 2 \).
     - Find that no solution exists in this interval.
   - **Case 2:** \( -1 \leq x \leq 0 \)
     - Compute \( |x - 1| + |x| + |x + 1| \) and set it equal to \( x + 2 \).
     - Find that \( x = 0 \) is the only solution in this interval.
   - **Case 3:** \( 0 \leq x \leq 1 \)
     - Compute \( |x - 1| + |x| + |x + 1| \) and set it equal to \( x + 2 \).
     - Find that all \( x \in [0, 1] \) are solutions.
   - **Case 4:** \( x \geq 1 \)
     - Compute \( |x - 1| + |x| + |x + 1| \) and set it equal to \( x + 2 \).
     - Find that \( x = 1 \) is the only solution in this interval.

4. **Conclusion:**
   - The only real numbers \( x \) that satisfy the equation \( |x - 1| + |x| + |x + 1| = x + 2 \) are \( x = 0 \) and \( x = 1 \).
   - Therefore, the condition \( 0 \leq x \leq 1 \) is necessary and sufficient.

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  have h_main : 0 ≤ x ∧ x ≤ 1 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  have h_main : 0 ≤ x ∧ x ≤ 1 := by
    by_cases h₁ : x ≤ -1
    · -- Case 1: x ≤ -1
      have h₂ : abs (x - 1) = 1 - x := by
        rw [abs_of_nonpos] <;> linarith
      have h₃ : abs x = -x := by
        rw [abs_of_nonpos] <;> linarith
      have h₄ : abs (x + 1) = -(x + 1) := by
        rw [abs_of_nonpos] <;> linarith
      rw [h₂, h₃, h₄] at h₀
      norm_num at h₀
      <;> nlinarith
    · -- Case 2: x > -1
      by_cases h₂ : x ≤ 0
      · -- Subcase 2.1: -1 < x ≤ 0
        have h₃ : abs (x - 1) = 1 - x := by
          rw [abs_of_nonpos] <;> linarith
        have h₄ : abs x = -x := by
          rw [abs_of_nonpos] <;> linarith
        have h₅ : abs (x + 1) = x + 1 := by
          rw [abs_of_nonneg] <;> linarith
        rw [h₃, h₄, h₅] at h₀
        norm_num at h₀
        <;> nlinarith
      · -- Subcase 2.2: x > 0
        have h₃ : abs (x - 1) = x - 1 := by
          rw [abs_of_nonneg] <;> linarith
        have h₄ : abs x = x := by
          rw [abs_of_nonneg] <;> linarith
        have h₅ : abs (x + 1) = x + 1 := by
          rw [abs_of_nonneg] <;> linarith
        rw [h₃, h₄, h₅] at h₀
        norm_num at h₀
        <;> nlinarith
  exact h_main
```