import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, we are given:
1. \( a = -1 \)
2. \( b = 5 \)

We need to evaluate the expression \(-a - b^2 + 3ab\) and show that it equals \(-39\).

#### Step 1: Substitute the given values into the expression.

Substitute \( a = -1 \) and \( b = 5 \) into the expression:
\[
-a - b^2 + 3ab = -(-1) - (5)^2 + 3(-1)(5)
\]

#### Step 2: Simplify the expression.

1. First, simplify \(-a\):
   \[
   -a = -(-1) = 1
   \]
2. Next, simplify \( b^2 \):
   \[
   b^2 = 5^2 = 25
   \]
3. Then, simplify \( 3ab \):
   \[
   3ab = 3(-1)(5) = -15
   \]
4. Combine all the simplified terms:
   \[
   -a - b^2 + 3ab = 1 - 25 - 15 = 1 - 40 = -39
   \]

Thus, the value of \(-a - b^2 + 3ab\) is \(-39\).

### Step-by-Step Abstract Plan

1. **Substitute the given values**:
   - Replace \( a \) with \(-1\) and \( b \) with \(5\) in the expression.

2. **Simplify each term**:
   - Compute \(-a = 1\) because \( a = -1 \).
   - Compute \( b^2 = 25 \) because \( b = 5 \).
   - Compute \( 3ab = -15 \) because \( a = -1 \) and \( b = 5 \).

3. **Combine the simplified terms**:
   - Add the simplified terms together: \( 1 - 25 - 15 = -39 \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_419 (a b : ℝ) (h₀ : a = -1) (h₁ : b = 5) : -a - b ^ 2 + 3 * (a * b) = -39 := by
  have h₂ : -a - b ^ 2 + 3 * (a * b) = -39 := by
    sorry
  sorry
```

This `have` statement directly reflects the final simplified form of the expression, and the proof can be completed by substituting the given values and simplifying.

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_419 (a b : ℝ) (h₀ : a = -1) (h₁ : b = 5) : -a - b ^ 2 + 3 * (a * b) = -39 := by
  have h₂ : -a - b ^ 2 + 3 * (a * b) = -39 := by
    subst_vars
    norm_num
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  exact h₂
