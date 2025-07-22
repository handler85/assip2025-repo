import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, we need to prove that:
\[ a^2 b (a - b) + b^2 c (b - c) + c^2 a (c - a) \geq 0 \]
under the conditions:
1. \( a, b, c > 0 \),
2. \( c < a + b \),
3. \( b < a + c \),
4. \( a < b + c \).

This is a symmetric inequality, but the terms are not symmetric due to the coefficients. We can attempt to rewrite the expression to make it more manageable.

#### Step 1: Expand the Expression
First, expand each term:
\[ a^2 b (a - b) = a^3 b - a^2 b^2 \]
\[ b^2 c (b - c) = b^3 c - b^2 c^2 \]
\[ c^2 a (c - a) = c^3 a - c^2 a^2 \]

Now, add them together:
\[ (a^3 b - a^2 b^2) + (b^3 c - b^2 c^2) + (c^3 a - c^2 a^2) \]
\[ = a^3 b + b^3 c + c^3 a - a^2 b^2 - b^2 c^2 - c^2 a^2 \]

#### Step 2: Symmetric Rearrangement
The expression is not symmetric, but we can try to find a symmetric lower bound. Notice that:
\[ a^3 b + b^3 c + c^3 a \geq a^2 b^2 + b^2 c^2 + c^2 a^2 \]
is equivalent to:
\[ a^3 b - a^2 b^2 + b^3 c - b^2 c^2 + c^3 a - c^2 a^2 \geq 0 \]
which is exactly our original expression. 

But we need to prove:
\[ a^3 b + b^3 c + c^3 a \geq a^2 b^2 + b^2 c^2 + c^2 a^2 \]

#### Step 3: Prove the Symmetric Inequality
We can use the **rearrangement inequality** or **Muirhead's inequality**. The left-hand side is a sum of terms of the form \( x^3 y \), while the right-hand side is a sum of terms of the form \( x^2 y^2 \). The majorization condition is:
\[ (a, b, c) \succ (a, b, c) \]
but we need to compare the sequences:
\[ (a^3, b^3, c^3) \succ (a^2, b^2, c^2) \]
This is true because \( a^3 + b^3 + c^3 \geq a^2 + b^2 + c^2 \) under the given conditions (since \( a, b, c > 0 \)).

But we can also prove it directly:
\[ a^3 b + b^3 c + c^3 a \geq a^2 b^2 + b^2 c^2 + c^2 a^2 \]
is equivalent to:
\[ a^3 b - a^2 b^2 + b^3 c - b^2 c^2 + c^3 a - c^2 a^2 \geq 0 \]
Factor each term:
\[ a^2 b (a - b) + b^2 c (b - c) + c^2 a (c - a) \geq 0 \]

But we can also use the **Rearrangement Inequality** to prove this. The expression is symmetric in \( a, b, c \), and the terms \( a^2 b, b^2 c, c^2 a \) can be paired with \( a - b, b - c, c - a \) in a way that gives a non-negative sum.

#### Step 4: Final Proof
We can use the **Rearrangement Inequality** to prove the inequality. The terms \( a^2 b, b^2 c, c^2 a \) are ordered in the same way as \( a, b, c \) (since \( a, b, c > 0 \)), and the differences \( a - b, b - c, c - a \) are ordered in the reverse order. Thus, the sum is minimized when the terms are paired in the same order, i.e., when the differences are paired in the same order. This gives:
\[ a^2 b (a - b) + b^2 c (b - c) + c^2 a (c - a) \geq 0 \]

### Step-by-Step Abstract Plan

1. **Expand the Original Expression**:
   - Expand each term in the original expression to get a sum of simpler terms.

2. **Compare Symmetric Sums**:
   - Compare the expanded form to a symmetric sum that is easier to handle.

3. **Use Rearrangement Inequality**:
   - Apply the Rearrangement Inequality to pair terms in a way that gives a non-negative sum.

4. **Final Inequality**:
   - Combine the results to show that the original expression is non-negative.

### Lean 4 `have` Statements

```lean4
theorem imo_1983_p6 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h_main : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem imo_1983_p6 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  have h_main : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos h₀.1 h₀.2.1, mul_pos h₀.2.1 h₀.2.2, mul_pos h₀.1 h₀.2.2,
      mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₁),
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃), sq_nonneg (a - b - (c - a)),
      sq_nonneg (b - c - (a - b)), sq_nonneg (c - a - (b - c))]
  exact h_main
```