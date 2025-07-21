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

This is a symmetric inequality, but the terms are not symmetric. We can try to factor or rearrange the expression.

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
\[ a^3 b + b^3 c + c^3 a - a^2 b^2 - b^2 c^2 - c^2 a^2 \geq 0 \]
which is exactly our expanded form.

#### Step 3: Prove the Symmetric Inequality
We need to prove:
\[ a^3 b + b^3 c + c^3 a \geq a^2 b^2 + b^2 c^2 + c^2 a^2 \]
under the given conditions.

This can be proven using the **rearrangement inequality**. The idea is that the sequences \( (a^2, b^2, c^2) \) and \( (a, b, c) \) are similarly ordered, so the product \( a^3 b + b^3 c + c^3 a \) is maximized when the sequences are similarly ordered.

Alternatively, we can use the **Muirhead's inequality**, which states that for symmetric sums, the majorization condition implies the inequality. Here, the sequences \( (3, 1, 0) \) and \( (2, 2, 0) \) are not comparable, but the condition \( a^3 b + b^3 c + c^3 a \geq a^2 b^2 + b^2 c^2 + c^2 a^2 \) can be checked directly.

However, a simpler approach is to use the **Chebyshev sum inequality** or **rearrangement**. The sequences \( (a^2, b^2, c^2) \) and \( (a, b, c) \) are similarly ordered, so by the rearrangement inequality:
\[ a^3 b + b^3 c + c^3 a \geq a^2 b^2 + b^2 c^2 + c^2 a^2 \]

This completes the proof.

### Step 4: Abstract Plan

1. **Expand the Expression**:
   - Expand each term in the original expression to get a sum of monomials.

2. **Symmetrize the Inequality**:
   - Rearrange the expanded form to compare symmetric sums.

3. **Apply Rearrangement Inequality**:
   - Use the fact that the sequences \( (a^2, b^2, c^2) \) and \( (a, b, c) \) are similarly ordered to prove the inequality.

### Lean 4 `have` Statements

```lean4
theorem imo_1983_p6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  have h_main : 0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem imo_1983_p6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
  have h_main : 0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos h₀.1 h₀.2.1, mul_pos h₀.2.1 h₀.2.2, mul_pos h₀.1 h₀.2.2,
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃),
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃), sq_nonneg (a - b - (b - c)),
      sq_nonneg (b - c - (c - a)), sq_nonneg (c - a - (a - b))]
  exact h_main
```