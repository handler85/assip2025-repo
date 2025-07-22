import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, let's understand the problem:
We need to find the minimum value of the quadratic expression \( x^2 - 14x + 3 \). 

To find the minimum of a quadratic function \( ax^2 + bx + c \), we can complete the square or use the vertex formula. Here, the vertex is at \( x = -\frac{b}{2a} \).

For the given quadratic \( x^2 - 14x + 3 \), the coefficient of \( x^2 \) is 1, and the coefficient of \( x \) is -14. Thus, the vertex is at:
\[ x = -\frac{-14}{2 \cdot 1} = \frac{14}{2} = 7. \]

This means that the minimum value of the quadratic is achieved when \( x = 7 \). 

To prove that the minimum value is \( 7^2 - 14 \cdot 7 + 3 \), we can complete the square for the quadratic expression:
\[ x^2 - 14x + 3 = (x^2 - 14x + 49) - 49 + 3 = (x - 7)^2 - 46. \]

Thus, the minimum value is \(-46\), achieved when \( x = 7 \). 

But wait, the problem statement says that the minimum value is \( 7^2 - 14 \cdot 7 + 3 \), which is \(-46\) (since \( 7^2 - 14 \cdot 7 + 3 = 49 - 98 + 3 = -46 \)). 

This is correct because the minimum value of the quadratic is \(-46\), and the expression \( 7^2 - 14 \cdot 7 + 3 \) is exactly \(-46\). 

Therefore, the inequality \( x^2 - 14x + 3 \geq 7^2 - 14 \cdot 7 + 3 \) is equivalent to \( x^2 - 14x + 3 \geq -46 \), which is always true because \( x^2 - 14x + 3 \geq -46 \) is equivalent to \( x^2 - 14x + 49 \geq 0 \), i.e., \( (x - 7)^2 \geq 0 \), which is always true. 

But wait, the original inequality is \( x^2 - 14x + 3 \geq 7^2 - 14 \cdot 7 + 3 \), and \( 7^2 - 14 \cdot 7 + 3 = 49 - 98 + 3 = -46 \). So the inequality is \( x^2 - 14x + 3 \geq -46 \). 

But \( x^2 - 14x + 3 \geq -46 \) is equivalent to \( x^2 - 14x + 49 \geq 0 \), i.e., \( (x - 7)^2 \geq 0 \), which is always true. 

Thus, the original inequality is always true, and the minimum value is achieved when \( x = 7 \). 

### Step 1: Abstract Plan

1. **Understand the Problem**: We need to find the minimum value of the quadratic expression \( x^2 - 14x + 3 \).

2. **Find the Vertex**: The vertex of the quadratic \( ax^2 + bx + c \) is at \( x = -\frac{b}{2a} \). Here, \( a = 1 \), \( b = -14 \), so the vertex is at \( x = 7 \).

3. **Evaluate the Expression at the Vertex**: Substitute \( x = 7 \) into the expression to find the minimum value:
   \[ 7^2 - 14 \cdot 7 + 3 = 49 - 98 + 3 = -46. \]

4. **Prove the Inequality**: The inequality \( x^2 - 14x + 3 \geq -46 \) is equivalent to \( x^2 - 14x + 49 \geq 0 \), i.e., \( (x - 7)^2 \geq 0 \), which is always true.

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h_main : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
  have h_main : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
    have h₁ : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by
      nlinarith [sq_nonneg (x - 7), sq_nonneg (x + 7), sq_nonneg (x - 1), sq_nonneg (x + 1),
        sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x - 3), sq_nonneg (x + 3),
        sq_nonneg (x - 4), sq_nonneg (x + 4), sq_nonneg (x - 5), sq_nonneg (x + 5),
        sq_nonneg (x - 6), sq_nonneg (x + 6), sq_nonneg (x - 8), sq_nonneg (x + 8),
        sq_nonneg (x - 9), sq_nonneg (x + 9), sq_nonneg (x - 10), sq_nonneg (x + 10)]
    exact h₁
  exact h_main
