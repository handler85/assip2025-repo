import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, let's carefully restate the problem and the given conditions:

1. We have two natural numbers \( x \) and \( y \) such that \( x + y = 17402 \).
2. \( x \) is divisible by \( 10 \), i.e., \( 10 \mid x \).
3. The quotient when \( x \) is divided by \( 10 \) is \( y \), i.e., \( \frac{x}{10} = y \).

We need to prove that \( x - y = 14238 \).

#### Step 1: Understand the relationship between \( x \) and \( y \)

From condition 3, we have:
\[ x = 10 y \]

This is because \( \frac{x}{10} = y \) is equivalent to \( x = 10 y \) (since \( x \) and \( y \) are natural numbers and \( 10 \neq 0 \)).

#### Step 2: Substitute \( x = 10 y \) into the sum equation

From condition 1, we have:
\[ x + y = 17402 \]

Substitute \( x = 10 y \):
\[ 10 y + y = 17402 \]
\[ 11 y = 17402 \]
\[ y = \frac{17402}{11} \]

But \( 17402 \div 11 = 1582 \), since \( 11 \times 1582 = 11 \times 1500 + 11 \times 82 = 16500 + 902 = 17402 \).

Thus:
\[ y = 1582 \]

#### Step 3: Find \( x \)

From \( x = 10 y \), we have:
\[ x = 10 \times 1582 = 15820 \]

#### Step 4: Verify the solution

Check the sum:
\[ x + y = 15820 + 1582 = 17402 \]
This is correct.

#### Step 5: Compute \( x - y \)

\[ x - y = 15820 - 1582 = 14238 \]

This matches the required result.

### Step-by-Step Abstract Plan

1. **Express \( x \) in terms of \( y \)**:
   - From \( \frac{x}{10} = y \), deduce \( x = 10 y \).

2. **Substitute into the sum equation**:
   - Use \( x + y = 17402 \) to get \( 11 y = 17402 \).

3. **Solve for \( y \)**:
   - \( y = \frac{17402}{11} = 1582 \).

4. **Find \( x \)**:
   - \( x = 10 y = 15820 \).

5. **Compute \( x - y \)**:
   - \( x - y = 15820 - 1582 = 14238 \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem amc12a_2021_p3 (x y : ℕ) (h₀ : x + y = 17402) (h₁ : 10 ∣ x) (h₂ : x / 10 = y) :
    ↑x - ↑y = (14238 : ℤ) := by
  have h_x_div_10 : x = 10 * y := by sorry
  have h_x_val : x = 15820 := by sorry
  have h_y_val : y = 1582 := by sorry
  have h_main : (x : ℤ) - y = 14238 := by sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem amc12a_2021_p3 (x y : ℕ) (h₀ : x + y = 17402) (h₁ : 10 ∣ x) (h₂ : x / 10 = y) :
    ↑x - ↑y = (14238 : ℤ) := by
  have h_x_div_10 : x = 10 * y := by
    have h₃ : x / 10 = y := h₂
    have h₄ : x = 10 * y := by
      have h₅ : x / 10 = y := h₂
      have h₆ : x = 10 * (x / 10) := by
        omega
      rw [h₅] at h₆
      omega
    exact h₄
  
  have h_x_val : x = 15820 := by
    have h₃ : x = 10 * y := h_x_div_10
    have h₄ : x + y = 17402 := h₀
    have h₅ : 10 * y + y = 17402 := by
      omega
    have h₆ : 11 * y = 17402 := by
      omega
    have h₇ : y = 1582 := by
      omega
    have h₈ : x = 10 * y := h_x_div_10
    have h₉ : x = 10 * 1582 := by
      omega
    have h₁₀ : x = 15820 := by
      omega
    exact h₁₀
  
  have h_y_val : y = 1582 := by
    have h₃ : x = 10 * y := h_x_div_10
    have h₄ : x = 15820 := h_x_val
    have h₅ : 10 * y = 15820 := by linarith
    have h₆ : y = 1582 := by
      omega
    exact h₆
  
  have h_main : (x : ℤ) - y = 14238 := by
    norm_num [h_x_val, h_y_val]
    <;>
    (try omega) <;>
    (try ring_nf) <;>
    (try norm_cast) <;>
    (try omega)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
  
  simpa [h_x_val, h_y_val] using h_main
