import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, let's carefully restate the problem and the given conditions:

We have three distinct digits \( A, B, C \) (i.e., \( A, B, C \in \{1, 2, \dots, 9\} \)) such that:
1. \( A + B = C \),
2. \( 10A + A - B = 2C \),
3. \( C \cdot B = 10A + A + A \).

We need to prove that \( A + B + C = 8 \).

#### Step 1: Simplify the second equation
The second equation is \( 10A + A - B = 2C \), which simplifies to \( 11A - B = 2C \).

#### Step 2: Use the first equation \( A + B = C \)
From \( A + B = C \), we can substitute \( C = A + B \) into the simplified second equation:
\[ 11A - B = 2(A + B) \]
\[ 11A - B = 2A + 2B \]
\[ 11A - 2A = 2B + B \]
\[ 9A = 3B \]
\[ 3A = B \]

#### Step 3: Find \( C \) in terms of \( A \)
From \( B = 3A \), substitute into \( A + B = C \):
\[ A + 3A = C \]
\[ 4A = C \]

#### Step 4: Check the third equation
The third equation is \( C \cdot B = 10A + A + A \). Substitute \( C = 4A \) and \( B = 3A \):
\[ (4A)(3A) = 10A + A + A \]
\[ 12A^2 = 12A \]
\[ 12A^2 - 12A = 0 \]
\[ 12A(A - 1) = 0 \]

Since \( A \) is a digit from 1 to 9, \( A \neq 0 \), and \( A \neq 1 \) is possible. But we must ensure that \( A \neq 1 \) is valid. 

If \( A = 1 \), then:
- \( B = 3 \cdot 1 = 3 \),
- \( C = 4 \cdot 1 = 4 \).

Check the original conditions:
1. \( A + B = 1 + 3 = 4 = C \),
2. \( 10A + A - B = 10 + 1 - 3 = 8 = 2 \cdot 4 = 2C \),
3. \( C \cdot B = 4 \cdot 3 = 12 = 10A + A + A = 10 + 1 + 1 = 12 \).

This is valid. 

But wait, we assumed \( A \neq 1 \). But in the case \( A = 1 \), the third equation is satisfied, and all other conditions are satisfied. 

But is \( A = 1 \) the only solution? 

From \( 12A(A - 1) = 0 \), we have \( A = 0 \) or \( A = 1 \). 

But \( A \) is a digit from 1 to 9, so \( A \neq 0 \). 

Thus, \( A = 1 \) is the only solution. 

But we must check if \( A = 1 \) is valid. 

It is, as shown above. 

Therefore, the only solution is \( A = 1 \), \( B = 3 \), \( C = 4 \), and \( A + B + C = 1 + 3 + 4 = 8 \).

#### Step 5: Verification
We can verify that all conditions are satisfied for \( A = 1 \), \( B = 3 \), \( C = 4 \):
1. \( A + B = 1 + 3 = 4 = C \),
2. \( 10A + A - B = 10 + 1 - 3 = 8 = 2 \cdot 4 = 2C \),
3. \( C \cdot B = 4 \cdot 3 = 12 = 10A + A + A = 10 + 1 + 1 = 12 \).

All conditions are satisfied, and the sum is \( 8 \).

### Step 6: Abstract Plan

1. **Simplify the second equation**:
   - Start with \( 10A + A - B = 2C \).
   - Simplify to \( 11A - B = 2C \).

2. **Substitute \( C = A + B \) from the first equation**:
   - Replace \( C \) in the simplified second equation to get \( 11A - B = 2(A + B) \).
   - Simplify to \( 9A = 3B \), or \( 3A = B \).

3. **Find \( C \) in terms of \( A \)**:
   - From \( B = 3A \), substitute into \( C = A + B \) to get \( C = 4A \).

4. **Check the third equation**:
   - Substitute \( B = 3A \) and \( C = 4A \) into \( C \cdot B = 10A + A + A \).
   - Simplify to \( 12A^2 = 12A \).
   - Since \( A \neq 0 \), divide by \( A \) to get \( 12A = 12 \), or \( A = 1 \).

5. **Find \( B \) and \( C \)**:
   - With \( A = 1 \), \( B = 3A = 3 \), and \( C = 4A = 4 \).

6. **Verify the sum**:
   - \( A + B + C = 1 + 3 + 4 = 8 \).

### Lean 4 Proof Sketch with `have`

```lean4
theorem mathd_numbertheory_430 (a b c : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 1 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : a + b = c)
    (h₇ : 10 * a + a - b = 2 * c) (h₈ : c * b = 10 * a + a + a) : a + b + c = 8 := by
  have h_a : a = 1 := by sorry
  have h_b : b = 3 := by sorry
  have h_c : c = 4 := by sorry
  have h_sum : a + b + c = 8 := by sorry
  exact h_sum
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_numbertheory_430 (a b c : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 1 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : a + b = c)
    (h₇ : 10 * a + a - b = 2 * c) (h₈ : c * b = 10 * a + a + a) : a + b + c = 8 := by
  have h_a : a = 1 := by
    have h₉ := h₈
    have h₁₀ : a ≤ 9 := by linarith
    have h₁₁ : b ≤ 9 := by linarith
    have h₁₂ : c ≤ 9 := by linarith
    interval_cases a <;> interval_cases b <;> omega
  
  have h_b : b = 3 := by
    have h₉ := h₈
    have h₁₀ : a ≤ 9 := by linarith
    have h₁₁ : b ≤ 9 := by linarith
    have h₁₂ : c ≤ 9 := by linarith
    subst_vars
    interval_cases b <;> omega
  
  have h_c : c = 4 := by
    have h₉ := h₆
    have h₁₀ := h₇
    have h₁₁ := h₈
    subst_vars
    <;> omega
  
  have h_sum : a + b + c = 8 := by
    subst_vars
    <;> norm_num
    <;> linarith
  
  exact h_sum
