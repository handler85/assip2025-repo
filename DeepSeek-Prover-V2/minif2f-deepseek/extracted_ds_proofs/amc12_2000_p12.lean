import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/-
### Detailed Proof and Analysis

First, we need to find the maximum value of the expression \( E = a \cdot m \cdot c + a \cdot m + m \cdot c + a \cdot c \) under the constraint \( a + m + c = 12 \) where \( a, m, c \) are non-negative integers.

#### Step 1: Understand the Constraint
The sum \( a + m + c = 12 \) is fixed, and we are to maximize \( E \). The expression \( E \) is symmetric in \( a, m, c \), so we can assume without loss of generality that \( a \leq m \leq c \). However, we will not strictly need this assumption for the proof.

#### Step 2: Enumerate Possible Cases
Since \( a, m, c \) are non-negative integers summing to 12, we can enumerate all possible triples \((a, m, c)\) and compute \( E \) for each. However, this is tedious, so we can instead use symmetry and logic to narrow down the possibilities.

#### Step 3: Use Symmetry and Logic
Notice that the expression \( E \) is symmetric in \( a, m, c \), so the maximum will occur when two of the variables are as large as possible and the third is as small as possible (given the sum constraint).

Let's consider the case where two variables are equal and the third is different. Suppose \( a = m \). Then \( 2a + c = 12 \), so \( c = 12 - 2a \). The expression becomes:
\[ E = a^2 \cdot c + a^2 + a \cdot c + a \cdot c = a^2 c + a^2 + 2a c \]
Substitute \( c = 12 - 2a \):
\[ E = a^2 (12 - 2a) + a^2 + 2a (12 - 2a) \]
\[ = 12a^2 - 2a^3 + a^2 + 24a - 4a^2 \]
\[ = -2a^3 + 9a^2 + 24a \]
To find the maximum of \( E \), we can take the derivative with respect to \( a \):
\[ \frac{dE}{da} = -6a^2 + 18a + 24 \]
Set the derivative to zero:
\[ -6a^2 + 18a + 24 = 0 \]
\[ 6a^2 - 18a - 24 = 0 \]
\[ a^2 - 3a - 4 = 0 \]
Solutions:
\[ a = \frac{3 \pm \sqrt{9 + 16}}{2} = \frac{3 \pm 5}{2} \]
Thus, \( a = 4 \) or \( a = -1 \). Since \( a \geq 0 \), \( a = 4 \).

Now, \( c = 12 - 2a = 12 - 8 = 4 \). So, \( a = m = c = 4 \).

But wait, this gives \( E = -2 \cdot 64 + 9 \cdot 16 + 24 \cdot 4 = -128 + 144 + 96 = 112 \).

This is the maximum value.

#### Step 4: Verify Other Cases
To ensure that this is indeed the maximum, we can check other cases where two variables are not equal. For example, if \( a = 5 \), then \( m + c = 7 \). The maximum \( E \) in this case is less than 112.

Alternatively, we can use the fact that the expression \( E \) is symmetric and convex in the variables, so the maximum occurs at the boundary or at critical points.

#### Step 5: Conclusion
The maximum value of \( E \) is \( 112 \), achieved when \( a = m = c = 4 \).

### Step-by-Step Abstract Plan

1. **Understand the Constraint**: We have \( a + m + c = 12 \) with \( a, m, c \geq 0 \).

2. **Symmetry Consideration**: The expression \( E = a \cdot m \cdot c + a \cdot m + m \cdot c + a \cdot c \) is symmetric in \( a, m, c \). The maximum is likely achieved when \( a = m = c \).

3. **Assume \( a = m = c \)**: Then \( 3a = 12 \), so \( a = 4 \). Compute \( E = 4 \cdot 4 \cdot 4 + 4 \cdot 4 + 4 \cdot 4 + 4 \cdot 4 = 64 + 16 + 16 + 16 = 112 \).

4. **Verify Other Cases**: Check cases where two variables are not equal to ensure \( E \leq 112 \). For example, \( a = 5, m = 2, c = 5 \) gives \( E = 5 \cdot 2 \cdot 5 + 5 \cdot 2 + 2 \cdot 5 + 5 \cdot 5 = 50 + 10 + 10 + 25 = 95 \leq 112 \).

5. **Conclusion**: The maximum value of \( E \) is \( 112 \), achieved when \( a = m = c = 4 \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem amc12_2000_p12 (a m c : ℕ) (h₀ : a + m + c = 12) :
    a * m * c + a * m + m * c + a * c ≤ 112 := by
  have h_main : a * m * c + a * m + m * c + a * c ≤ 112 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem amc12_2000_p12 (a m c : ℕ) (h₀ : a + m + c = 12) :
    a * m * c + a * m + m * c + a * c ≤ 112 := by
  have h_main : a * m * c + a * m + m * c + a * c ≤ 112 := by
    have h₁ : a ≤ 12 := by omega
    have h₂ : m ≤ 12 := by omega
    have h₃ : c ≤ 12 := by omega
    interval_cases a <;> interval_cases m <;> interval_cases c <;> norm_num <;>
      (try omega) <;> (try nlinarith) <;> (try ring_nf at * <;> omega)
  exact h_main
