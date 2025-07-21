import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, we are given:
1. \( b = a^2 \)
2. \( a + b = 1 \)
3. \( d = c^2 \)
4. \( c + d = 1 \)
5. \( a \neq c \)

We need to prove that:
\[ \sqrt{(a - c)^2 + (b - d)^2} = \sqrt{10} \]

#### Step 1: Solve for \( b \) and \( d \) in terms of \( a \) and \( c \)
From the given equations:
1. \( b = a^2 \)
2. \( a + b = 1 \Rightarrow a + a^2 = 1 \Rightarrow a^2 + a - 1 = 0 \)
3. \( d = c^2 \)
4. \( c + d = 1 \Rightarrow c + c^2 = 1 \Rightarrow c^2 + c - 1 = 0 \)

#### Step 2: Solve the quadratic equations for \( a \) and \( c \)
The roots of \( x^2 + x - 1 = 0 \) are:
\[ x = \frac{-1 \pm \sqrt{1 + 4}}{2} = \frac{-1 \pm \sqrt{5}}{2} \]
Thus, the solutions are:
\[ a = \frac{-1 + \sqrt{5}}{2} \quad \text{or} \quad a = \frac{-1 - \sqrt{5}}{2} \]
Similarly, for \( c \):
\[ c = \frac{-1 + \sqrt{5}}{2} \quad \text{or} \quad c = \frac{-1 - \sqrt{5}}{2} \]

#### Step 3: Enumerate all possible cases for \( a \) and \( c \)
Since \( a \neq c \), we can consider the following cases:
1. \( a = \frac{-1 + \sqrt{5}}{2} \) and \( c = \frac{-1 - \sqrt{5}}{2} \)
2. \( a = \frac{-1 - \sqrt{5}}{2} \) and \( c = \frac{-1 + \sqrt{5}}{2} \)

In both cases, we can compute \( b - d \):
\[ b - d = a^2 - c^2 = (a - c)(a + c) \]

Similarly, \( a - c \) is the same in both cases:
\[ a - c = \frac{-1 + \sqrt{5}}{2} - \frac{-1 - \sqrt{5}}{2} = \frac{-1 + \sqrt{5} + 1 + \sqrt{5}}{2} = \frac{2\sqrt{5}}{2} = \sqrt{5} \]

Thus, in both cases:
\[ (a - c)^2 = (\sqrt{5})^2 = 5 \]

Now, compute \( b - d \):
\[ b - d = a^2 - c^2 = (a - c)(a + c) \]

In the first case:
\[ a + c = \frac{-1 + \sqrt{5}}{2} + \frac{-1 - \sqrt{5}}{2} = \frac{-1 + \sqrt{5} - 1 - \sqrt{5}}{2} = \frac{-2}{2} = -1 \]
Thus:
\[ b - d = (a - c)(a + c) = \sqrt{5} \cdot (-1) = -\sqrt{5} \]
\[ (b - d)^2 = (-\sqrt{5})^2 = 5 \]

In the second case:
\[ a + c = \frac{-1 - \sqrt{5}}{2} + \frac{-1 + \sqrt{5}}{2} = \frac{-1 - \sqrt{5} - 1 + \sqrt{5}}{2} = \frac{-2}{2} = -1 \]
Thus:
\[ b - d = (a - c)(a + c) = \sqrt{5} \cdot (-1) = -\sqrt{5} \]
\[ (b - d)^2 = (-\sqrt{5})^2 = 5 \]

In both cases:
\[ (a - c)^2 + (b - d)^2 = 5 + 5 = 10 \]
Thus:
\[ \sqrt{(a - c)^2 + (b - d)^2} = \sqrt{10} \]

### Step 4: Abstract Plan

1. **Solve for \( a \) and \( c \)**:
   - Use the quadratic equations derived from the given conditions to find all possible real values of \( a \) and \( c \).

2. **Enumerate Cases**:
   - Since \( a \neq c \), consider all possible pairs of distinct real roots for \( a \) and \( c \).

3. **Compute Differences**:
   - For each case, compute \( a - c \) and \( b - d \).

4. **Calculate Sum of Squares**:
   - For each case, compute \( (a - c)^2 + (b - d)^2 \).

5. **Verify Result**:
   - Confirm that the sum of squares is always 10, and thus the square root is \( \sqrt{10} \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_487
  (a b c d : ℝ)
  (h₀ : b = a^2)
  (h₁ : a + b = 1)
  (h₂ : d = c^2)
  (h₃ : c + d = 1)
  (h₄ : a ≠ c) :
  Real.sqrt ((a - c)^2 + (b - d)^2)= Real.sqrt 10 := by
  have h₅ : a = (-1 + Real.sqrt 5) / 2 ∨ a = (-1 - Real.sqrt 5) / 2 := by sorry
  have h₆ : c = (-1 + Real.sqrt 5) / 2 ∨ c = (-1 - Real.sqrt 5) / 2 := by sorry
  have h₇ : (a - c)^2 + (b - d)^2 = 10 := by sorry
  have h₈ : Real.sqrt ((a - c)^2 + (b - d)^2) = Real.sqrt 10 := by sorry
  exact h₈
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_487
  (a b c d : ℝ)
  (h₀ : b = a^2)
  (h₁ : a + b = 1)
  (h₂ : d = c^2)
  (h₃ : c + d = 1)
  (h₄ : a ≠ c) :
  Real.sqrt ((a - c)^2 + (b - d)^2)= Real.sqrt 10 := by
  have h₅ : a = (-1 + Real.sqrt 5) / 2 ∨ a = (-1 - Real.sqrt 5) / 2 := by
    have h₅₁ : a = (-1 + Real.sqrt 5) / 2 ∨ a = (-1 - Real.sqrt 5) / 2 := by
      apply or_iff_not_imp_left.mpr
      intro h₅₂
      apply mul_left_cancel₀ (sub_ne_zero.mpr h₅₂)
      nlinarith [Real.sq_sqrt (show 0 ≤ 5 by norm_num), Real.sqrt_nonneg 5, sq_nonneg (a + 1)]
    exact h₅₁
  
  have h₆ : c = (-1 + Real.sqrt 5) / 2 ∨ c = (-1 - Real.sqrt 5) / 2 := by
    have h₆₁ : c = (-1 + Real.sqrt 5) / 2 ∨ c = (-1 - Real.sqrt 5) / 2 := by
      apply or_iff_not_imp_left.mpr
      intro h₆₂
      apply mul_left_cancel₀ (sub_ne_zero.mpr h₆₂)
      nlinarith [Real.sq_sqrt (show 0 ≤ 5 by norm_num), Real.sqrt_nonneg 5, sq_nonneg (c + 1)]
    exact h₆₁
  
  have h₇ : (a - c)^2 + (b - d)^2 = 10 := by
    rcases h₅ with (rfl | rfl) <;> rcases h₆ with (rfl | rfl) <;>
    simp_all [h₀, h₂, sub_eq_add_neg, add_assoc]
    <;> ring_nf at * <;> norm_num at * <;>
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    <;> linarith
  
  have h₈ : Real.sqrt ((a - c)^2 + (b - d)^2) = Real.sqrt 10 := by
    rw [h₇]
    <;>
    norm_num
    <;>
    apply Real.sqrt_inj
    <;>
    norm_num
    <;>
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  
  rw [h₈]
  <;>
  norm_num
  <;>
  apply Real.sqrt_inj
  <;>
  norm_num
  <;>
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
```