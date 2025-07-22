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

#### Step 1: Solve for \( b \) in terms of \( a \)
From \( a + b = 1 \), we get \( b = 1 - a \). But we also have \( b = a^2 \), so:
\[ a^2 = 1 - a \]
\[ a^2 + a - 1 = 0 \]

The roots of this quadratic equation are:
\[ a = \frac{-1 \pm \sqrt{1 + 4}}{2} = \frac{-1 \pm \sqrt{5}}{2} \]

Thus, \( a \) is either \( \frac{-1 + \sqrt{5}}{2} \) or \( \frac{-1 - \sqrt{5}}{2} \).

#### Step 2: Solve for \( d \) in terms of \( c \)
From \( c + d = 1 \), we get \( d = 1 - c \). But we also have \( d = c^2 \), so:
\[ c^2 = 1 - c \]
\[ c^2 + c - 1 = 0 \]

The roots of this quadratic equation are:
\[ c = \frac{-1 \pm \sqrt{1 + 4}}{2} = \frac{-1 \pm \sqrt{5}}{2} \]

Thus, \( c \) is either \( \frac{-1 + \sqrt{5}}{2} \) or \( \frac{-1 - \sqrt{5}}{2} \).

#### Step 3: Find the possible values of \( a \) and \( c \)
From the above, \( a \) and \( c \) are roots of the same quadratic equation. The roots are:
\[ a = \frac{-1 + \sqrt{5}}{2}, \quad a = \frac{-1 - \sqrt{5}}{2} \]
\[ c = \frac{-1 + \sqrt{5}}{2}, \quad c = \frac{-1 - \sqrt{5}}{2} \]

But \( a \neq c \), so we must have:
1. \( a = \frac{-1 + \sqrt{5}}{2} \) and \( c = \frac{-1 - \sqrt{5}}{2} \), or
2. \( a = \frac{-1 - \sqrt{5}}{2} \) and \( c = \frac{-1 + \sqrt{5}}{2} \).

But in both cases, \( a - c = \sqrt{5} \) or \( a - c = -\sqrt{5} \), and \( b - d = (1 - a) - (1 - c) = c - a = -(a - c) \). Thus:
\[ (a - c)^2 + (b - d)^2 = (a - c)^2 + (c - a)^2 = 2(a - c)^2 \]
But \( a - c = \sqrt{5} \) or \( a - c = -\sqrt{5} \), so:
\[ 2(a - c)^2 = 2 \cdot 5 = 10 \]
Thus:
\[ \sqrt{(a - c)^2 + (b - d)^2} = \sqrt{10} \]

### Step 4: Abstract Plan

1. **Find \( a \) and \( c \)**:
   - Solve \( a^2 + a - 1 = 0 \) to get \( a = \frac{-1 \pm \sqrt{5}}{2} \).
   - Similarly, solve \( c^2 + c - 1 = 0 \) to get \( c = \frac{-1 \pm \sqrt{5}}{2} \).

2. **Case Analysis**:
   - Since \( a \neq c \), we have two cases:
     - \( a = \frac{-1 + \sqrt{5}}{2} \) and \( c = \frac{-1 - \sqrt{5}}{2} \), or
     - \( a = \frac{-1 - \sqrt{5}}{2} \) and \( c = \frac{-1 + \sqrt{5}}{2} \).

3. **Compute Differences**:
   - In both cases, \( a - c = \sqrt{5} \) or \( a - c = -\sqrt{5} \).
   - Compute \( b - d = c - a = -(a - c) \).

4. **Final Calculation**:
   - \( (a - c)^2 + (b - d)^2 = (a - c)^2 + (c - a)^2 = 2(a - c)^2 \).
   - Substitute \( a - c = \sqrt{5} \) to get \( 2 \cdot 5 = 10 \).
   - Thus, \( \sqrt{(a - c)^2 + (b - d)^2} = \sqrt{10} \).

### Lean 4 Proof Sketch with `have`

```lean4
theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have h₅ : a = (-1 + Real.sqrt 5) / 2 ∨ a = (-1 - Real.sqrt 5) / 2 := by sorry
  have h₆ : c = (-1 + Real.sqrt 5) / 2 ∨ c = (-1 - Real.sqrt 5) / 2 := by sorry
  have h₇ : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by sorry
  have h₈ : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by sorry
  exact h₈
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
  have h₅ : a = (-1 + Real.sqrt 5) / 2 ∨ a = (-1 - Real.sqrt 5) / 2 := by
    have h₅₁ : a ^ 2 + a - 1 = 0 := by
      nlinarith
    have h₅₂ : a = (-1 + Real.sqrt 5) / 2 ∨ a = (-1 - Real.sqrt 5) / 2 := by
      apply or_iff_not_imp_left.mpr
      intro h₅₃
      apply mul_left_cancel₀ (sub_ne_zero.mpr h₅₃)
      nlinarith [Real.sq_sqrt (show 0 ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    exact h₅₂
  
  have h₆ : c = (-1 + Real.sqrt 5) / 2 ∨ c = (-1 - Real.sqrt 5) / 2 := by
    have h₆₁ : c ^ 2 + c - 1 = 0 := by
      nlinarith
    have h₆₂ : c = (-1 + Real.sqrt 5) / 2 ∨ c = (-1 - Real.sqrt 5) / 2 := by
      apply or_iff_not_imp_left.mpr
      intro h₆₃
      apply mul_left_cancel₀ (sub_ne_zero.mpr h₆₃)
      nlinarith [Real.sq_sqrt (show 0 ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    exact h₆₂
  
  have h₇ : (a - c) ^ 2 + (b - d) ^ 2 = 10 := by
    rcases h₅ with (rfl | rfl) <;> rcases h₆ with (rfl | rfl) <;>
    simp_all [h₀, h₂, sq, mul_add, mul_comm, mul_left_comm, mul_assoc]
    <;> ring_nf at * <;> norm_num at * <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  
  have h₈ : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by
    rw [h₇]
    <;>
    norm_num
    <;>
    linarith
  
  exact h₈
```