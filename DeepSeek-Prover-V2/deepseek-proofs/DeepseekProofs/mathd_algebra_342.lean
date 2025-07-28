import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, recall the problem:
- The sum of the first 5 terms of an arithmetic series is 70.
- The sum of the first 10 terms of the same arithmetic series is 210.
- We need to find the first term `a` of the series and show that it is `42/5`.

#### Step 1: Understand the Sum of an Arithmetic Series
The sum of the first `n` terms of an arithmetic series with first term `a` and common difference `d` is given by:
\[ S_n = \frac{n}{2} (2a + (n - 1)d) \]

#### Step 2: Apply the Given Conditions
1. For `n = 5` and `S_5 = 70`:
   \[ 70 = \frac{5}{2} (2a + 4d) \]
   Simplify:
   \[ 70 = \frac{5}{2} (2a + 4d) \]
   Multiply both sides by `2/5`:
   \[ 28 = 2a + 4d \]
   Divide by `2`:
   \[ 14 = a + 2d \quad \text{(Equation 1)} \]

2. For `n = 10` and `S_{10} = 210`:
   \[ 210 = \frac{10}{2} (2a + 9d) \]
   Simplify:
   \[ 210 = 5 (2a + 9d) \]
   Divide by `5`:
   \[ 42 = 2a + 9d \quad \text{(Equation 2)} \]

#### Step 3: Solve the System of Equations
We have:
1. \( a + 2d = 14 \) (Equation 1)
2. \( 2a + 9d = 42 \) (Equation 2)

From Equation 1:
\[ a = 14 - 2d \]

Substitute into Equation 2:
\[ 2(14 - 2d) + 9d = 42 \]
\[ 28 - 4d + 9d = 42 \]
\[ 28 + 5d = 42 \]
\[ 5d = 14 \]
\[ d = \frac{14}{5} \]

Now, find `a`:
\[ a = 14 - 2d = 14 - 2 \cdot \frac{14}{5} = 14 - \frac{28}{5} = \frac{70}{5} - \frac{28}{5} = \frac{42}{5} \]

Thus, the first term is `a = 42/5`.

### Step 4: Abstract Plan

1. **Understand the Sum Formula**:
   - The sum of the first `n` terms of an arithmetic series is `S_n = n/2 * (2a + (n - 1)d)`.

2. **Set Up Equations**:
   - For `n = 5` and `S_5 = 70`, derive `a + 2d = 14`.
   - For `n = 10` and `S_{10} = 210`, derive `2a + 9d = 42`.

3. **Solve the System**:
   - Express `a` in terms of `d` from the first equation.
   - Substitute into the second equation to find `d = 14/5`.
   - Back-substitute to find `a = 42/5`.

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_342 (a d : ℝ) (h₀ : (∑ k in Finset.range 5, (a + k * d)) = 70)
    (h₁ : (∑ k in Finset.range 10, (a + k * d)) = 210) : a = 42 / 5 := by
  have h₂ : a + 2 * d = 14 := by sorry
  have h₃ : 2 * a + 9 * d = 42 := by sorry
  have h₄ : d = 14 / 5 := by sorry
  have h₅ : a = 42 / 5 := by sorry
  exact h₅
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_342 (a d : ℝ) (h₀ : (∑ k in Finset.range 5, (a + k * d)) = 70)
    (h₁ : (∑ k in Finset.range 10, (a + k * d)) = 210) : a = 42 / 5 := by
  have h₂ : a + 2 * d = 14 := by
    have h₂₀ : (∑ k in Finset.range 5, (a + k * d)) = 70 := h₀
    simp [Finset.sum_range_succ, Finset.sum_range_zero] at h₂₀
    ring_nf at h₂₀ ⊢
    nlinarith
  
  have h₃ : 2 * a + 9 * d = 42 := by
    have h₃₀ : (∑ k in Finset.range 10, (a + k * d)) = 210 := h₁
    simp [Finset.sum_range_succ, Finset.sum_range_zero] at h₃₀
    ring_nf at h₃₀ h₂ ⊢
    nlinarith
  
  have h₄ : d = 14 / 5 := by
    have h₄₁ : d = 14 / 5 := by
      -- Solve the system of linear equations to find d
      linarith
    exact h₄₁
  
  have h₅ : a = 42 / 5 := by
    have h₅₁ : a = 42 / 5 := by
      -- Substitute d = 14 / 5 into the equation a + 2 * d = 14 to find a
      linarith
    exact h₅₁
  
  linarith
