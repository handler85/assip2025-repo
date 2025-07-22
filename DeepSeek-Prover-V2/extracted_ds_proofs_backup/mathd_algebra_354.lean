import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We are given an arithmetic sequence with the first term `a` and common difference `d`. The 7th term is `30`, and the 11th term is `60`. We need to find the 21st term, which is `a + 20 * d`, and show that it equals `135`.

**Given Equations:**
1. `a + 6 * d = 30` (7th term)
2. `a + 10 * d = 60` (11th term)

**Goal:**
Prove that `a + 20 * d = 135`.

**Approach:**
1. Subtract the first equation from the second to eliminate `a` and find `d`.
2. Substitute the value of `d` back into one of the original equations to find `a`.
3. Use the values of `a` and `d` to find `a + 20 * d`.

**Detailed Steps:**

1. Subtract the first equation from the second:
   \[
   (a + 10d) - (a + 6d) = 60 - 30
   \]
   Simplifying:
   \[
   a + 10d - a - 6d = 30 \\
   4d = 30 \\
   d = \frac{30}{4} = \frac{15}{2}
   \]

2. Substitute `d = 15/2` back into the first equation to find `a`:
   \[
   a + 6 \cdot \frac{15}{2} = 30 \\
   a + \frac{90}{2} = 30 \\
   a + 45 = 30 \\
   a = 30 - 45 = -15
   \]

3. Calculate `a + 20 * d`:
   \[
   a + 20 \cdot d = -15 + 20 \cdot \frac{15}{2} = -15 + 150 = 135
   \]

**Conclusion:**
The 21st term of the sequence is `135`.

### Step-by-Step Abstract Plan

1. **Find the common difference `d`:**
   - Subtract the first equation from the second to eliminate `a`.
   - Simplify to find `d = 15/2`.

2. **Find the first term `a`:**
   - Substitute `d = 15/2` back into the first equation.
   - Simplify to find `a = -15`.

3. **Find the 21st term `a + 20 * d`:**
   - Substitute `a = -15` and `d = 15/2` into the expression.
   - Simplify to get the final result `135`.

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  have h_d : d = 15 / 2 := by sorry
  have h_a : a = -15 := by sorry
  have h_main : a + 20 * d = 135 := by sorry
  exact h_main
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  have h_d : d = 15 / 2 := by
    have h₂ : a + 6 * d = 30 := h₀
    have h₃ : a + 10 * d = 60 := h₁
    -- Subtract the first equation from the second to eliminate a
    have h₄ : (a + 10 * d) - (a + 6 * d) = 60 - 30 := by linarith
    -- Simplify the equation to find d
    have h₅ : 4 * d = 30 := by linarith
    have h₆ : d = 15 / 2 := by linarith
    exact h₆
  
  have h_a : a = -15 := by
    have h₂ : a + 6 * d = 30 := h₀
    have h₃ : d = 15 / 2 := h_d
    -- Substitute d = 15 / 2 into the equation a + 6 * d = 30
    rw [h₃] at h₂
    -- Simplify the equation to solve for a
    ring_nf at h₂ ⊢
    linarith
  
  have h_main : a + 20 * d = 135 := by
    rw [h_a, h_d]
    <;> norm_num
    <;> linarith
  
  exact h_main
```