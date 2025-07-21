import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We are given two real numbers \( x \) and \( y \):
1. Their arithmetic mean is \( 7 \), i.e., \( \frac{x + y}{2} = 7 \).
2. Their geometric mean is \( \sqrt{19} \), i.e., \( \sqrt{xy} = \sqrt{19} \).

We need to find \( x^2 + y^2 \).

**Key Observations:**
1. From the arithmetic mean, we can directly express \( x + y \):
   \[ x + y = 14. \]
2. The geometric mean is \( \sqrt{xy} = \sqrt{19} \), so:
   \[ xy = 19. \]
3. We can find \( x^2 + y^2 \) using the identity:
   \[ x^2 + y^2 = (x + y)^2 - 2xy. \]

**Proof:**
1. From \( \frac{x + y}{2} = 7 \), we multiply both sides by \( 2 \) to get:
   \[ x + y = 14. \]
2. From \( \sqrt{xy} = \sqrt{19} \), we square both sides to get:
   \[ xy = 19. \]
3. Now, we compute \( x^2 + y^2 \):
   \[ x^2 + y^2 = (x + y)^2 - 2xy = 14^2 - 2 \cdot 19 = 196 - 38 = 158. \]

This completes the proof.

### Step 1: Abstract Plan

1. **Find \( x + y \)**:
   - Multiply the given arithmetic mean by \( 2 \).
   - \( x + y = 14 \).

2. **Find \( xy \)**:
   - Square the given geometric mean.
   - \( xy = 19 \).

3. **Find \( x^2 + y^2 \)**:
   - Use the identity \( x^2 + y^2 = (x + y)^2 - 2xy \).
   - Substitute the known values to get \( x^2 + y^2 = 158 \).

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_algebra_332
  (x y : ℝ)
  (h₀ : (x + y) / 2 = 7)
  (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
  x^2 + y^2 = 158 := by
  have h₂ : x + y = 14 := by sorry
  have h₃ : x * y = 19 := by sorry
  have h₄ : x^2 + y^2 = 158 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_332
  (x y : ℝ)
  (h₀ : (x + y) / 2 = 7)
  (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
  x^2 + y^2 = 158 := by
  have h₂ : x + y = 14 := by
    have h₂₁ : (x + y) / 2 = 7 := h₀
    have h₂₂ : x + y = 14 := by linarith
    exact h₂₂
  
  have h₃ : x * y = 19 := by
    have h₃₁ : Real.sqrt (x * y) = Real.sqrt 19 := h₁
    have h₃₂ : x * y = 19 := by
      have h₃₃ : Real.sqrt (x * y) = Real.sqrt 19 := h₁
      have h₃₄ : Real.sqrt (x * y) ^ 2 = (Real.sqrt 19) ^ 2 := by rw [h₃₃]
      have h₃₅ : x * y ≥ 0 := by
        by_contra h
        have h₃₆ : x * y < 0 := by linarith
        have h₃₇ : Real.sqrt (x * y) = 0 := by
          apply Real.sqrt_eq_zero_of_nonpos
          nlinarith
        rw [h₃₇] at h₃₃
        have h₃₈ : Real.sqrt 19 > 0 := Real.sqrt_pos.mpr (by norm_num)
        nlinarith [Real.sq_sqrt (show 0 ≤ 19 by norm_num)]
      have h₃₉ : Real.sqrt 19 ≥ 0 := Real.sqrt_nonneg 19
      have h₄₀ : Real.sqrt (x * y) ^ 2 = x * y := by
        rw [Real.sq_sqrt] <;> nlinarith
      have h₄₁ : (Real.sqrt 19) ^ 2 = 19 := by
        rw [Real.sq_sqrt] <;> norm_num
      nlinarith
    exact h₃₂
  
  have h₄ : x^2 + y^2 = 158 := by
    have h₅ : x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by
      ring
    rw [h₅]
    rw [h₂]
    rw [h₃]
    <;> norm_num
    <;> linarith
  
  exact h₄
```