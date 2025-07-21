import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, let's carefully restate the problem and the given conditions:

1. We have a point `(x, y)` in the plane with both coordinates negative (`x < 0` and `y < 0`).
2. The distance of `(x, y)` from the `x`-axis is `6` units. This means `|y| = 6`, which is given as `h₁`. Since `y < 0`, we have `y = -6`.
3. The distance of `(x, y)` from the point `(8, 3)` is `15` units. This means `√((x - 8)² + (y - 3)²) = 15`, which is given as `h₂`.
4. The distance of `(x, y)` from the origin is `√(x² + y²)`, and this is equal to `√n`, where `n` is a non-negative real number (`n : NNReal`). This is given as `h₃`.
5. We need to prove that `n = 52`.

#### Step 1: Find `y`
From `h₁` and `y < 0`, we have `y = -6`.

#### Step 2: Find `x`
Substitute `y = -6` into `h₂`:
`√((x - 8)² + (-6 - 3)²) = 15` → `√((x - 8)² + (-9)²) = 15` → `√((x - 8)² + 81) = 15`.

Square both sides:
`(x - 8)² + 81 = 225` → `(x - 8)² = 144` → `x - 8 = ±12`.

Thus:
1. `x - 8 = 12` → `x = 20` (but `x < 0` is violated).
2. `x - 8 = -12` → `x = -4` (valid since `x < 0`).

Therefore, `x = -4` and `y = -6`.

#### Step 3: Find `n`
Substitute `x = -4` and `y = -6` into `h₃`:
`√((-4)² + (-6)²) = √(16 + 36) = √52 = √n`.

Thus, `n = 52`.

### Step 4: Verification
Check that all conditions are satisfied:
1. `x = -4 < 0` and `y = -6 < 0` → `h₀` is satisfied.
2. `|y| = 6` → `h₁` is satisfied.
3. `√((x - 8)² + (y - 3)²) = √((-12)² + (-9)²) = √(144 + 81) = √225 = 15` → `h₂` is satisfied.
4. `√(x² + y²) = √(16 + 36) = √52 = √n` → `h₃` is satisfied.

### Step 5: Abstract Plan

1. **Find `y`**:
   - From `h₁` and `y < 0`, deduce `y = -6`.

2. **Find `x`**:
   - Substitute `y = -6` into `h₂` to get `√((x - 8)² + 81) = 15`.
   - Square both sides to get `(x - 8)² + 81 = 225`.
   - Simplify to `(x - 8)² = 144` and solve for `x` to get `x = -4` (since `x < 0`).

3. **Find `n`**:
   - Substitute `x = -4` and `y = -6` into `h₃` to get `√(16 + 36) = √n`.
   - Simplify to `√52 = √n` and thus `n = 52`.

### Lean 4 `have` Statements

```lean4
theorem mathd_algebra_288
  (x y : ℝ)
  (n : NNReal)
  (h₀ : x < 0 ∧ y < 0)
  (h₁ : abs y = 6)
  (h₂ : Real.sqrt ((x - 8)^2 + (y - 3)^2) = 15)
  (h₃ : Real.sqrt (x^2 + y^2) = Real.sqrt n) :
  n = 52 := by
  have h_y : y = -6 := by sorry
  have h_x : x = -4 := by sorry
  have h_n : (n : ℝ) = 52 := by sorry
  have h_final : n = 52 := by sorry
  exact h_final
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_288
  (x y : ℝ)
  (n : NNReal)
  (h₀ : x < 0 ∧ y < 0)
  (h₁ : abs y = 6)
  (h₂ : Real.sqrt ((x - 8)^2 + (y - 3)^2) = 15)
  (h₃ : Real.sqrt (x^2 + y^2) = Real.sqrt n) :
  n = 52 := by
  have h_y : y = -6 := by
    have h₄ : y = -6 := by
      have h₅ : y < 0 := h₀.2
      have h₆ : abs y = 6 := h₁
      have h₇ : y = -6 := by
        cases' abs_cases y with h₈ h₈ <;> nlinarith
      exact h₇
    exact h₄
  
  have h_x : x = -4 := by
    have h₄ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15 := h₂
    have h₅ : y = -6 := h_y
    have h₆ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15 := by simpa [h₅] using h₄
    have h₇ : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
      have h₈ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15 := h₆
      have h₉ : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
        have h₁₀ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15 := h₆
        have h₁₁ : (x - 8) ^ 2 + (y - 3) ^ 2 ≥ 0 := by positivity
        have h₁₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) ^ 2 = (x - 8) ^ 2 + (y - 3) ^ 2 := by
          rw [Real.sq_sqrt] <;> nlinarith
        nlinarith
      nlinarith
    have h₈ : x = -4 := by
      have h₉ : y = -6 := h_y
      have h₁₀ : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := h₇
      rw [h₉] at h₁₀
      have h₁₁ : (x - 8) ^ 2 + (-6 - 3) ^ 2 = 225 := by linarith
      have h₁₂ : (x - 8) ^ 2 + (-9) ^ 2 = 225 := by linarith
      have h₁₃ : (x - 8) ^ 2 + 81 = 225 := by linarith
      have h₁₄ : (x - 8) ^ 2 = 144 := by linarith
      have h₁₅ : x - 8 = 12 ∨ x - 8 = -12 := by
        apply or_iff_not_imp_left.mpr
        intro h₁₆
        apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₆)
        nlinarith
      cases h₁₅ with
      | inl h₁₅ =>
        have h₁₆ : x - 8 = 12 := h₁₅
        have h₁₇ : x = 20 := by linarith
        nlinarith
      | inr h₁₅ =>
        have h₁₆ : x - 8 = -12 := h₁₅
        have h₁₇ : x = -4 := by linarith
        exact h₁₇
    exact h₈
  
  have h_n : (n : ℝ) = 52 := by
    have h₄ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n := h₃
    have h₅ : x = -4 := h_x
    have h₆ : y = -6 := h_y
    rw [h₅, h₆] at h₄
    have h₇ : Real.sqrt ((-4 : ℝ) ^ 2 + (-6 : ℝ) ^ 2) = Real.sqrt n := by simpa using h₄
    have h₈ : Real.sqrt ((-4 : ℝ) ^ 2 + (-6 : ℝ) ^ 2) = Real.sqrt 52 := by
      have h₉ : (-4 : ℝ) ^ 2 + (-6 : ℝ) ^ 2 = 52 := by norm_num
      rw [h₉]
    have h₉ : Real.sqrt n = Real.sqrt 52 := by linarith
    have h₁₀ : (n : ℝ) = 52 := by
      have h₁₁ : Real.sqrt n = Real.sqrt 52 := h₉
      have h₁₂ : (n : ℝ) = 52 := by
        have h₁₃ : Real.sqrt n = Real.sqrt 52 := h₁₁
        have h₁₄ : 0 ≤ (n : ℝ) := by exact_mod_cast NNReal.coe_nonneg n
        have h₁₅ : 0 ≤ (52 : ℝ) := by norm_num
        have h₁₆ : Real.sqrt n = Real.sqrt 52 := h₁₃
        have h₁₇ : (n : ℝ) = 52 := by
          nlinarith [Real.sqrt_nonneg n, Real.sqrt_nonneg 52, Real.sq_sqrt (show 0 ≤ (n : ℝ) by exact_mod_cast NNReal.coe_nonneg n), Real.sq_sqrt (show 0 ≤ (52 : ℝ) by norm_num)]
        exact h₁₇
      exact h₁₂
    exact h₁₀
  
  have h_final : n = 52 := by
    have h₅ : (n : ℝ) = 52 := h_n
    have h₆ : n = 52 := by
      norm_cast at h₅
      <;> simp_all [NNReal.eq_iff]
      <;> nlinarith
    exact h₆
  
  exact h_final
```