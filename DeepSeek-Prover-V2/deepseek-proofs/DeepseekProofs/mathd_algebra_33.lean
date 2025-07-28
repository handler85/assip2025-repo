import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof

**Problem Analysis:**
We are given three real numbers \( x, y, z \) with \( x \neq 0 \), and two equations:
1. \( 2x = 5y \)
2. \( 7y = 10z \)

We need to prove that \( \frac{z}{x} = \frac{7}{25} \).

**Approach:**
1. First, express \( y \) in terms of \( x \) using the first equation:
   \[ y = \frac{2x}{5} \]
2. Substitute this expression for \( y \) into the second equation to find \( z \) in terms of \( x \):
   \[ 7y = 10z \implies 7 \cdot \frac{2x}{5} = 10z \implies \frac{14x}{5} = 10z \implies z = \frac{14x}{50} = \frac{7x}{25} \]
3. Now, compute \( \frac{z}{x} \):
   \[ \frac{z}{x} = \frac{\frac{7x}{25}}{x} = \frac{7x}{25x} = \frac{7}{25} \]
   (since \( x \neq 0 \), we can cancel \( x \).)

**Verification:**
1. The first step is correct because we are simply solving for \( y \) in terms of \( x \).
2. The second step is correct because we substitute \( y \) and solve for \( z \).
3. The third step is correct because we simplify the fraction \( \frac{z}{x} \).

### Step-by-Step Abstract Plan

1. **Express \( y \) in terms of \( x \):**
   - From \( 2x = 5y \), solve for \( y \) to get \( y = \frac{2x}{5} \).

2. **Express \( z \) in terms of \( x \):**
   - Substitute \( y = \frac{2x}{5} \) into \( 7y = 10z \) to get \( 7 \cdot \frac{2x}{5} = 10z \).
   - Simplify to \( \frac{14x}{5} = 10z \), then \( z = \frac{14x}{50} = \frac{7x}{25} \).

3. **Compute \( \frac{z}{x} \):**
   - Substitute \( z = \frac{7x}{25} \) to get \( \frac{z}{x} = \frac{\frac{7x}{25}}{x} = \frac{7}{25} \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have h_y : y = (2 * x) / 5 := by sorry
  have h_z : z = (7 * x) / 25 := by sorry
  have h_main : z / x = 7 / 25 := by sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  have h_y : y = (2 * x) / 5 := by
    have h₃ : 2 * x = 5 * y := h₁
    have h₄ : y = (2 * x) / 5 := by
      apply Eq.symm
      ring_nf at h₃ ⊢
      linarith
    exact h₄
  
  have h_z : z = (7 * x) / 25 := by
    have h₃ : 7 * y = 10 * z := h₂
    rw [h_y] at h₃
    ring_nf at h₃ ⊢
    nlinarith
  
  have h_main : z / x = 7 / 25 := by
    rw [h_z]
    have h₃ : x ≠ 0 := h₀
    field_simp [h₃]
    <;> ring_nf
    <;> field_simp [h₃]
    <;> nlinarith
  
  rw [h_main]
  <;> norm_num
