import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, let's recall the problem and the given conditions:
1. We have a point \((x, y)\) in the plane with both coordinates negative: \(x < 0\) and \(y < 0\).
2. The point is a distance of 6 units from the \(x\)-axis. This means \(|y| = 6\) (since the distance from the \(x\)-axis is the absolute value of the \(y\)-coordinate).
3. The point is a distance of 15 units from the point \((8, 3)\). This means \(\sqrt{(x - 8)^2 + (y - 3)^2} = 15\).
4. The point is a distance \(\sqrt{n}\) from the origin. This means \(\sqrt{x^2 + y^2} = \sqrt{n}\).
5. We need to find \(n = 52\).

#### Step 1: Simplify \(|y| = 6\)
Since \(y < 0\), \(|y| = -y\). Thus, \(-y = 6 \Rightarrow y = -6\).

#### Step 2: Substitute \(y = -6\) into the distance from \((8, 3)\)
The distance is \(\sqrt{(x - 8)^2 + (y - 3)^2} = 15\). Substitute \(y = -6\):
\[
\sqrt{(x - 8)^2 + (-6 - 3)^2} = 15 \Rightarrow \sqrt{(x - 8)^2 + 81} = 15.
\]
Square both sides:
\[
(x - 8)^2 + 81 = 225.
\]
Simplify:
\[
(x - 8)^2 = 144.
\]
Take square roots:
\[
x - 8 = \pm 12.
\]
Thus:
1. \(x - 8 = 12 \Rightarrow x = 20\) (but \(x < 0\) is violated).
2. \(x - 8 = -12 \Rightarrow x = -4\) (valid since \(x < 0\)).

#### Step 3: Find \(x = -4\) and \(y = -6\)
We have \(x = -4\) and \(y = -6\).

#### Step 4: Find \(n\)
The distance from the origin is \(\sqrt{x^2 + y^2} = \sqrt{(-4)^2 + (-6)^2} = \sqrt{16 + 36} = \sqrt{52} = \sqrt{4 \cdot 13} = 2 \sqrt{13}\).

But wait, this contradicts the given condition \(\sqrt{x^2 + y^2} = \sqrt{n}\). 

But we have:
\[
\sqrt{x^2 + y^2} = \sqrt{(-4)^2 + (-6)^2} = \sqrt{16 + 36} = \sqrt{52} = 2 \sqrt{13}.
\]
But the problem states that \(\sqrt{x^2 + y^2} = \sqrt{n}\), so:
\[
\sqrt{n} = 2 \sqrt{13} \Rightarrow n = (2 \sqrt{13})^2 = 4 \cdot 13 = 52.
\]
Thus, \(n = 52\) is correct.

#### Verification
1. \(x = -4 < 0\) and \(y = -6 < 0\) are satisfied.
2. \(|y| = 6\) is satisfied.
3. \(\sqrt{(x - 8)^2 + (y - 3)^2} = \sqrt{144 + 81} = \sqrt{225} = 15\) is satisfied.
4. \(\sqrt{x^2 + y^2} = \sqrt{16 + 36} = \sqrt{52} = 2 \sqrt{13}\) is satisfied.
5. \(n = 52\) is correct.

### Step-by-Step Abstract Plan

1. **Simplify \(|y| = 6\)**:
   - Since \(y < 0\), \(|y| = -y\).
   - Thus, \(-y = 6 \Rightarrow y = -6\).

2. **Substitute \(y = -6\) into the distance from \((8, 3)\)**:
   - Compute \((x - 8)^2 + (y - 3)^2 = (x - 8)^2 + 81\).
   - Set \(\sqrt{(x - 8)^2 + 81} = 15\) and square both sides to get \((x - 8)^2 = 144\).
   - Solve for \(x\) to get \(x = -4\) (since \(x < 0\)).

3. **Find \(n\)**:
   - Compute \(x^2 + y^2 = 16 + 36 = 52\).
   - Thus, \(\sqrt{n} = \sqrt{52} = 2 \sqrt{13}\), so \(n = 52\).

### Lean 4 `have` Statements

```lean4
theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  have h_y : y = -6 := by sorry
  have h_x : x = -4 := by sorry
  have h_n : (n : ℝ) = 52 := by sorry
  have h_final : n = 52 := by sorry
  exact h_final
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by
  have h_y : y = -6 := by
    have h₄ : y = -6 := by
      cases' abs_cases y with h₅ h₅ <;>
        nlinarith
    exact h₄
  
  have h_x : x = -4 := by
    have h₄ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15 := h₂
    have h₅ : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
      have h₆ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15 := h₄
      have h₇ : (x - 8) ^ 2 + (y - 3) ^ 2 = 225 := by
        have h₈ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15 := h₆
        have h₉ : (x - 8) ^ 2 + (y - 3) ^ 2 ≥ 0 := by nlinarith
        have h₁₀ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) ^ 2 = (x - 8) ^ 2 + (y - 3) ^ 2 := by
          rw [Real.sq_sqrt] <;> nlinarith
        nlinarith
      nlinarith
    have h₆ : y = -6 := h_y
    have h₇ : x = -4 := by
      rw [h₆] at h₅
      nlinarith [sq_nonneg (x + 4), sq_nonneg (x - 4), sq_nonneg (x - 8), sq_nonneg (x + 8)]
    exact h₇
  
  have h_n : (n : ℝ) = 52 := by
    have h₄ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n := h₃
    have h₅ : x = -4 := h_x
    have h₆ : y = -6 := h_y
    have h₇ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n := h₄
    have h₈ : (x : ℝ) ^ 2 + y ^ 2 = n := by
      have h₉ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n := h₇
      have h₁₀ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n := h₉
      have h₁₁ : (x : ℝ) ^ 2 + y ^ 2 = n := by
        have h₁₂ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n := h₁₀
        have h₁₃ : Real.sqrt (x ^ 2 + y ^ 2) ^ 2 = (Real.sqrt n) ^ 2 := by rw [h₁₂]
        have h₁₄ : (x ^ 2 + y ^ 2 : ℝ) = n := by
          have h₁₅ : Real.sqrt (x ^ 2 + y ^ 2) ^ 2 = x ^ 2 + y ^ 2 := by
            rw [Real.sq_sqrt] <;> nlinarith
          have h₁₆ : (Real.sqrt n : ℝ) ^ 2 = n := by
            rw [Real.sq_sqrt] <;> exact mod_cast NNReal.coe_nonneg n
          nlinarith
        nlinarith
      nlinarith
    have h₉ : (n : ℝ) = 52 := by
      rw [h₈]
      norm_num [h_x, h_y]
      <;>
      nlinarith
    exact h₉
  
  have h_final : n = 52 := by
    have h₅ : (n : ℝ) = 52 := h_n
    have h₆ : n = 52 := by
      apply_fun (fun x : ℝ => ⟨x, by linarith⟩ : ℝ → NNReal) at h₅
      norm_cast at h₅ ⊢
      <;> simp_all
    exact h₆
  
  exact h_final
```