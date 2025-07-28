import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof

**Problem Analysis:**
We are given a cone with:
1. The area of the base `B = 30` square units.
2. The height `h = 6.5` units.
3. The volume `V` is given by the formula `V = (1/3) * B * h`.
4. We need to prove that `V = 65` cubic units.

**Given:**
1. `b > 0`, `h > 0`, `v > 0` (these are the given conditions in Lean).
2. `v = (1/3) * b * h` (the volume formula).
3. `b = 30` (the area of the base).
4. `h = 13/2` (the height).

**To Prove:** `v = 65`.

**Proof:**
1. Substitute `b = 30` and `h = 13/2` into the volume formula `v = (1/3) * b * h`:
   \[
   v = \frac{1}{3} \cdot 30 \cdot \frac{13}{2}
   \]
2. Simplify the expression:
   \[
   v = \frac{1}{3} \cdot 30 \cdot \frac{13}{2} = 10 \cdot \frac{13}{2} = 10 \cdot 6.5 = 65
   \]
   Alternatively, we can simplify the product first:
   \[
   \frac{1}{3} \cdot 30 = 10
   \]
   and then:
   \[
   10 \cdot \frac{13}{2} = \frac{130}{2} = 65
   \]
   So, `v = 65`.

### Step 1: Abstract Plan

1. **Substitute the Given Values**:
   - Replace `b` with `30` and `h` with `13/2` in the volume formula `v = (1/3) * b * h`.

2. **Simplify the Expression**:
   - Calculate `(1/3) * 30` to get `10`.
   - Multiply `10` by `13/2` to get `65`.

3. **Conclude the Proof**:
   - The simplified expression is `v = 65`, which is the desired result.

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_algebra_478 (b h v : ℝ) (h₀ : 0 < b ∧ 0 < h ∧ 0 < v) (h₁ : v = 1 / 3 * (b * h))
    (h₂ : b = 30) (h₃ : h = 13 / 2) : v = 65 := by
  have h_main : v = 65 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_478 (b h v : ℝ) (h₀ : 0 < b ∧ 0 < h ∧ 0 < v) (h₁ : v = 1 / 3 * (b * h))
    (h₂ : b = 30) (h₃ : h = 13 / 2) : v = 65 := by
  have h_main : v = 65 := by
    have h₄ : v = 1 / 3 * (b * h) := h₁
    rw [h₄]
    rw [h₂, h₃]
    norm_num
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  exact h_main
