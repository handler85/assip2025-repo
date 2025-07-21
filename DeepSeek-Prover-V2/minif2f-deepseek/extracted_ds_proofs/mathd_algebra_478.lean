import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We are given:
1. `b > 0`, `h > 0`, `v > 0` (all positive real numbers).
2. `v = (1/3) * (b * h)`.
3. `b = 30`.
4. `h = 13/2`.

We need to prove that `v = 65`.

**Approach:**
Substitute the given values of `b` and `h` into the equation for `v` to directly compute `v`.

**Detailed Steps:**
1. Substitute `b = 30` and `h = 13/2` into `v = (1/3) * (b * h)`:
   \[
   v = \frac{1}{3} \cdot (30 \cdot \frac{13}{2}) = \frac{1}{3} \cdot (15 \cdot 13) = \frac{1}{3} \cdot 195 = 65.
   \]
   Here, we first simplify `30 * (13/2) = 15 * 13 = 195` and then divide by `3` to get `65`.

2. Alternatively, we can directly compute `b * h` first:
   \[
   b \cdot h = 30 \cdot \frac{13}{2} = 15 \cdot 13 = 195.
   \]
   Then, multiply by `1/3`:
   \[
   v = \frac{1}{3} \cdot 195 = 65.
   \]

Both approaches lead to the same result, `v = 65`.

### Step 1: Abstract Plan

1. **Substitute the given values of `b` and `h` into the expression for `v`.**
   - `b = 30`
   - `h = 13/2`
   - `v = (1/3) * (b * h)`

2. **Calculate `b * h`:**
   - `b * h = 30 * (13/2) = 15 * 13 = 195`

3. **Calculate `v`:**
   - `v = (1/3) * 195 = 65`

4. **Conclude that `v = 65`.**

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_algebra_478
  (b h v : ℝ)
  (h₀ : 0 < b ∧ 0 < h ∧ 0 < v)
  (h₁ : v = 1 / 3 * (b * h))
  (h₂ : b = 30)
  (h₃ : h = 13 / 2) :
  v = 65 := by
  have h_main : v = 65 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_478
  (b h v : ℝ)
  (h₀ : 0 < b ∧ 0 < h ∧ 0 < v)
  (h₁ : v = 1 / 3 * (b * h))
  (h₂ : b = 30)
  (h₃ : h = 13 / 2) :
  v = 65 := by
  have h_main : v = 65 := by
    have h₄ : v = 1 / 3 * (b * h) := h₁
    rw [h₄]
    rw [h₂, h₃]
    norm_num
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  exact h_main
```