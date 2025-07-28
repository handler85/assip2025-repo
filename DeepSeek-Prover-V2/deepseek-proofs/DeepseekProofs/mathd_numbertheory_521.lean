import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

**Problem Analysis:**
We are given two consecutive positive even integers `m` and `n` (with `m > n`) such that:
1. `m - n = 2` (since they are consecutive even integers, the difference is 2).
2. `m * n = 288`.

We need to find the value of `m` and show that it is `18`.

**Key Observations:**
1. Since `m` and `n` are consecutive even integers, we can express them as:
   - `m = n + 2` (or `n = m - 2`).
   But we are given `m - n = 2`, which is equivalent to `m = n + 2` (since `m > n`).

2. Substitute `m = n + 2` into the product equation:
   \[
   (n + 2) \cdot n = 288 \implies n^2 + 2n - 288 = 0.
   \]

3. Solve the quadratic equation `n² + 2n - 288 = 0`:
   \[
   n = \frac{-2 \pm \sqrt{4 + 1152}}{2} = \frac{-2 \pm \sqrt{1156}}{2} = \frac{-2 \pm 34}{2}.
   \]
   The solutions are:
   \[
   n = \frac{32}{2} = 16 \quad \text{and} \quad n = \frac{-36}{2} = -18.
   \]
   Since `n` is a positive integer, we discard `n = -18` and take `n = 16`.

4. Find `m`:
   \[
   m = n + 2 = 16 + 2 = 18.
   \]

**Verification:**
1. `m - n = 18 - 16 = 2` ✔️.
2. `m * n = 18 * 16 = 288` ✔️.

### Step 1: Abstract Plan

1. **Express `m` in terms of `n`:**
   - Since `m` and `n` are consecutive even integers, `m = n + 2`.

2. **Substitute into the product equation:**
   - `(n + 2) * n = 288` simplifies to `n² + 2n - 288 = 0`.

3. **Solve the quadratic equation:**
   - The solutions are `n = 16` and `n = -18`.
   - Since `n` is a positive integer, `n = 16`.

4. **Find `m`:**
   - `m = n + 2 = 18`.

5. **Verify the solution:**
   - Check that `m - n = 2` and `m * n = 288`.

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have h_main : m = 18 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by
  have h_main : m = 18 := by
    have h₄ : m ∣ 288 := by
      use n
      linarith
    have h₅ : m ≤ 288 := Nat.le_of_dvd (by norm_num) h₄
    interval_cases m <;> norm_num [Nat.even_iff, Nat.mul_mod, Nat.add_mod, Nat.mod_mod] at h₀ h₁ h₂ h₃ ⊢ <;>
      (try omega) <;> (try contradiction) <;> (try {
        have h₆ := h₂
        omega
      }) <;> (try {
        have h₆ := h₂
        omega
      }) <;> (try {
        have h₆ := h₂
        omega
      })
    <;> omega
  exact h_main
