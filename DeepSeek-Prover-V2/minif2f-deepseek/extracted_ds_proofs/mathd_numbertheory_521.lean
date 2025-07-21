import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

**Problem Analysis:**
We have two positive even integers `m` and `n` such that:
1. `m - n = 2` (as natural numbers, this implies `m ≥ n` and `m = n + 2`).
2. `m * n = 288`.

We need to find `m` and show that it is `18`.

**Approach:**
1. From `m - n = 2`, we can express `m` as `m = n + 2` (since `m ≥ n` is implied by `m - n = 2` in natural numbers).
2. Substitute `m = n + 2` into the second equation `m * n = 288` to get `(n + 2) * n = 288`, i.e., `n² + 2n - 288 = 0`.
3. Solve the quadratic equation `n² + 2n - 288 = 0` for `n` to find the positive integer solution.
4. The quadratic equation has roots `n = (-2 ± sqrt(4 + 1152))/2 = (-2 ± sqrt(1156))/2 = (-2 ± 34)/2`, i.e., `n = 16` or `n = -18`. Since `n` is a natural number, `n = 16` is the only solution.
5. Substitute `n = 16` back into `m = n + 2` to get `m = 18`.
6. Verify that `m = 18` and `n = 16` satisfy all original conditions:
   - `m - n = 18 - 16 = 2`.
   - `m * n = 18 * 16 = 288`.
   - `m` and `n` are even.

**Verification of `m` and `n` being even:**
- `m = 18` is even.
- `n = 16` is even.

**Conclusion:**
The only solution is `m = 18` and `n = 16`.

### Step 1: Abstract Plan

1. **Express `m` in terms of `n`:**
   - From `m - n = 2`, deduce that `m = n + 2` (since `m ≥ n` is implied by the natural number subtraction).

2. **Substitute into the product equation:**
   - Replace `m` with `n + 2` in `m * n = 288` to get `(n + 2) * n = 288`.

3. **Expand and rearrange the equation:**
   - Expand to `n² + 2n = 288`.
   - Rearrange to `n² + 2n - 288 = 0`.

4. **Solve the quadratic equation for `n`:**
   - Use the quadratic formula to find `n = 16` (the other root is negative and discarded).

5. **Find `m`:**
   - Substitute `n = 16` back into `m = n + 2` to get `m = 18`.

6. **Verify the solution:**
   - Check that `m = 18` and `n = 16` satisfy all original conditions.

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_numbertheory_521
  (m n : ℕ)
  (h₀ : Even m)
  (h₁ : Even n)
  (h₂ : m - n = 2)
  (h₃ : m * n = 288) :
  m = 18 := by
  have h_main : m = 18 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_numbertheory_521
  (m n : ℕ)
  (h₀ : Even m)
  (h₁ : Even n)
  (h₂ : m - n = 2)
  (h₃ : m * n = 288) :
  m = 18 := by
  have h_main : m = 18 := by
    have h₄ : m ≥ n := by
      omega
    have h₅ : m = n + 2 := by
      omega
    rw [h₅] at h₃
    have h₆ : (n + 2) * n = 288 := by
      omega
    have h₇ : n ≤ 18 := by
      nlinarith
    interval_cases n <;> norm_num at h₆ ⊢ <;>
      (try omega) <;>
      (try
        {
          have h₈ : Even m := h₀
          have h₉ : Even n := h₁
          simp_all [Nat.even_iff, Nat.mul_mod, Nat.add_mod]
          <;> omega
        }) <;>
      (try omega)
    <;>
    (try omega)
    <;>
    (try omega)
  exact h_main
```