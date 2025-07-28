import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, let's understand the problem correctly. We have:
1. `a` is an even natural number (`Even a`).
2. The difference between the sum of the first 8 odd numbers (starting from 1) and the sum of 5 consecutive even integers starting from `a` is `4` (as an integer).

The sum of the first `n` odd numbers is `n²`. So, the sum of the first 8 odd numbers is `8² = 64`.

The sum of 5 consecutive even integers starting from `a` is:
`a + (a + 2) + (a + 4) + (a + 6) + (a + 8) = 5a + 20 = 5(a + 4)`.

The difference is:
`64 - 5(a + 4) = 4` (as an integer).

Simplify the equation:
`64 - 5a - 20 = 4`  
`44 - 5a = 4`  
`40 = 5a`  
`a = 8`.

But wait, the Lean 4 statement is:
`∑ k in Finset.range 8, (2 * k + 1) - ∑ k in Finset.range 5, (a + 2 * k) = (4 : ℤ)`.

This is interpreted as:
`(∑ k in Finset.range 8, (2 * k + 1)) - (∑ k in Finset.range 5, (a + 2 * k)) = 4`.

But the Lean 4 code uses `-` for subtraction, which is not the same as the mathematical notation. The Lean 4 code is correct because `-` is the binary operation for subtraction in `ℤ`.

### Step 1: Compute the Sums

First, compute the sum of the first 8 odd numbers:
`∑ k in Finset.range 8, (2 * k + 1) = ∑ k in Finset.range 8, (2 * k + 1) = 1 + 3 + 5 + 7 + 9 + 11 + 13 + 15 = 64`.

Next, compute the sum of the first 5 even integers starting from `a`:
`∑ k in Finset.range 5, (a + 2 * k) = (a + 0) + (a + 2) + (a + 4) + (a + 6) + (a + 8) = 5a + 20`.

### Step 2: Formulate the Equation

The difference is:
`64 - (5a + 20) = 4`.

Simplify:
`64 - 5a - 20 = 4`  
`44 - 5a = 4`  
`40 = 5a`  
`a = 8`.

### Step 3: Verification

The smallest even integer is `8`, and the next four are `10`, `12`, `14`, `16`. The sum is `8 + 10 + 12 + 14 + 16 = 60`, and the difference is `64 - 60 = 4`, which matches the given condition.

### Step 4: Abstract Plan

1. **Compute the sum of the first 8 odd numbers**:
   - The sum is `64`.

2. **Compute the sum of the first 5 even integers starting from `a`**:
   - The sum is `5a + 20`.

3. **Formulate the equation**:
   - The difference is `64 - (5a + 20) = 4`.

4. **Solve for `a`**:
   - Simplify to `40 = 5a` and get `a = 8`.

5. **Verify the solution**:
   - Check that `a = 8` satisfies the original condition.

### Lean 4 Proof Sketch with `have`

```lean4
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ∑ k in Finset.range 8, (2 * k + 1) - ∑ k in Finset.range 5, (a + 2 * k) = (4 : ℤ)) :
    a = 8 := by
  have h_sum_odd : ∑ k in Finset.range 8, (2 * k + 1) = 64 := by sorry
  have h_sum_even : ∑ k in Finset.range 5, (a + 2 * k) = 5 * a + 20 := by sorry
  have h_main : a = 8 := by sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ∑ k in Finset.range 8, (2 * k + 1) - ∑ k in Finset.range 5, (a + 2 * k) = (4 : ℤ)) :
    a = 8 := by
  have h_sum_odd : ∑ k in Finset.range 8, (2 * k + 1) = 64 := by
    simp [Finset.sum_range_succ, mul_add, mul_one, add_assoc]
    <;> norm_num
    <;> rfl
  
  have h_sum_even : ∑ k in Finset.range 5, (a + 2 * k) = 5 * a + 20 := by
    have h₂ : ∑ k in Finset.range 5, (a + 2 * k) = ∑ k in Finset.range 5, (a + 2 * k) := rfl
    rw [h₂]
    simp [Finset.sum_range_succ, mul_add, mul_one, add_assoc, add_comm, add_left_comm]
    <;> ring_nf at *
    <;> omega
  
  have h_main : a = 8 := by
    have h₂ : (∑ k in Finset.range 8, (2 * k + 1) : ℤ) - ∑ k in Finset.range 5, (a + 2 * k : ℤ) = 4 := by
      exact_mod_cast h₁
    simp [h_sum_odd, h_sum_even] at h₂
    norm_num at h₂
    have h₃ : a ≤ 16 := by
      by_contra h
      have h₄ : a ≥ 17 := by omega
      have h₅ : (a : ℤ) ≥ 17 := by exact_mod_cast h₄
      nlinarith
    interval_cases a <;> norm_num at h₂ ⊢ <;> omega
  
  exact h_main
