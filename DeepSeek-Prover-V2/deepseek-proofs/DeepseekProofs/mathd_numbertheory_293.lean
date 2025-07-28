import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, we need to understand the problem:
We have a four-digit number `20_7` where the blank is a digit `n` (i.e., `0 ≤ n ≤ 9`). The number `20n7` is a multiple of `11`. We need to find all possible values of `n` that satisfy this condition and show that `n = 5` is the only solution.

#### Step 1: Understand the Divisibility Condition
A number is divisible by `11` if and only if the alternating sum of its digits is divisible by `11`. For a four-digit number `abcd`, this is:
`a - b + c - d` is divisible by `11`.

For `20n7`, the alternating sum is:
`2 - 0 + n - 7 = (2 - 0) + (n - 7) = 2 + n - 7 = n - 5`.

Thus, the condition `11 ∣ 20n7` is equivalent to `11 ∣ (n - 5)`.

#### Step 2: Solve `11 ∣ (n - 5)`
Since `n` is a digit (`0 ≤ n ≤ 9`), we have `-5 ≤ n - 5 ≤ 4`. The multiples of `11` in this range are `-11, -1, 0, 11` (but `11` is too large). The only possible value is `n - 5 = 0`, i.e., `n = 5`.

But wait, we must also consider `n` as a digit (`0 ≤ n ≤ 9`). The condition `11 ∣ (n - 5)` is equivalent to `n ≡ 5 mod 11`, i.e., `n = 5` (since `n` is a digit).

But we must also check that `n = 5` is within the range `0 ≤ n ≤ 9`, which it is.

#### Step 3: Verification
For `n = 5`, the number is `2057`. The alternating sum is `2 - 0 + 5 - 7 = 0`, which is divisible by `11`. Thus, `n = 5` is indeed the solution.

### Step 4: Abstract Plan

1. **Understand the Alternating Sum Condition**:
   - For a four-digit number `abcd`, the condition `11 ∣ abcd` is equivalent to `11 ∣ (a - b + c - d)`.
   - For `20n7`, this becomes `11 ∣ (2 - 0 + n - 7) = 11 ∣ (n - 5)`.

2. **Solve `11 ∣ (n - 5)`**:
   - Since `n` is a digit (`0 ≤ n ≤ 9`), `n - 5` ranges from `-5` to `4`.
   - The only multiple of `11` in this range is `0`, so `n - 5 = 0` or `n = 5`.

3. **Verification**:
   - For `n = 5`, the number is `2057`, and `2 - 0 + 5 - 7 = 0` is divisible by `11`.

### Lean 4 Proof Sketch with `have`

```lean4
theorem mathd_numbertheory_293 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 11 ∣ 20 * 100 + 10 * n + 7) : n = 5 := by
  have h_main : n = 5 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_numbertheory_293 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 11 ∣ 20 * 100 + 10 * n + 7) : n = 5 := by
  have h_main : n = 5 := by
    have h₂ : n ≤ 9 := h₀
    interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h₁ ⊢ <;> omega
  exact h_main
