import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, recall that the problem is to find the units digit `n` (i.e., `n ∈ {0, ..., 9}`) such that the four-digit number `374n` is divisible by 18. 

A number is divisible by 18 if and only if it is divisible by both 2 and 9. 

1. **Divisibility by 2**: A number is divisible by 2 if its last digit is even. Here, the last digit is `n`, so `n` must be even. Thus, `n ∈ {0, 2, 4, 6, 8}`.

2. **Divisibility by 9**: A number is divisible by 9 if the sum of its digits is divisible by 9. The number `374n` can be written as `3740 + n` (since `374 * 10 + n = 3740 + n`). The digits of `3740 + n` are `3`, `7`, `4`, `0`, and `n` (if `n` is a single digit). However, since `n` is a digit, we can directly compute the sum of the digits of `374n` as `3 + 7 + 4 + n = 14 + n`. 

   The condition for divisibility by 9 is `14 + n ≡ 0 mod 9`, i.e., `14 + n ≡ 5 mod 9` (since `14 ≡ 5 mod 9`). 

   But we can simplify this further. The condition `14 + n ≡ 0 mod 9` is equivalent to `14 + n ≡ 5 mod 9` (since `14 ≡ 5 mod 9`). 

   However, we can also directly check the possible values of `n` in `{0, ..., 9}`:
   - `n = 0`: `14 + 0 = 14 ≡ 5 mod 9`
   - `n = 1`: `14 + 1 = 15 ≡ 6 mod 9`
   - `n = 2`: `14 + 2 = 16 ≡ 7 mod 9`
   - `n = 3`: `14 + 3 = 17 ≡ 8 mod 9`
   - `n = 4`: `14 + 4 = 18 ≡ 0 mod 9`
   - `n = 5`: `14 + 5 = 19 ≡ 1 mod 9`
   - `n = 6`: `14 + 6 = 20 ≡ 2 mod 9`
   - `n = 7`: `14 + 7 = 21 ≡ 3 mod 9`
   - `n = 8`: `14 + 8 = 22 ≡ 4 mod 9`
   - `n = 9`: `14 + 9 = 23 ≡ 5 mod 9`

   The only `n` in `{0, ..., 9}` that satisfies `14 + n ≡ 0 mod 9` is `n = 4`.

Thus, the units digit `n` must be `4`.

### Step 1: Abstract Plan

1. **Understand the Divisibility Condition**:
   - A number is divisible by 18 if and only if it is divisible by both 2 and 9.

2. **Divisibility by 2**:
   - The last digit of `374n` is `n`, so `n` must be even (`n ∈ {0, 2, 4, 6, 8}`).

3. **Divisibility by 9**:
   - The sum of the digits of `374n` is `3 + 7 + 4 + n = 14 + n`.
   - The condition is `14 + n ≡ 0 mod 9`, i.e., `n ≡ 4 mod 9`.
   - Check all possible `n ∈ {0, ..., 9}`: only `n = 4` satisfies this.

4. **Conclusion**:
   - The only possible value of `n` is `4`.

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_numbertheory_1124
  (n : ℕ)
  (h₀ : n ≤ 9)
  (h₁ : 18∣374 * 10 + n) :
  n = 4 := by
  have h_main : n = 4 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_numbertheory_1124
  (n : ℕ)
  (h₀ : n ≤ 9)
  (h₁ : 18∣374 * 10 + n) :
  n = 4 := by
  have h_main : n = 4 := by
    have h₂ : n ≤ 9 := h₀
    interval_cases n <;> norm_num at h₁ ⊢ <;>
    (try omega) <;>
    (try {
      norm_num at h₁
      omega
    }) <;>
    (try {
      omega
    })
  exact h_main
```