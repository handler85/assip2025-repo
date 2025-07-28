import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, we need to prove that for any natural number `n`, `11` divides `10^n - (-1)^n` in the integers. 

#### Observations:
1. `(-1)^n` is `1` when `n` is even and `-1` when `n` is odd.
2. `10^n` is congruent to `1` modulo `9` because `10 ≡ 1 mod 9`, so `10^n ≡ 1^n ≡ 1 mod 9`.
3. `10^n` is congruent to `10 ≡ -1 mod 11` when `n` is odd, and `10^n ≡ 1 mod 11` when `n` is even.

#### Key Idea:
We can directly compute `10^n - (-1)^n` modulo `11` for all `n` and show that it is `0` modulo `11`.

#### Proof:
1. If `n` is even, say `n = 2k`, then `(-1)^n = 1` and `10^n - (-1)^n = 10^{2k} - 1`. We need to show that `10^{2k} - 1 ≡ 0 mod 11`, i.e., `10^{2k} ≡ 1 mod 11`. Since `10 ≡ -1 mod 11`, we have `10^{2k} ≡ (-1)^{2k} ≡ 1 mod 11` because `2k` is even.
2. If `n` is odd, say `n = 2k + 1`, then `(-1)^n = -1` and `10^n - (-1)^n = 10^{2k + 1} + 1`. We need to show that `10^{2k + 1} + 1 ≡ 0 mod 11`, i.e., `10^{2k + 1} ≡ -1 mod 11`. Since `10 ≡ -1 mod 11`, we have `10^{2k + 1} ≡ (-1)^{2k + 1} ≡ -1 mod 11` because `2k + 1` is odd.

Thus, in all cases, `11` divides `10^n - (-1)^n`.

### Step 1: Abstract Plan

1. **Case 1: `n` is even (`n = 2k`)**
   - `(-1)^n = 1`
   - `10^n - (-1)^n = 10^{2k} - 1`
   - Prove `10^{2k} ≡ 1 mod 11` because `10 ≡ -1 mod 11` and `2k` is even.

2. **Case 2: `n` is odd (`n = 2k + 1`)**
   - `(-1)^n = -1`
   - `10^n - (-1)^n = 10^{2k + 1} + 1`
   - Prove `10^{2k + 1} ≡ -1 mod 11` because `10 ≡ -1 mod 11` and `2k + 1` is odd.

### Step 2: Lean 4 `have` Statements

```lean4
theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  have h_main : 11 ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by
  have h_main : 11 ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := by
    have h : ∀ n : ℕ, 11 ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        simp [pow_succ, Int.mul_emod, Int.sub_emod] at ih ⊢
        <;> omega
    exact h n
  exact h_main
