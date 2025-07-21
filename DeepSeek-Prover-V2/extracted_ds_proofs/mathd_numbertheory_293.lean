import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, let's understand the problem correctly. We have a four-digit number `20_7` where the underscore represents a digit `n` (where `n` is a digit from 0 to 9, inclusive). The number is `20 * 100 + 10 * n + 7 = 2000 + 10 * n + 7 = 2007 + 10 * n`. 

But wait, the Lean code interprets the number as `20 * 100 + 10 * n + 7 = 2000 + 10 * n + 7 = 2007 + 10 * n`, which is correct. 

The condition is that `11` divides `2007 + 10 * n`, i.e., `2007 + 10 * n ≡ 0 mod 11`. 

First, simplify `2007 mod 11`:
- `11 * 182 = 2002`
- `2007 - 2002 = 5`
So, `2007 ≡ 5 mod 11`. 

Thus, the condition becomes `5 + 10 * n ≡ 0 mod 11`, i.e., `10 * n ≡ -5 ≡ 6 mod 11` (since `-5 + 11 = 6`). 

Multiply both sides by the modular inverse of `10` modulo `11`. Note that `10 * 10 = 100 ≡ 1 mod 11`, so the inverse of `10` is `10`. 

Thus, `n ≡ 6 * 10 ≡ 60 ≡ 5 mod 11` (since `60 - 5 * 11 = 60 - 55 = 5`). 

Therefore, the only solution is `n = 5`. 

But wait, we can also directly check all possible values of `n` from `0` to `9` to see which one satisfies `11 ∣ 2007 + 10 * n`. 

Alternatively, we can use the fact that `11 ∣ 2007 + 10 * n` is equivalent to `11 ∣ 2007 - 10 * n`, i.e., `11 ∣ 2007 - 10 * n`. 

But `2007 ≡ 5 mod 11`, so `11 ∣ 2007 - 10 * n` is equivalent to `11 ∣ 5 - 10 * n`, i.e., `11 ∣ 5 - 10 * n` or `11 ∣ 10 * n - 5`. 

But `10 ≡ -1 mod 11`, so `10 * n ≡ -n mod 11`, and `5 ≡ 5 mod 11`. 

Thus, `11 ∣ 10 * n - 5` is equivalent to `11 ∣ -n - 5`, i.e., `11 ∣ n + 5` (since `-n - 5 = -(n + 5)`). 

Therefore, `11 ∣ 2007 + 10 * n` is equivalent to `11 ∣ n + 5`. 

This is much simpler! 

Now, we can find all `n` from `0` to `9` such that `11 ∣ n + 5`. 

`n + 5 ≡ 0 mod 11` is equivalent to `n ≡ -5 ≡ 6 mod 11`. 

Thus, the only solution is `n = 6` (since `6 ≡ 6 mod 11`). 

But wait, this contradicts our earlier conclusion that `n = 5` is the solution. 

Where is the mistake? 

The mistake is in the simplification of `2007 mod 11`. 

Let's recompute `2007 mod 11` correctly:
- `11 * 182 = 2002`
- `2007 - 2002 = 5`
So, `2007 ≡ 5 mod 11`. 

Thus, the correct condition is `11 ∣ 5 + 10 * n`, i.e., `11 ∣ 10 * n + 5`. 

But `10 ≡ -1 mod 11`, so `10 * n ≡ -n mod 11`, and `5 ≡ 5 mod 11`. 

Thus, `11 ∣ 10 * n + 5` is equivalent to `11 ∣ -n + 5`, i.e., `11 ∣ n - 5` (since `-n + 5 = 5 - n`). 

Therefore, `11 ∣ 10 * n + 5` is equivalent to `11 ∣ n - 5`. 

Now, we can find all `n` from `0` to `9` such that `11 ∣ n - 5`. 

`n - 5 ≡ 0 mod 11` is equivalent to `n ≡ 5 mod 11`. 

Thus, the only solution is `n = 5` (since `5 ≡ 5 mod 11`). 

This is consistent with our earlier conclusion. 

### Step 1: Abstract Plan

1. **Understand the Problem**:
   - We have a four-digit number `20_7` where the underscore represents a digit `n` (from `0` to `9`).
   - The number is `2007 + 10 * n`.
   - We need to find `n` such that `11` divides `2007 + 10 * n`.

2. **Simplify the Condition**:
   - `11 ∣ 2007 + 10 * n` is equivalent to `11 ∣ 10 * n + 2007` (since `11 ∣ a + b` iff `11 ∣ a - b`).
   - Alternatively, `11 ∣ 2007 + 10 * n` is equivalent to `11 ∣ 10 * n + 5` (since `2007 ≡ 5 mod 11`).

3. **Find `n`**:
   - We need `11 ∣ 10 * n + 5`.
   - Since `10 ≡ -1 mod 11`, this is equivalent to `11 ∣ -n + 5`, i.e., `11 ∣ n - 5`.
   - Thus, `n ≡ 5 mod 11`.
   - The only digit `n` in `0..9` satisfying this is `n = 5`.

4. **Verification**:
   - For `n = 5`, the number is `2057`.
   - `2057 ÷ 11 = 187` (since `11 * 187 = 2057`).
   - Thus, `11 ∣ 2057`, and `n = 5` is correct.

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_numbertheory_293
  (n : ℕ)
  (h₀ : n ≤ 9)
  (h₁ : 11∣20 * 100 + 10 * n + 7) :
  n = 5 := by
  have h_main : n = 5 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_numbertheory_293
  (n : ℕ)
  (h₀ : n ≤ 9)
  (h₁ : 11∣20 * 100 + 10 * n + 7) :
  n = 5 := by
  have h_main : n = 5 := by
    have h₂ : n ≤ 9 := h₀
    interval_cases n <;> norm_num [Nat.dvd_iff_mod_eq_zero] at h₁ ⊢ <;> omega
  exact h_main
```