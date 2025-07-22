import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, we need to understand the problem correctly. We are to find the number of 4-digit positive integers (i.e., integers between 1000 and 9999, inclusive) that have only even digits and are divisible by 5.

#### Key Observations:
1. A number is divisible by 5 if and only if its last digit is 0 or 5. However, since the digits must be even, the last digit can only be 0 (as 5 is odd).
2. Therefore, the last digit must be 0, and the number must be of the form `abcd0` where `a, b, c, d` are even digits (i.e., `0, 2, 4, 6, 8`).
3. The first digit `a` cannot be 0, so it can be any of `2, 4, 6, 8` (4 choices).
4. The second digit `b` can be any of `0, 2, 4, 6, 8` (5 choices).
5. The third digit `c` can be any of `0, 2, 4, 6, 8` (5 choices).
6. The last digit `d` is fixed to be `0` (1 choice).

#### Calculation:
The total number of such numbers is `4 * 5 * 5 * 1 = 100`.

#### Verification:
- The first digit has 4 choices (2, 4, 6, 8).
- The second digit has 5 choices (0, 2, 4, 6, 8).
- The third digit has 5 choices (0, 2, 4, 6, 8).
- The last digit is fixed to 0.

Thus, the total is `4 * 5 * 5 * 1 = 100`.

### Step 1: Abstract Plan

1. **Understand the Set `S`**:
   - `S` is the set of 4-digit positive integers (1000 ≤ n ≤ 9999) with all even digits and divisible by 5.

2. **Characterize the Elements of `S`**:
   - A number is divisible by 5 if and only if its last digit is 0 or 5.
   - All digits must be even, so the last digit must be 0.
   - The first digit cannot be 0, so it is one of 2, 4, 6, 8 (4 choices).
   - The second and third digits can be any of 0, 2, 4, 6, 8 (5 choices each).
   - The last digit is fixed to 0 (1 choice).

3. **Count the Elements of `S`**:
   - The number of choices is `4 * 5 * 5 * 1 = 100`.

### Step 2: Lean 4 `have` Statements

```lean4
theorem amc12a_2020_p4 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
    S.card = 100 := by
  have h_main : S.card = 100 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem amc12a_2020_p4 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
    S.card = 100 := by
  have h_main : S.card = 100 := by
    have : S = Finset.filter (fun n => n % 10 = 0) (Finset.filter (fun n => (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d)) (Finset.filter (fun n => n % 5 = 0) (Finset.Icc 1000 9999)))) := by
      apply Finset.ext
      intro n
      simp only [Finset.mem_filter, Finset.mem_Icc, h₀, Nat.mod_eq_of_lt]
      <;>
      (try omega) <;>
      (try
        {
          constructor <;> intro h <;>
          (try simp_all [Nat.even_iff, Nat.odd_iff, Nat.mod_eq_of_lt]) <;>
          (try omega) <;>
          (try omega) <;>
          (try omega)
        }) <;>
      (try
        {
          aesop
        }) <;>
      (try
        {
          norm_num at * <;>
          omega
        })
    rw [this]
    rfl
  exact h_main
