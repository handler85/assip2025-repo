import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, we need to find an integer `n` such that:
1. `0 ≤ n < 101`,
2. `123456 ≡ n mod 101`,
3. `101` divides `123456 - n`.

This is equivalent to finding `n` such that:
1. `0 ≤ n < 101`,
2. `123456 - n ≡ 0 mod 101`,
3. `101` divides `123456 - n`.

But since `101` divides `123456 - n` is already given, we can directly work with this.

#### Step 1: Compute `123456 mod 101`

First, we need to find `123456 mod 101`. 

We can use the division algorithm to find the remainder:
`101 * 1222 = 123422`
`123456 - 123422 = 34`

Thus, `123456 ≡ 34 mod 101`.

This means that `n ≡ 34 mod 101` is the unique solution to `123456 ≡ n mod 101` under the condition `0 ≤ n < 101`.

But we must also ensure that `101` divides `123456 - n`. Since `123456 ≡ 34 mod 101`, we have `123456 - n ≡ 34 - n mod 101`. 

But `101` divides `123456 - n` is equivalent to `123456 - n ≡ 0 mod 101`, i.e., `34 - n ≡ 0 mod 101`, or `n ≡ 34 mod 101`.

Thus, the condition `101` divides `123456 - n` is redundant and is automatically satisfied if `n ≡ 34 mod 101`.

But we must also ensure that `0 ≤ n < 101`. Since `n ≡ 34 mod 101`, the only possible value is `n = 34` (because `34 ≡ 34 mod 101` and `-67 ≡ 34 mod 101` is not in `[0, 101)`).

Thus, the unique solution is `n = 34`.

#### Step 2: Verification

1. `0 ≤ 34 < 101` is true.
2. `123456 - 34 = 123422` and `101 * 1222 = 123422`, so `101` divides `123456 - 34`.

Thus, `n = 34` is the unique solution.

### Step 3: Abstract Plan

1. **Find `123456 mod 101`**:
   - Compute `101 * 1222 = 123422`.
   - Subtract to get `123456 - 123422 = 34`.
   - Thus, `123456 ≡ 34 mod 101`.

2. **Solve for `n`**:
   - The congruence `123456 ≡ n mod 101` is equivalent to `n ≡ 34 mod 101`.
   - The condition `101` divides `123456 - n` is automatically satisfied for `n ≡ 34 mod 101`.
   - The only `n` in `[0, 101)` satisfying `n ≡ 34 mod 101` is `n = 34`.

3. **Conclusion**:
   - The unique solution is `n = 34`.

### Lean 4 Proof Sketch with `have`

```lean4
theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by
  have h_main : n = 34 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by
  have h_main : n = 34 := by
    have h₂ : n ≤ 100 := by linarith
    interval_cases n <;> norm_num at h₁ ⊢ <;>
    (try omega) <;>
    (try contradiction) <;>
    (try omega)
  exact h_main
