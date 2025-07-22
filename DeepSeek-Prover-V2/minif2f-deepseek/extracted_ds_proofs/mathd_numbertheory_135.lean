import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, let's understand the problem:
1. We have `n = 3^17 + 3^10`.
2. `11` divides `n + 1`, i.e., `11 ∣ n + 1`.
3. The digits `A, B, C` (in base 10) are pairwise distinct and form a subset of `{0, ..., 9}`.
4. `A` and `C` are odd.
5. `B` is not divisible by `3`.
6. The base-10 representation of `n` is `[B, A, B, C, C, A, C, B, A]` (i.e., `n = B * 10^8 + A * 10^7 + B * 10^6 + C * 10^5 + C * 10^4 + A * 10^3 + C * 10^2 + B * 10 + A`).
7. We need to prove that `100 * A + 10 * B + C = 129`.

#### Step 1: Compute `n`
First, compute `3^17 + 3^10`:
```
3^10 = 59049
3^17 = 3^10 * 3^7 = 59049 * 2187 = 129140163
n = 129140163 + 59049 = 129199212
```
But wait, this is incorrect! The mistake is in `3^17 = 3^10 * 3^7 = 59049 * 2187 = 129140163`. Actually, `3^7 = 2187`, so `3^17 = 3^10 * 3^7 = 59049 * 2187 = 129140163` is correct. But then `n = 129140163 + 59049 = 129199212` is correct.

But Lean says `n = 3^17 + 3^10` is `n = 3^17 + 3^10 = 129199212`? No, Lean is correct because `3^17 = 129140163` and `3^10 = 59049`, so `3^17 + 3^10 = 129140163 + 59049 = 129199212`.

But wait, the Lean code says `h₀ : n = 3 ^ 17 + 3 ^ 10`, and `3 ^ 17` is `129140163` and `3 ^ 10` is `59049`, so `n = 129140163 + 59049 = 129199212`.

But the Lean code also says `h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]`. 

But `n = 129199212`, and `Nat.digits 10 129199212 = [2, 1, 2, 9, 9, 1, 9, 1, 2]`? 

But Lean says `Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]`, so `B = 2`, `A = 1`, `C = 9`. 

But then `n = 129199212` and `Nat.digits 10 n = [2, 1, 2, 9, 9, 1, 9, 1, 2]` is correct. 

But `h₆` says `Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]`, so `B = 2`, `A = 1`, `C = 9`. 

But then `100 * A + 10 * B + C = 100 * 1 + 10 * 2 + 9 = 100 + 20 + 9 = 129`. 

Thus, the problem is correctly solved, and the answer is `129`.

#### Step 2: Verify the Digits
Given `Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]`, we can deduce:
1. `n` is a 9-digit number because `Nat.digits 10 n` has 9 elements.
2. The first digit is `B` (from the right), the second is `A`, etc.
3. The last digit is `A` (from the right), so the first digit is `B` (from the left).

But `n` is `129199212`, and `Nat.digits 10 129199212 = [2, 1, 2, 9, 9, 1, 9, 1, 2]`. 

This is incorrect because `B` is the first digit from the right, `A` is the second digit from the right, etc. 

But `Nat.digits 10 129199212 = [2, 1, 2, 9, 9, 1, 9, 1, 2]` is correct because `129199212` is `212991912` in base 10. 

Thus, `B = 2`, `A = 1`, `C = 9`. 

#### Step 3: Verify the Hypotheses
1. `11 ∣ n + 1`: `n + 1 = 129199213`, and `129199213 ÷ 11 = 11745383` with remainder `0`, so `11 ∣ 129199213`.
2. `h₂ : [A, B, C].Pairwise (· ≠ ·)`: `A = 1`, `B = 2`, `C = 9`, so `[1, 2, 9].Pairwise (· ≠ ·)` is true.
3. `h₃ : {A, B, C} ⊂ Finset.Icc 0 9`: `{1, 2, 9} ⊂ Finset.Icc 0 9` is true because `0 ≤ 1 ≤ 9`, `0 ≤ 2 ≤ 9`, `0 ≤ 9 ≤ 9`, and `1 ≠ 2`, `1 ≠ 9`, `2 ≠ 9`.
4. `h₄ : Odd A ∧ Odd C`: `A = 1` is odd, `C = 9` is odd.
5. `h₅ : ¬3 ∣ B`: `B = 2`, `3 ∣ 2` is false.
6. `h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]`: `n = 129199212`, `Nat.digits 10 129199212 = [2, 1, 2, 9, 9, 1, 9, 1, 2]`, so `B = 2`, `A = 1`, `C = 9`.

#### Step 4: Conclusion
All hypotheses are satisfied, and the conclusion `100 * A + 10 * B + C = 129` is correct.

### Abstract Plan

1. **Compute `n`**:
   - Calculate `3^17` and `3^10`.
   - Add them to get `n = 129199212`.

2. **Extract digits from `n`**:
   - `Nat.digits 10 n = [2, 1, 2, 9, 9, 1, 9, 1, 2]`.
   - This gives `B = 2`, `A = 1`, `C = 9`.

3. **Verify hypotheses**:
   - Check that all conditions are satisfied.

4. **Calculate the result**:
   - `100 * A + 10 * B + C = 100 * 1 + 10 * 2 + 9 = 129`.

### Lean 4 Proof Sketch with `have`

```lean4
theorem mathd_numbertheory_135 (n A B C : ℕ) (h₀ : n = 3 ^ 17 + 3 ^ 10) (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·)) (h₃ : {A, B, C} ⊂ Finset.Icc 0 9) (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B) (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by
  have h_n : n = 129199212 := by sorry
  have h_digits : B = 2 ∧ A = 1 ∧ C = 9 := by sorry
  have h_main : 100 * A + 10 * B + C = 129 := by sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_numbertheory_135 (n A B C : ℕ) (h₀ : n = 3 ^ 17 + 3 ^ 10) (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·)) (h₃ : {A, B, C} ⊂ Finset.Icc 0 9) (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B) (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by
  have h_n : n = 129199212 := by
    rw [h₀]
    <;> norm_num
    <;> rfl
  
  have h_digits : B = 2 ∧ A = 1 ∧ C = 9 := by
    have h₇ := h₆
    have h₈ := h₇
    have h₉ := h₈
    have h₁₀ := h₉
    simp [h_n] at h₇ h₈ h₉ h₁₀
    <;>
    (try omega) <;>
    (try
      {
        have h₁₁ := h₃
        simp [Finset.subset_iff, Finset.mem_Icc] at h₁₁
        have h₁₂ := h₁₁.1
        have h₁₃ := h₁₁.2
        simp_all (config := {decide := true})
        <;> omega
      }) <;>
    (try
      {
        have h₁₁ := h₂
        simp [List.Pairwise, List.get] at h₁₁
        simp_all (config := {decide := true})
        <;> omega
      }) <;>
    (try
      {
        have h₁₁ := h₄
        simp [Nat.odd_iff_not_even, Nat.even_iff] at h₁₁
        simp_all (config := {decide := true})
        <;> omega
      }) <;>
    (try
      {
        have h₁₁ := h₅
        simp [Nat.dvd_iff_mod_eq_zero] at h₁₁
        simp_all (config := {decide := true})
        <;> omega
      })
    <;>
    aesop
  
  have h_main : 100 * A + 10 * B + C = 129 := by
    rcases h_digits with ⟨rfl, rfl, rfl⟩
    <;> norm_num
    <;> rfl
  
  apply h_main
