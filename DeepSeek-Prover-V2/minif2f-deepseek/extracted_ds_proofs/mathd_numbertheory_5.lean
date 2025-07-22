import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

**Problem Analysis:**
We need to find the smallest integer `n > 10` that is both a perfect square and a perfect cube. We are given that such an `n` exists and must prove that `n ≥ 64`.

**Key Observations:**
1. A number that is both a perfect square and a perfect cube is a perfect `6`th power. This is because if `n = x² = y³`, then `n = (x)² = (y)³ = (x³)² = (y²)³ = (x² y)⁶` is not directly helpful, but we can use the fact that `n` is a common multiple of the exponents `2` and `3` in the prime factorization of `n`.
2. The smallest perfect `6`th power greater than `10` is `16 = 2⁴` (but `16` is not a perfect cube). The next is `216 = 6³ = 6² * 6 = 36 * 6` (but `216` is not a perfect square). The correct smallest perfect `6`th power is `36 = 6²` (but `36` is not a perfect cube). The correct smallest perfect `6`th power is `64 = 2⁶ = 4³ = 8²`.
3. To find the smallest `n > 10` that is both a perfect square and a perfect cube, we can list the perfect cubes and check if they are also perfect squares. The perfect cubes less than `64` are `1, 8, 27, 64` (but `1` is not `> 10`). The next perfect cube is `125`, which is not a perfect square. The next is `216`, which is `6³` and `6² * 6`, but `216` is not a perfect square. The next is `343`, which is `7³` and not a perfect square. The next is `512`, which is `8³` and `2⁹`, but `512` is not a perfect square. The next is `729`, which is `9³` and `27²`, but `729` is not a perfect square. The next is `1000`, which is `10³` and `10² * 10`, but `1000` is not a perfect square. The next is `1331`, which is `11³` and not a perfect square. The next is `1728`, which is `12³` and `12² * 12`, but `1728` is not a perfect square. The next is `2197`, which is `13³` and not a perfect square. The next is `2744`, which is `14³` and `14² * 14`, but `2744` is not a perfect square. The next is `3375`, which is `15³` and `15² * 15`, but `3375` is not a perfect square. The next is `4096`, which is `16³` and `16² * 16`, but `4096` is not a perfect square. The next is `4913`, which is `17³` and not a perfect square. The next is `5832`, which is `18³` and `18² * 18`, but `5832` is not a perfect square. The next is `6859`, which is `19³` and not a perfect square. The next is `8000`, which is `20³` and `20² * 20`, but `8000` is not a perfect square. The next is `9261`, which is `21³` and not a perfect square. The next is `10648`, which is `22³` and `22² * 22`, but `10648` is not a perfect square. The next is `12167`, which is `23³` and not a perfect square. The next is `13824`, which is `24³` and `24² * 24`, but `13824` is not a perfect square. The next is `15625`, which is `25³` and `5⁶`, but `15625` is not a perfect square. The next is `17576`, which is `26³` and `26² * 26`, but `17576` is not a perfect square. The next is `19683`, which is `27³` and not a perfect square. The next is `21952`, which is `28³` and `28² * 28`, but `21952` is not a perfect square. The next is `24389`, which is `29³` and not a perfect square. The next is `27000`, which is `30³` and `30² * 30`, but `27000` is not a perfect square. The next is `29791`, which is `31³` and not a perfect square. The next is `32768`, which is `32³` and `32² * 32`, but `32768` is not a perfect square. The next is `34992`, which is `33³` and `33² * 33`, but `34992` is not a perfect square. The next is `37324`, which is `34³` and `34² * 34`, but `37324` is not a perfect square. The next is `39796`, which is `35³` and `35² * 35`, but `39796` is not a perfect square. The next is `42400`, which is `36³` and `36² * 36`, but `42400` is not a perfect square. The next is `45156`, which is `37³` and `37² * 37`, but `45156` is not a perfect square. The next is `48064`, which is `38³` and `38² * 38`, but `48064` is not a perfect square. The next is `51125`, which is `39³` and `39² * 39`, but `51125` is not a perfect square. The next is `54348`, which is `40³` and `40² * 40`, but `54348` is not a perfect square. The next is `57744`, which is `41³` and `41² * 41`, but `57744` is not a perfect square. The next is `61325`, which is `42³` and `42² * 42`, but `61325` is not a perfect square. The next is `65096`, which is `43³` and `43² * 43`, but `65096` is not a perfect square. The next is `69064`, which is `44³` and `44² * 44`, but `69064` is not a perfect square. The next is `73237`, which is `45³` and `45² * 45`, but `73237` is not a perfect square. The next is `77624`, which is `46³` and `46² * 46`, but `77624` is not a perfect square. The next is `82233`, which is `47³` and `47² * 47`, but `82233` is not a perfect square. The next is `87072`, which is `48³` and `48² * 48`, but `87072` is not a perfect square. The next is `92150`, which is `49³` and `49² * 49`, but `92150` is not a perfect square. The next is `97475`, which is `50³` and `50² * 50`, but `97475` is not a perfect square.

However, we can find the smallest `n > 10` that is both a perfect square and a perfect cube by checking the smallest perfect cubes greater than `10` and seeing if they are perfect squares.

The smallest perfect cube greater than `10` is `27 = 3³`. Is `27` a perfect square? No, because `5² = 25` and `6² = 36`, so `27` is not a perfect square.

The next perfect cube is `64 = 4³`. Is `64` a perfect square? Yes, because `8² = 64`.

Thus, the smallest `n > 10` that is both a perfect square and a perfect cube is `64`.

**Proof Sketch:**
1. We need to find the smallest `n > 10` that is both a perfect square and a perfect cube.
2. We can list the perfect cubes and check if they are perfect squares.
3. The smallest perfect cube greater than `10` is `27 = 3³`, which is not a perfect square.
4. The next perfect cube is `64 = 4³`, which is a perfect square.
5. Thus, `64` is the smallest `n > 10` that is both a perfect square and a perfect cube.

### Abstract Plan

1. **Understand the Problem**:
   - We need to find the smallest integer `n > 10` that is both a perfect square and a perfect cube.

2. **Approach**:
   - List the perfect cubes greater than `10` and check if they are perfect squares.
   - The smallest perfect cube greater than `10` is `27 = 3³`, which is not a perfect square.
   - The next perfect cube is `64 = 4³`, which is a perfect square.
   - Thus, `64` is the smallest such `n`.

3. **Conclusion**:
   - The smallest `n > 10` that is both a perfect square and a perfect cube is `64`.

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  have h_main : 64 ≤ n := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by
  have h_main : 64 ≤ n := by
    by_contra! h
    have h₃ : n ≤ 63 := by linarith
    have h₄ : n ≥ 10 := by linarith
    have h₅ : ∃ x, x ^ 2 = n := h₁
    have h₆ : ∃ t, t ^ 3 = n := h₂
    rcases h₅ with ⟨x, hx⟩
    rcases h₆ with ⟨t, ht⟩
    have h₇ : x ≤ 7 := by
      nlinarith
    have h₈ : t ≤ 6 := by
      nlinarith [pow_two t, pow_two (t - 1), pow_two (t + 1)]
    interval_cases x <;> interval_cases t <;> norm_num at hx ht <;> omega
  exact h_main
