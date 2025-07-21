import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, let's carefully restate the problem and the given conditions:

We have three distinct digits `A`, `B`, `C` (i.e., `1 ≤ A, B, C ≤ 9` and `A ≠ B`, `A ≠ C`, `B ≠ C`) that satisfy the following equations:
1. `A + B = C`
2. `10A + A - B = 2C` (i.e., `11A - B = 2C`)
3. `C * B = 10A + A + A` (i.e., `C * B = 12A`)

We need to prove that `A + B + C = 8`.

#### Step 1: Simplify the first equation `A + B = C`

This is already given, so we can substitute `C = A + B` into the other equations.

#### Step 2: Substitute `C = A + B` into the second equation `11A - B = 2C`

We get:
`11A - B = 2(A + B) = 2A + 2B`

Simplify:
`11A - B = 2A + 2B`
`11A - 2A = 2B + B`
`9A = 3B`
`3A = B`
`B = 3A`

#### Step 3: Substitute `B = 3A` into the third equation `C * B = 12A`

We get:
`(A + B) * B = 12A`
`(A + 3A) * 3A = 12A`
`4A * 3A = 12A`
`12A² = 12A`

Assuming `A ≠ 0` (since `A ≥ 1`), we can divide both sides by `12A`:
`A = 1`

#### Step 4: Find `B` and `C` using `A = 1`

From `B = 3A`, we get:
`B = 3 * 1 = 3`

From `C = A + B`, we get:
`C = 1 + 3 = 4`

#### Step 5: Verify the solution

Check the original equations:
1. `A + B = C` → `1 + 3 = 4` ✔️
2. `11A - B = 2C` → `11*1 - 3 = 2*4` → `11 - 3 = 8` → `8 = 8` ✔️
3. `C * B = 12A` → `4 * 3 = 12 * 1` → `12 = 12` ✔️

All conditions are satisfied, and `A + B + C = 1 + 3 + 4 = 8`.

### Step-by-Step Abstract Plan

1. **Substitute `C = A + B` into the equations**:
   - The first equation `A + B = C` is already given.
   - The second equation becomes `11A - B = 2C = 2(A + B) = 2A + 2B`.
   - Simplify to get `9A = 3B` or `B = 3A`.
   - The third equation becomes `C * B = (A + B) * B = 12A`.

2. **Find `A` and `B` using `B = 3A`**:
   - Substitute `B = 3A` into `C * B = 12A` to get `(A + 3A) * 3A = 12A` or `12A² = 12A`.
   - Simplify to `A² = A` or `A(A - 1) = 0`.
   - Since `A ≥ 1`, `A = 1` is the only solution.
   - Then `B = 3A = 3` and `C = A + B = 4`.

3. **Verify the solution**:
   - Check all original equations with `A = 1`, `B = 3`, `C = 4`.

4. **Conclusion**:
   - The sum `A + B + C = 1 + 3 + 4 = 8`.

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_numbertheory_430
  (a b c : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9)
  (h₁ : 1 ≤ b ∧ b ≤ 9)
  (h₂ : 1 ≤ c ∧ c ≤ 9)
  (h₃ : a ≠ b)
  (h₄ : a ≠ c)
  (h₅ : b ≠ c)
  (h₆ : a + b = c)
  (h₇ : 10 * a + a - b = 2 * c)
  (h₈ : c * b = 10 * a + a + a) :
  a + b + c = 8 := by
  have h_a : a = 1 := by sorry
  have h_b : b = 3 := by sorry
  have h_c : c = 4 := by sorry
  have h_sum : a + b + c = 8 := by sorry
  exact h_sum
```

### Complete Lean 4 Proof

```lean4
theorem mathd_numbertheory_430
  (a b c : ℕ)
  (h₀ : 1 ≤ a ∧ a ≤ 9)
  (h₁ : 1 ≤ b ∧ b ≤ 9)
  (h₂ : 1 ≤ c ∧ c ≤ 9)
  (h₃ : a ≠ b)
  (h₄ : a ≠ c)
  (h₅ : b ≠ c)
  (h₆ : a + b = c)
  (h₇ : 10 * a + a - b = 2 * c)
  (h₈ : c * b = 10 * a + a + a) :
  a + b + c = 8 := by
  have h_a : a = 1 := by
    have h₉ := h₈
    have h₁₀ := h₇
    have h₁₁ := h₆
    have h₁₂ : a ≤ 9 := by linarith
    have h₁₃ : b ≤ 9 := by linarith
    have h₁₄ : c ≤ 9 := by linarith
    interval_cases a <;> interval_cases b <;> omega
  
  have h_b : b = 3 := by
    have h₉ := h₈
    have h₁₀ := h₇
    have h₁₁ := h₆
    have h₁₂ : a = 1 := h_a
    subst_vars
    <;> omega
  
  have h_c : c = 4 := by
    have h₉ := h₆
    have h₁₀ := h₇
    have h₁₁ := h₈
    have h₁₂ : a = 1 := h_a
    have h₁₃ : b = 3 := h_b
    subst_vars at *
    <;> omega
  
  have h_sum : a + b + c = 8 := by
    subst_vars
    <;> norm_num
    <;> linarith
  
  exact h_sum
```