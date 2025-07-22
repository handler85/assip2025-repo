import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, let's carefully restate the problem and the given conditions.

**Problem Statement:**
We have two classes:
1. Morning class with `m` students. The mean score is `84`.
2. Afternoon class with `a` students. The mean score is `70`.

The ratio of the number of students in the morning class to the number of students in the afternoon class is `3/4`, i.e., `m / a = 3 / 4`.

We need to find the mean score of all students, which is `(84 * m + 70 * a) / (m + a)`.

**Given:**
1. `m` and `a` are positive integers (`0 < m ∧ 0 < a`).
2. `m / a = 3 / 4` (as real numbers).

**To Prove:**
`(84 * m + 70 * a) / (m + a) = 76` (as real numbers).

---

**Proof:**

1. From `m / a = 3 / 4`, we can cross-multiply to get `4 * m = 3 * a`. This is a key relationship between `m` and `a`.

2. Rearrange the equation to express `m` in terms of `a`:
   \[
   4m = 3a \implies m = \frac{3a}{4}.
   \]
   Since `m` is a positive integer, `3a` must be divisible by `4`, and `a` must be even (because `3a` is divisible by `4` only if `a` is even).

3. Substitute `m = (3a)/4` into the expression for the total mean:
   \[
   \frac{84m + 70a}{m + a} = \frac{84 \cdot \frac{3a}{4} + 70a}{\frac{3a}{4} + a}.
   \]
   Simplify the numerator and denominator:
   \[
   \text{Numerator} = 84 \cdot \frac{3a}{4} + 70a = 63a + 70a = 133a,
   \]
   \[
   \text{Denominator} = \frac{3a}{4} + a = \frac{3a + 4a}{4} = \frac{7a}{4}.
   \]
   Thus, the expression becomes:
   \[
   \frac{133a}{7a/4} = \frac{133a \cdot 4}{7a} = \frac{532a}{7a} = 76.
   \]
   The `a` cancels out, and we are left with `76`.

4. Verification:
   - The assumption that `a` is even is correct because `3a` must be divisible by `4` for `m` to be an integer.
   - The final result is `76`, which matches the expected answer.

---

### Step-by-Step Abstract Plan

1. **Understand the Given Information:**
   - We have two classes with `m` and `a` students, respectively.
   - The mean scores are `84` and `70` for `m` and `a` students.
   - The ratio of `m` to `a` is `3/4`, i.e., `m / a = 3 / 4`.

2. **Derive Relationships:**
   - From `m / a = 3 / 4`, we get `4m = 3a` (cross-multiplication).
   - Rearrange to `m = (3a)/4`.

3. **Substitute into the Total Mean Expression:**
   - The total mean is `(84m + 70a)/(m + a)`.
   - Substitute `m = (3a)/4` to get `(84 * (3a)/4 + 70a)/((3a)/4 + a)`.

4. **Simplify the Expression:**
   - Numerator: `84 * (3a)/4 = 63a`, so `63a + 70a = 133a`.
   - Denominator: `(3a)/4 + a = (3a + 4a)/4 = (7a)/4`.
   - Thus, the total mean is `(133a)/(7a/4) = 133a * 4 / 7a = 532a / 7a = 76`.

5. **Conclusion:**
   - The total mean score is `76`, which is the required answer.

---

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by
  have h_main : (84 * ↑m + 70 * ↑a : ℝ) / (↑m + ↑a : ℝ) = 76 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by
  have h_main : (84 * ↑m + 70 * ↑a : ℝ) / (↑m + ↑a : ℝ) = 76 := by
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < m := by linarith
    have h₄ : (m : ℝ) / a = 3 / 4 := by exact_mod_cast h₁
    have h₅ : (m : ℝ) = (3 / 4) * a := by
      have h₅₁ : (m : ℝ) / a = 3 / 4 := h₄
      have h₅₂ : a ≠ 0 := by positivity
      field_simp at h₅₁ ⊢
      <;> nlinarith
    have h₆ : (84 * ↑m + 70 * ↑a : ℝ) / (↑m + ↑a : ℝ) = 76 := by
      have h₆₁ : (m : ℝ) = (3 / 4) * a := h₅
      have h₆₂ : (84 * ↑m + 70 * ↑a : ℝ) / (↑m + ↑a : ℝ) = 76 := by
        field_simp [h₆₁]
        <;> ring_nf
        <;> field_simp [h₂.ne']
        <;> ring_nf
        <;> nlinarith
      exact h₆₂
    exact h₆
  exact h_main
```