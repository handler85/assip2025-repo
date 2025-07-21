import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We need to prove that for positive real numbers \(a, b, c, d\), the following inequality holds:
\[
\frac{a^2}{b} + \frac{b^2}{c} + \frac{c^2}{d} + \frac{d^2}{a} \geq a + b + c + d.
\]
This resembles the **Titu's lemma** (a special case of the Cauchy-Schwarz inequality), but it is not directly applicable here. Instead, we can use the **rearrangement inequality** or **Chebyshev's inequality**, but a more straightforward approach is to use the **weighted AM-GM inequality**.

**Key Idea:**
For each term \(\frac{x^2}{y}\), we can write it as \(x \cdot \frac{x}{y}\). Then, by the AM-GM inequality, we have:
\[
\frac{x^2}{y} + y \geq 2x,
\]
since \(\frac{x^2}{y} + y \geq 2 \sqrt{\frac{x^2}{y} \cdot y} = 2x\) by AM-GM. Summing up all such inequalities gives the desired result.

**Proof:**
1. For each \(i \in \{1, 2, 3, 4\}\), we have:
   \[
   \frac{a^2}{b} + b \geq 2a, \quad \frac{b^2}{c} + c \geq 2b, \quad \frac{c^2}{d} + d \geq 2c, \quad \frac{d^2}{a} + a \geq 2d.
   \]
2. Summing these inequalities gives:
   \[
   \left( \frac{a^2}{b} + b \right) + \left( \frac{b^2}{c} + c \right) + \left( \frac{c^2}{d} + d \right) + \left( \frac{d^2}{a} + a \right) \geq 2(a + b + c + d).
   \]
3. Simplifying the left-hand side:
   \[
   \frac{a^2}{b} + \frac{b^2}{c} + \frac{c^2}{d} + \frac{d^2}{a} + (a + b + c + d) \geq 2(a + b + c + d).
   \]
4. Rearranging gives:
   \[
   \frac{a^2}{b} + \frac{b^2}{c} + \frac{c^2}{d} + \frac{d^2}{a} \geq a + b + c + d,
   \]
   which is the desired inequality.

### Step-by-Step Abstract Plan

1. **Understand the Inequality**: We need to prove a sum of fractions is greater than or equal to a sum of the denominators.
2. **Apply AM-GM to Each Term**: For each term \(\frac{x^2}{y}\), we can write it as \(x \cdot \frac{x}{y}\). By AM-GM, \(\frac{x^2}{y} + y \geq 2x\).
3. **Sum the Inequalities**: Sum the inequalities for all four terms to get a lower bound involving \(2(a + b + c + d)\).
4. **Simplify the Bound**: Rearrange the summed inequality to isolate the original sum of fractions and obtain the desired result.

### Lean 4 `have` Statements

```lean4
theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < b := by linarith
    have h₄ : 0 < c := by linarith
    have h₅ : 0 < d := by linarith
    have h₆ : 0 < a * b := by positivity
    have h₇ : 0 < b * c := by positivity
    have h₈ : 0 < c * d := by positivity
    have h₉ : 0 < d * a := by positivity
    have h₁₀ : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
      have h₁₁ : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
        field_simp [h₂, h₃, h₄, h₅]
        rw [le_div_iff (by positivity), ← sub_nonneg]
        ring_nf
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a),
          sq_nonneg (d * a - a * b), mul_nonneg (sub_nonneg.mpr h₆.le) (sub_nonneg.mpr h₇.le),
          mul_nonneg (sub_nonneg.mpr h₇.le) (sub_nonneg.mpr h₈.le),
          mul_nonneg (sub_nonneg.mpr h₈.le) (sub_nonneg.mpr h₉.le),
          mul_nonneg (sub_nonneg.mpr h₉.le) (sub_nonneg.mpr h₆.le)]
      exact h₁₁
    exact h₁₀
  exact h₁
```