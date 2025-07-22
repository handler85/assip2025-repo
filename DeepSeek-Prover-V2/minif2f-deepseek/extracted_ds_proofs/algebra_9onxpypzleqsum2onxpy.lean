import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/-
### Detailed Proof

**Problem Analysis:**
We need to prove that for any three positive real numbers \(x, y, z\), the following inequality holds:
\[
\frac{9}{x + y + z} \leq \frac{2}{x + y} + \frac{2}{y + z} + \frac{2}{z + x}.
\]
This is a classic inequality that can be approached using the **Titu's lemma** (a special case of Cauchy-Schwarz) or by directly manipulating the denominators.

**Key Observations:**
1. The denominators on the right are symmetric in pairs, but not fully symmetric.
2. The denominators on the left and right are related by the sum of the variables.
3. The inequality is homogeneous, so we can assume \(x + y + z = 1\) or \(x + y + z = 2\) without loss of generality.

**Proof Sketch:**
1. Assume without loss of generality that \(x + y + z = 1\) (by homogeneity). The inequality becomes:
   \[
   9 \leq 2(1 - z) + 2(1 - x) + 2(1 - y) = 6 - 2(x + y + z) = 6 - 2 = 4.
   \]
   This is incorrect, so the assumption is wrong. The correct approach is to assume \(x + y + z = 2\) (or any other positive value).

2. Assume \(x + y + z = 2\). The inequality becomes:
   \[
   \frac{9}{2} \leq \frac{2}{x + y} + \frac{2}{y + z} + \frac{2}{z + x}.
   \]
   Simplifying, we get:
   \[
   \frac{9}{2} \leq 2 \left( \frac{1}{x + y} + \frac{1}{y + z} + \frac{1}{z + x} \right).
   \]
   This is equivalent to:
   \[
   \frac{9}{4} \leq \frac{1}{x + y} + \frac{1}{y + z} + \frac{1}{z + x}.
   \]
   This is a known inequality (see below for a proof).

3. To prove the general case, we can use the **substitution** \(a = x + y\), \(b = y + z\), \(c = z + x\). Then \(a, b, c > 0\) and \(x = \frac{c + a - b}{2}\), \(y = \frac{a + b - c}{2}\), \(z = \frac{b + c - a}{2}\). The condition \(x, y, z > 0\) becomes \(a + b > c\), \(a + c > b\), \(b + c > a\). The inequality to prove becomes:
   \[
   \frac{9}{2(x + y + z)} \leq \frac{1}{x + y} + \frac{1}{y + z} + \frac{1}{z + x}.
   \]
   Substituting \(x + y + z = \frac{a + b + c}{2}\), we get:
   \[
   \frac{9}{a + b + c} \leq \frac{1}{x + y} + \frac{1}{y + z} + \frac{1}{z + x}.
   \]
   This is equivalent to:
   \[
   \frac{9}{a + b + c} \leq \frac{2}{a} + \frac{2}{b} + \frac{2}{c} - 2.
   \]
   This is not obviously true, so the substitution approach is not straightforward.

4. A better approach is to use the **rearrangement inequality**. The denominators \(x + y\), \(y + z\), \(z + x\) are symmetric in pairs, and the numerators are all 2. The sum \(x + y + z\) is fixed. The maximum of the sum of reciprocals is achieved when the denominators are as unequal as possible, i.e., when two of them are equal and the third is as large as possible.

   Assume without loss of generality that \(x \leq y \leq z\). Then the denominators are ordered as \(x + y \leq y + z \leq z + x\). The sum of reciprocals is maximized when the denominators are as unequal as possible, i.e., when \(x + y = y + z = z + x = \frac{2(x + y + z)}{3}\).

   However, this is not possible because \(x + y \leq y + z \leq z + x\) and \(x + y + z\) is fixed. The maximum is achieved when two of the denominators are equal and the third is as large as possible.

   Alternatively, we can use the **method of Lagrange multipliers** to find the maximum of the sum of reciprocals under the constraint \(x + y + z = 2\).

   The maximum is achieved when \(x = y = z = \frac{2}{3}\), and the sum of reciprocals is:
   \[
   3 \cdot \frac{1}{\frac{2}{3} + \frac{2}{3}} = 3 \cdot \frac{1}{\frac{4}{3}} = 3 \cdot \frac{3}{4} = \frac{9}{4}.
   \]
   This is the maximum possible value of the sum of reciprocals under the constraint \(x + y + z = 2\).

   Therefore, the inequality:
   \[
   \frac{9}{4} \leq \frac{1}{x + y} + \frac{1}{y + z} + \frac{1}{z + x}
   \]
   holds for all \(x, y, z > 0\) with \(x + y + z = 2\).

   By homogeneity, the original inequality holds for all \(x, y, z > 0\).

### Step-by-Step Abstract Plan

1. **Understand the Inequality**: We need to prove that the sum of reciprocals of pairwise sums of three positive real numbers is at least \(9/4\) times the reciprocal of their total sum.

2. **Use Symmetry and Homogeneity**: The inequality is symmetric and homogeneous, so we can assume a normalization to simplify the problem. Assume \(x + y + z = 2\) without loss of generality.

3. **Find the Maximum of the Sum of Reciprocals**: The maximum of the sum of reciprocals under the constraint \(x + y + z = 2\) is achieved when \(x = y = z = 2/3\). Calculate the sum of reciprocals in this case to get \(9/4\).

4. **Conclude the Proof**: Since the maximum sum of reciprocals is \(9/4\), the inequality holds for all positive real numbers \(x, y, z\).

### Lean 4 `have` Statements

```lean4
theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h_main : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h_main : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
    have h₁ : 0 < x := h₀.1
    have h₂ : 0 < y := h₀.2.1
    have h₃ : 0 < z := h₀.2.2
    have h₄ : 0 < x * y := mul_pos h₁ h₂
    have h₅ : 0 < y * z := mul_pos h₂ h₃
    have h₆ : 0 < z * x := mul_pos h₃ h₁
    field_simp
    rw [div_le_div_iff (by positivity) (by positivity)]
    ring_nf
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y),
      mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (z - x)),
      mul_nonneg (sq_nonneg (y - z)) (sq_nonneg (x - y)),
      mul_nonneg (sq_nonneg (z - x)) (sq_nonneg (y - z))]

  exact h_main
