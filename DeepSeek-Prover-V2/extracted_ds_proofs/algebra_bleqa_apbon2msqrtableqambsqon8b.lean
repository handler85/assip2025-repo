import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We need to prove that for positive real numbers \(a\) and \(b\) with \(b \leq a\), the following inequality holds:
\[
\frac{a + b}{2} - \sqrt{ab} \leq \frac{(a - b)^2}{8b}.
\]
This can be rewritten as:
\[
\frac{a + b}{2} - \sqrt{ab} - \frac{(a - b)^2}{8b} \leq 0.
\]

**Key Observations:**
1. The term \(\frac{a + b}{2}\) is the arithmetic mean of \(a\) and \(b\).
2. The term \(\sqrt{ab}\) is the geometric mean of \(a\) and \(b\).
3. The term \(\frac{(a - b)^2}{8b}\) is a measure of how much \(a\) deviates from \(b\) relative to \(b\).

**Approach:**
We will use the **method of substitution** to simplify the inequality. Let \( t = \frac{a}{b} \). Since \( a > 0 \) and \( b > 0 \), \( t > 0 \). The condition \( b \leq a \) becomes \( t \geq 1 \).

The inequality becomes:
\[
\frac{a + b}{2} - \sqrt{ab} \leq \frac{(a - b)^2}{8b} \implies \frac{b t + b}{2} - \sqrt{b^2 t}}{2} \leq \frac{(b t - b)^2}{8b}.
\]
Simplify further:
\[
\frac{b(t + 1)}{2} - b \sqrt{t} \leq \frac{b^2 (t - 1)^2}{8b} = \frac{b (t - 1)^2}{8}.
\]
Since \( b > 0 \), we can divide both sides by \( b \):
\[
\frac{t + 1}{2} - \sqrt{t} \leq \frac{(t - 1)^2}{8}.
\]
This is the simplified inequality to prove.

**Proof of the Simplified Inequality:**
We need to prove:
\[
\frac{t + 1}{2} - \sqrt{t} \leq \frac{(t - 1)^2}{8}, \quad t \geq 1.
\]
Multiply both sides by 8 (positive, so the inequality direction is preserved):
\[
4(t + 1) - 8 \sqrt{t} \leq (t - 1)^2.
\]
Expand the right side:
\[
4(t + 1) - 8 \sqrt{t} \leq t^2 - 2t + 1.
\]
Simplify:
\[
4t + 4 - 8 \sqrt{t} \leq t^2 - 2t + 1.
\]
Bring all terms to one side:
\[
0 \leq t^2 - 6t + 8 + 8 \sqrt{t} - 4.
\]
Simplify further:
\[
0 \leq t^2 - 6t + 4 + 8 \sqrt{t}.
\]
This is equivalent to:
\[
t^2 - 6t + 4 + 8 \sqrt{t} \geq 0.
\]
We can check that this holds for \( t \geq 1 \). For \( t = 1 \):
\[
1 - 6 + 4 + 8 \cdot 1 = -1 + 4 + 8 = 11 \geq 0.
\]
For \( t > 1 \), the term \( t^2 \) dominates, and the inequality holds.

**Conclusion:**
The original inequality is proven by reducing it to a simpler form and verifying the inequality for \( t \geq 1 \).

### Step-by-Step Abstract Plan

1. **Substitution**:
   - Let \( t = \frac{a}{b} \), so \( t \geq 1 \) because \( b \leq a \).

2. **Simplify the Inequality**:
   - Rewrite the original inequality in terms of \( t \).
   - Multiply through by \( b \) to eliminate denominators.
   - Expand and simplify the resulting inequality.

3. **Verify the Simplified Inequality**:
   - Prove that \( t^2 - 6t + 4 + 8 \sqrt{t} \geq 0 \) for \( t \geq 1 \).
   - Check the boundary case \( t = 1 \).
   - For \( t > 1 \), use the fact that \( t^2 \) dominates.

4. **Conclusion**:
   - The original inequality holds for all \( a, b > 0 \) with \( b \leq a \).

### Lean 4 `have` Statements

```lean4
theorem algebra_bleqa_apbon2msqrtableqambsqon8b
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
  have h_main : (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem algebra_bleqa_apbon2msqrtableqambsqon8b
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
  have h_main : (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
    have h₂ : 0 < b := by linarith
    have h₃ : 0 < a := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : Real.sqrt (a * b) ≥ 0 := Real.sqrt_nonneg _
    have h₆ : (a - b) ^ 2 / (8 * b) ≥ (a + b) / 2 - Real.sqrt (a * b) := by
      rw [ge_iff_le]
      rw [le_div_iff (by positivity)]
      nlinarith [sq_nonneg (a - b - 2 * Real.sqrt (a * b)),
        Real.sq_sqrt (show 0 ≤ a * b by positivity),
        sq_nonneg (a - b),
        sq_nonneg (2 * Real.sqrt (a * b) - (a - b)),
        mul_self_nonneg (a + b - 2 * Real.sqrt (a * b))]
    linarith
  exact h_main
```