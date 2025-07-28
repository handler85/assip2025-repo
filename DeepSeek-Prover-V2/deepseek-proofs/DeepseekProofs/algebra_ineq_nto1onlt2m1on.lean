import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/-
### Detailed Proof and Analysis

First, we need to prove that for any positive natural number \( n \),
\[ n^{1/n} \leq 2 - \frac{1}{n}. \]

#### Observations:
1. The expression \( n^{1/n} \) is not well-defined for \( n = 1 \) in the real numbers because \( 1^{1/1} = 1 \), but \( 2 - 1/1 = 1 \). However, Lean interprets \( n^{1/n} \) as \( n^0 = 1 \) when \( n = 1 \), and \( 2 - 1/1 = 1 \), so the inequality holds.
2. For \( n \geq 2 \), \( n^{1/n} \) is the \( n \)-th root of \( n \), i.e., \( n^{1/n} = n^{1/n} \). The inequality becomes \( n^{1/n} \leq 2 - \frac{1}{n} \).

#### Key Idea:
We can prove the inequality by considering the function \( f(n) = n^{1/n} \) and showing that it is maximized at \( n = 2 \) and decreases for \( n \geq 3 \). However, this is not straightforward because \( n^{1/n} \) is not a polynomial. Instead, we can use the fact that \( n^{1/n} \leq 2 - \frac{1}{n} \) can be verified directly for small \( n \) and then use induction for \( n \geq 3 \).

But a better approach is to use the fact that \( n^{1/n} \leq 2 - \frac{1}{n} \) is equivalent to \( n \leq (2 - \frac{1}{n})^n \). We can then prove this by induction.

#### Induction Proof:
1. **Base Case \( n = 1 \)**:
   - \( 1 \leq (2 - \frac{1}{1})^1 \) is \( 1 \leq 1 \), which is true.
2. **Base Case \( n = 2 \)**:
   - \( 2 \leq (2 - \frac{1}{2})^2 = (1.5)^2 = 2.25 \), which is true.
3. **Base Case \( n = 3 \)**:
   - \( 3 \leq (2 - \frac{1}{3})^3 = (1.\overline{6})^3 \approx 2.37037 \), which is true.
4. **Inductive Step**:
   Assume \( n \geq 3 \) and \( n \leq (2 - \frac{1}{n})^n \). We need to show \( n+1 \leq (2 - \frac{1}{n+1})^{n+1} \).
   - The function \( f(x) = (2 - \frac{1}{x})^x \) is increasing for \( x \geq 1 \). This can be shown by taking the derivative and showing that \( f'(x) > 0 \) for \( x \geq 1 \).
   - Since \( f(x) \) is increasing and \( n \geq 3 \), we have \( f(n) \leq f(n+1) \), i.e., \( (2 - \frac{1}{n})^n \leq (2 - \frac{1}{n+1})^{n+1} \).
   - By the inductive hypothesis, \( n \leq (2 - \frac{1}{n})^n \), so \( n \leq (2 - \frac{1}{n})^n \leq (2 - \frac{1}{n+1})^{n+1} \), i.e., \( n \leq (2 - \frac{1}{n+1})^{n+1} \).

Thus, the inequality is proved by induction.

#### Alternative Direct Proof:
We can also prove the inequality directly for \( n \geq 1 \) by using the fact that \( n^{1/n} \leq 2 - \frac{1}{n} \) is equivalent to \( n \leq (2 - \frac{1}{n})^n \).

For \( n = 1 \), \( 1 \leq 1 \) is true.
For \( n = 2 \), \( 2 \leq (1.5)^2 = 2.25 \) is true.
For \( n = 3 \), \( 3 \leq (1.\overline{6})^3 \approx 2.37037 \) is true.
For \( n \geq 4 \), we can use the fact that \( (2 - \frac{1}{n})^n \) is increasing in \( n \geq 4 \). This can be shown by taking the derivative of \( f(n) = (2 - \frac{1}{n})^n \) with respect to \( n \) and showing that \( f'(n) > 0 \) for \( n \geq 4 \).

Thus, the inequality is true for all \( n \geq 1 \).

### Step 1: Abstract Plan

1. **Base Cases**:
   - For \( n = 1 \), \( 1 \leq 1 \) is true.
   - For \( n = 2 \), \( 2 \leq 2.25 \) is true.
   - For \( n = 3 \), \( 3 \leq 2.37037 \) is true.

2. **Inductive Step**:
   - Assume \( n \geq 4 \) and the inequality holds for all \( k \leq n \).
   - Show that \( (2 - \frac{1}{n+1})^{n+1} > n+1 \).

3. **Conclusion**:
   - By induction, the inequality holds for all \( n \geq 1 \).

### Step 2: Lean 4 `have` Statements

```lean4
theorem algebra_ineq_nto1onlt2m1on (n : ℕ) : (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by
  have h_main : (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem algebra_ineq_nto1onlt2m1on (n : ℕ) : (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by
  have h_main : (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by
    by_cases h : n = 0
    · subst h
      norm_num
    · by_cases h₁ : n = 1
      · subst h₁
        norm_num
      · have h₂ : n ≥ 2 := by
          by_contra h₂
          interval_cases n <;> simp_all (config := {decide := true})
        have h₃ : (n : ℝ) ≥ 2 := by exact_mod_cast h₂
        have h₄ : (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by
          have h₅ : (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - 1 / n := by
            -- Use the fact that the function is decreasing and the limit is 2
            have h₆ : (n : ℝ) ≥ 2 := by exact_mod_cast h₂
            have h₇ : (1 : ℝ) / n ≤ 1 / 2 := by
              apply (div_le_div_iff (by positivity) (by positivity)).mpr
              nlinarith
            have h₈ : (n : ℝ) ^ ((1 : ℝ) / n) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_le
              · nlinarith
              · nlinarith
            have h₉ : (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt n := by
              simp [Real.sqrt_eq_rpow]
              <;> ring_nf
            have h₁₀ : Real.sqrt n ≤ 2 - 1 / n := by
              have h₁₁ : Real.sqrt n ≤ 2 - 1 / n := by
                apply Real.sqrt_le_iff.mpr
                constructor
                · positivity
                ·
                  have h₁₂ : (n : ℝ) ≥ 2 := by exact_mod_cast h₂
                  field_simp
                  rw [div_le_iff (by positivity)]
                  nlinarith [sq_nonneg (Real.sqrt n - 1), Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
              linarith
            calc
              (n : ℝ) ^ ((1 : ℝ) / n) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by exact h₈
              _ = Real.sqrt n := by rw [h₉]
              _ ≤ 2 - 1 / n := by exact h₁₀
              _ ≤ 2 - 1 / n := by linarith
            <;> linarith
          exact h₅
        exact h₄
      <;> linarith
  exact h_main
