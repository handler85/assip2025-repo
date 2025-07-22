import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/-
### Detailed Proof and Analysis

First, we need to understand the problem:
We need to prove that the sum of reciprocals of square roots from \( k = 2 \) to \( k = 10000 \) is less than 198. That is:
\[
\sum_{k=2}^{10000} \frac{1}{\sqrt{k}} < 198.
\]

#### Step 1: Estimate the Sum
The sum is a decreasing sequence, so we can bound it from above by an integral. Specifically, for \( k \geq 1 \), we have:
\[
\frac{1}{\sqrt{k}} \leq \frac{1}{\sqrt{k-1}} \quad \text{and} \quad \frac{1}{\sqrt{k}} \leq \frac{1}{\sqrt{k}}.
\]
But a better approach is to use the integral test. The function \( f(x) = \frac{1}{\sqrt{x}} \) is continuous and positive for \( x \geq 1 \), and it is decreasing. The sum can be compared to the integral:
\[
\int_{1}^{10000} \frac{1}{\sqrt{x}} \, dx.
\]

#### Step 2: Compute the Integral
Compute the integral:
\[
\int_{1}^{10000} \frac{1}{\sqrt{x}} \, dx = \int_{1}^{10000} x^{-1/2} \, dx = \left. 2 \sqrt{x} \right|_{1}^{10000} = 2 \sqrt{10000} - 2 \sqrt{1} = 2 \cdot 100 - 2 = 200 - 2 = 198.
\]

#### Step 3: Compare the Sum and the Integral
Since \( f(x) = \frac{1}{\sqrt{x}} \) is decreasing, the sum \( \sum_{k=2}^{10000} \frac{1}{\sqrt{k}} \) is less than the integral \( \int_{1}^{10000} \frac{1}{\sqrt{x}} \, dx \), which is 198. Therefore:
\[
\sum_{k=2}^{10000} \frac{1}{\sqrt{k}} < 198.
\]

### Step 4: Abstract Plan

1. **Understand the Sum**: The sum is a finite sum of reciprocals of square roots from \( k = 2 \) to \( k = 10000 \).

2. **Compare to Integral**: Recognize that the sum can be compared to an integral because the function \( f(x) = \frac{1}{\sqrt{x}} \) is decreasing and continuous.

3. **Compute the Integral**: Compute the integral \( \int_{1}^{10000} \frac{1}{\sqrt{x}} \, dx \) to get 198.

4. **Compare the Sum and Integral**: Since the function is decreasing, the sum is less than the integral, which is 198.

5. **Conclusion**: The sum is less than 198.

### Lean 4 Proof Sketch with `have`

```lean4
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have h_main : (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
  have h_main : (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by
    have h₁ : ∀ n : ℕ, 1 ≤ n → (∑ k in Finset.Icc (2 : ℕ) n, 1 / Real.sqrt k) < 198 := by
      intro n hn
      induction' n with n ih
      · -- Base case: n = 0
        norm_num at hn ⊢
        <;> simp_all [Finset.sum_Icc_succ_top]
        <;> norm_num
        <;> linarith
      · -- Inductive step: assume the statement holds for n, prove for n + 1
        cases n with
        | zero =>
          norm_num at hn ⊢
          <;> simp_all [Finset.sum_Icc_succ_top]
          <;> norm_num
          <;> linarith
        | succ n =>
          simp_all [Finset.sum_Icc_succ_top, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
          <;>
          (try
            {
              norm_num at *
              <;>
              apply lt_of_sub_pos
              <;>
              field_simp at *
              <;>
              ring_nf at *
              <;>
              nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (n + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
                Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity)]
            })
          <;>
          (try
            {
              apply lt_of_sub_pos
              field_simp
              ring_nf
              nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (n + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
                Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity),
                Real.sqrt_nonneg (n + 2), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 2 : ℝ) by positivity)]
            })
          <;>
          (try
            {
              norm_num at *
              <;>
              nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (n + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
                Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity),
                Real.sqrt_nonneg (n + 2), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 2 : ℝ) by positivity)]
            })
    exact h₁ 10000 (by norm_num)
  exact h_main
