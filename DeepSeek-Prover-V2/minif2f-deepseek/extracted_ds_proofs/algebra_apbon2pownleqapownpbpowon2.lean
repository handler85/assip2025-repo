import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

**Problem Analysis:**
We need to prove that for positive real numbers \(a\) and \(b\) and a positive integer \(n\), the following inequality holds:
\[
\left(\frac{a + b}{2}\right)^n \leq \frac{a^n + b^n}{2}.
\]
This is a form of the **Power Mean Inequality** (or **Chebyshev's sum inequality**), which states that the \(n\)-th power mean of two numbers is at least their arithmetic mean.

**Key Observations:**
1. The function \(f(x) = x^n\) is convex for \(x > 0\) and \(n \geq 1\) (since the second derivative is \(f''(x) = n(n-1)x^{n-2} \geq 0\) for \(n \geq 1\)).
2. By Jensen's inequality for convex functions, for a convex function \(f\) and weights \(w_i\) summing to 1, we have:
   \[
   f\left(\sum w_i x_i\right) \leq \sum w_i f(x_i).
   \]
   Here, \(f(x) = x^n\), \(w_1 = w_2 = \frac{1}{2}\), \(x_1 = a\), and \(x_2 = b\).

**Proof Sketch:**
1. The function \(f(x) = x^n\) is convex for \(x > 0\) and \(n \geq 1\).
2. By Jensen's inequality, for \(w_1 = w_2 = \frac{1}{2}\), we have:
   \[
   f\left(\frac{a + b}{2}\right) \leq \frac{1}{2} f(a) + \frac{1}{2} f(b) = \frac{a^n + b^n}{2}.
   \]
   This is exactly the desired inequality.

### Step 1: Abstract Plan

1. **Convexity of \(x^n\)**:
   - The function \(f(x) = x^n\) is convex for \(x > 0\) and \(n \geq 1\).

2. **Apply Jensen's Inequality**:
   - For the convex function \(f(x) = x^n\) and the points \(a, b > 0\) with weights \(\frac{1}{2}\), we have:
     \[
     f\left(\frac{a + b}{2}\right) \leq \frac{1}{2} f(a) + \frac{1}{2} f(b).
     \]
   - Substitute \(f(x) = x^n\) to get the desired inequality.

### Step 2: Lean 4 `have` Statements

```lean4
theorem algebra_apbon2pownleqapownpbpowon2
  (a b : ℝ)
  (n : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
  have h_main : ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem algebra_apbon2pownleqapownpbpowon2
  (a b : ℝ)
  (n : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
  have h_main : ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < b := by linarith
    have h₄ : 0 < a * b := by positivity
    have h₅ : 0 < a ^ n := by positivity
    have h₆ : 0 < b ^ n := by positivity
    have h₇ : 0 < a ^ n * b ^ n := by positivity
    -- Use the convexity of the function x^n to prove the inequality
    have h₈ : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
      -- Use the fact that the function x^n is convex for x > 0 and n ≥ 1
      have h₉ : ∀ (x y : ℝ), 0 < x → 0 < y → 0 < x * y → ∀ (n : ℕ), 0 < n → ((x + y) / 2) ^ n ≤ (x ^ n + y ^ n) / 2 := by
        intro x y hx hy hxy n hn
        induction' hn with n hn IH
        · -- Base case: n = 1
          norm_num
          <;>
          nlinarith [sq_nonneg (x - y)]
        · -- Inductive step: assume the statement holds for n, prove for n + 1
          simp_all [pow_succ, mul_assoc]
          <;>
          nlinarith [sq_nonneg (x - y), mul_self_nonneg ((x + y) / 2 - x), mul_self_nonneg ((x + y) / 2 - y),
            mul_nonneg hx.le hy.le, mul_nonneg (sq_nonneg (x - y)) hx.le, mul_nonneg (sq_nonneg (x - y)) hy.le]
      exact h₉ a b h₂ h₃ h₄ n h₁
    exact h₈
  exact h_main
```