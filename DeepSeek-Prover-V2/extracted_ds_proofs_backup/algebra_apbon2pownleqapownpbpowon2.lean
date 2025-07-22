import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/-
### Detailed Proof and Analysis

First, we need to prove that for positive real numbers \(a\) and \(b\), and a positive integer \(n\), the following inequality holds:
\[
\left(\frac{a + b}{2}\right)^n \leq \frac{a^n + b^n}{2}.
\]

#### Key Observations:
1. The term \(\left(\frac{a + b}{2}\right)^n\) is the \(n\)-th power of the arithmetic mean of \(a\) and \(b\).
2. The term \(\frac{a^n + b^n}{2}\) is the arithmetic mean of the \(n\)-th powers of \(a\) and \(b\).
3. The inequality resembles the **Power Mean Inequality**, which states that for positive real numbers and \(k \geq l\), the \(k\)-th power mean is greater than or equal to the \(l\)-th power mean. Here, \(k = n\) and \(l = 1\) (since \((\frac{a + b}{2})^n\) is the \(n\)-th power mean and \(\frac{a^n + b^n}{2}\) is the arithmetic mean of the \(n\)-th powers).

However, we can also prove this directly by induction on \(n\).

#### Proof by Induction:

**Base Case (\(n = 1\)):**
\[
\left(\frac{a + b}{2}\right)^1 = \frac{a + b}{2} \leq \frac{a^1 + b^1}{2} = \frac{a + b}{2},
\]
which is trivially true with equality.

**Inductive Step:**
Assume the statement holds for some \(n \geq 1\), i.e.,
\[
\left(\frac{a + b}{2}\right)^n \leq \frac{a^n + b^n}{2}.
\]
We need to show that it holds for \(n + 1\), i.e.,
\[
\left(\frac{a + b}{2}\right)^{n + 1} \leq \frac{a^{n + 1} + b^{n + 1}}{2}.
\]

Starting with the left-hand side:
\[
\left(\frac{a + b}{2}\right)^{n + 1} = \left(\frac{a + b}{2}\right)^n \cdot \frac{a + b}{2}.
\]
By the inductive hypothesis, we have:
\[
\left(\frac{a + b}{2}\right)^n \leq \frac{a^n + b^n}{2}.
\]
Thus:
\[
\left(\frac{a + b}{2}\right)^n \cdot \frac{a + b}{2} \leq \frac{a^n + b^n}{2} \cdot \frac{a + b}{2}.
\]
We now need to show that:
\[
\frac{a^n + b^n}{2} \cdot \frac{a + b}{2} \leq \frac{a^{n + 1} + b^{n + 1}}{2}.
\]
This is equivalent to:
\[
(a^n + b^n)(a + b) \leq 2(a^{n + 1} + b^{n + 1}).
\]
Expanding the left-hand side:
\[
a^{n + 1} + a^n b + b^n a + b^{n + 1} \leq 2a^{n + 1} + 2b^{n + 1}.
\]
Rearranging terms:
\[
a^{n + 1} + a^n b + b^n a + b^{n + 1} - 2a^{n + 1} - 2b^{n + 1} \leq 0,
\]
which simplifies to:
\[
- a^{n + 1} + a^n b + b^n a - b^{n + 1} \leq 0.
\]
This can be rewritten as:
\[
a^n b + b^n a \leq a^{n + 1} + b^{n + 1}.
\]
This is true because \(a, b > 0\) and by the **rearrangement inequality**, the sum \(a^n b + b^n a\) is maximized when \(a\) and \(b\) are ordered in the same way, i.e., when \(a \geq b\) or \(a \leq b\). In either case, the maximum is \(a^{n + 1} + b^{n + 1}\).

Thus, the inductive step is complete, and the inequality holds for all positive integers \(n\).

#### Alternative Direct Proof:

We can also prove the inequality directly by using the **Weighted AM-GM Inequality**.

Consider the numbers \(a\) and \(b\) with weights \(n\) and \(n\). The weighted AM is:
\[
\text{AM} = \frac{n \cdot a + n \cdot b}{n + n} = \frac{n(a + b)}{2n} = \frac{a + b}{2}.
\]
The weighted GM is:
\[
\text{GM} = \left(a^n \cdot b^n\right)^{1/(n + n)} = \left(a^n b^n\right)^{1/(2n)} = \left(a^n b^n\right)^{1/(2n)}.
\]
But this is not directly helpful. Instead, we can use the **Power Mean Inequality** or the **rearrangement inequality** as above.

### Step 1: Abstract Plan

1. **Base Case (\(n = 1\))**:
   - The inequality simplifies to \( \frac{a + b}{2} \leq \frac{a + b}{2} \), which is trivially true.

2. **Inductive Step**:
   - Assume the inequality holds for some \(n \geq 1\), i.e., \( \left( \frac{a + b}{2} \right)^n \leq \frac{a^n + b^n}{2} \).
   - Prove it for \(n + 1\):
     - Multiply both sides of the inductive hypothesis by \( \frac{a + b}{2} \).
     - Use the inequality \( (a^n b + b^n a) \leq (a^{n + 1} + b^{n + 1}) \) to complete the proof.

### Step 2: Lean 4 `have` Statements

```lean4
theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  have h_main : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  have h_main : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
    have h₂ : 0 < a := by linarith
    have h₃ : 0 < b := by linarith
    have h₄ : 0 < a * b := mul_pos h₂ h₃
    have h₅ : 0 < a ^ n := pow_pos h₂ n
    have h₆ : 0 < b ^ n := pow_pos h₃ n
    have h₇ : 0 < a ^ n * b ^ n := mul_pos h₅ h₆
    -- Use the weighted AM-GM inequality to prove the main inequality
    have h₈ : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
      -- Use the weighted AM-GM inequality to prove the main inequality
      have h₉ : ∀ n : ℕ, ∀ a b : ℝ, 0 < a → 0 < b → ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
        intro n a b h₁ h₂
        induction n with
        | zero =>
          norm_num
        | succ n ih =>
          have h₃ : 0 < a * b := mul_pos h₁ h₂
          have h₄ : 0 < a ^ n := pow_pos h₁ n
          have h₅ : 0 < b ^ n := pow_pos h₂ n
          have h₆ : 0 < a ^ n * b ^ n := mul_pos h₄ h₅
          simp_all [pow_succ, mul_assoc, mul_comm, mul_left_comm]
          <;>
            nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ n - b ^ n),
              sq_nonneg (a ^ n + b ^ n), sq_nonneg (a ^ n - a * b), sq_nonneg (b ^ n - a * b)]
      exact h₉ n a b h₂ h₃
    exact h₈
  exact h_main
