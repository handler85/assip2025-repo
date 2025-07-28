import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/-
### Detailed Proof and Analysis

**Problem Analysis:**
We are given a sequence of nonnegative real numbers \(a_0, a_1, \ldots, a_{n-1}\) (indexed from 0 to \(n-1\) in Lean) such that the sum of the first \(n\) terms is \(n\). We need to prove that the product of the first \(n\) terms is at most 1.

**Key Observations:**
1. The arithmetic mean-geometric mean (AM-GM) inequality states that for nonnegative real numbers, the arithmetic mean is at least the geometric mean.
2. The arithmetic mean of the numbers \(a_0, a_1, \ldots, a_{n-1}\) is \(\frac{1}{n} \sum_{i=0}^{n-1} a_i = 1\) (since the sum is \(n\)).
3. By AM-GM, the geometric mean is at most the arithmetic mean, i.e., \(\left( \prod_{i=0}^{n-1} a_i \right)^{1/n} \leq 1\). Raising both sides to the power of \(n\) gives \(\prod_{i=0}^{n-1} a_i \leq 1\).

**Proof Sketch:**
1. The arithmetic mean of the \(a_i\) is 1 because the sum is \(n\) and there are \(n\) terms.
2. By the AM-GM inequality, the geometric mean is at most the arithmetic mean.
3. The geometric mean is \(\left( \prod_{i=0}^{n-1} a_i \right)^{1/n}\), so \(\left( \prod_{i=0}^{n-1} a_i \right)^{1/n} \leq 1\).
4. Raising both sides to the power of \(n\) gives \(\prod_{i=0}^{n-1} a_i \leq 1\).

**Formal Proof Sketch:**
1. The arithmetic mean of the \(a_i\) is 1.
2. The geometric mean is at most the arithmetic mean.
3. The geometric mean is \(\left( \prod_{i=0}^{n-1} a_i \right)^{1/n}\), so \(\left( \prod_{i=0}^{n-1} a_i \right)^{1/n} \leq 1\).
4. Raise both sides to the power of \(n\) to get \(\prod_{i=0}^{n-1} a_i \leq 1\).

### Step 1: Abstract Plan

1. **Arithmetic Mean Calculation**:
   - The sum of the \(a_i\) is \(n\).
   - The number of terms is \(n\).
   - The arithmetic mean is \(\frac{n}{n} = 1\).

2. **Apply AM-GM Inequality**:
   - The geometric mean of the \(a_i\) is at most the arithmetic mean, i.e., \(\left( \prod_{i=0}^{n-1} a_i \right)^{1/n} \leq 1\).

3. **Raise to Power \(n\)**:
   - \(\prod_{i=0}^{n-1} a_i \leq 1^n = 1\).

### Step 2: Lean 4 `have` Statements

```lean4
theorem algebra_amgm_sum1toneqn_prod1tonleq1 (a : ℕ → NNReal) (n : ℕ)
    (h₀ : (∑ x in Finset.range n, a x) = n) : (∏ x in Finset.range n, a x) ≤ 1 := by
  have h_main : (∏ x in Finset.range n, a x) ≤ 1 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem algebra_amgm_sum1toneqn_prod1tonleq1 (a : ℕ → NNReal) (n : ℕ)
    (h₀ : (∑ x in Finset.range n, a x) = n) : (∏ x in Finset.range n, a x) ≤ 1 := by
  have h_main : (∏ x in Finset.range n, a x) ≤ 1 := by
    have h₁ : ∀ x ∈ Finset.range n, a x ≤ 1 := by
      intro x hx
      have h₂ : ∑ i in Finset.range n, a i = n := h₀
      have h₃ : a x ≤ ∑ i in Finset.range n, a i := by
        exact Finset.single_le_sum (fun i _ => by exact zero_le (a i)) hx
      have h₄ : (∑ i in Finset.range n, a i : ℕ) = n := by simp_all
      have h₅ : a x ≤ 1 := by
        simp_all [h₄]
        <;>
        (try omega) <;>
        (try simp_all [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]) <;>
        (try omega)
      exact h₅
    exact
      calc
        (∏ x in Finset.range n, a x) ≤ ∏ x in Finset.range n, (1 : NNReal) := by
          exact Finset.prod_le_prod (fun x _ => by simp [zero_le']) (fun x hx => h₁ x hx)
        _ = 1 := by simp
  exact h_main
