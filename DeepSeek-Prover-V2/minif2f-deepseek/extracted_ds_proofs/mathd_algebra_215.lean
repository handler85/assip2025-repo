import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, we need to find all real numbers \( x \) such that \((x + 3)^2 = 121\). Then, we will sum all such \( x \) and show that the sum is \(-6\).

#### Step 1: Solve \((x + 3)^2 = 121\)

Take the square root of both sides:
\[ x + 3 = \pm 11 \]

This gives two cases:
1. \( x + 3 = 11 \Rightarrow x = 8 \)
2. \( x + 3 = -11 \Rightarrow x = -14 \)

Thus, the solutions are \( x = 8 \) and \( x = -14 \).

#### Step 2: Sum the Solutions

The sum is:
\[ 8 + (-14) = 8 - 14 = -6 \]

#### Step 3: Verify the Lean 4 Hypothesis

The Lean 4 hypothesis is:
\[ S = \{ x \in \mathbb{R} \mid (x + 3)^2 = 121 \} \]

We need to prove that \(\sum_{k \in S} k = -6\).

#### Step 4: Prove the Lean 4 Theorem

1. **Find the Elements of \( S \)**:
   - We have \( S = \{ -14, 8 \} \).

2. **Compute the Sum**:
   - The sum is \(-14 + 8 = -6\).

3. **Formalize the Proof**:
   - We need to show that \( S = \{ -14, 8 \} \) and then compute the sum.

### Step-by-Step Abstract Plan

1. **Find the Elements of \( S \)**:
   - Solve \((x + 3)^2 = 121\) to get \( x = -14 \) and \( x = 8 \).
   - Thus, \( S = \{ -14, 8 \} \).

2. **Compute the Sum**:
   - The sum is \(-14 + 8 = -6\).

3. **Formalize the Proof**:
   - Prove that \( S = \{ -14, 8 \} \) and then compute the sum.

### Lean 4 `have` Statements

```lean4
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    (∑ k in S, k) = -6 := by
  have h₁ : S = { -14, 8 } := by
    sorry
  have h₂ : (∑ k in S, k) = -6 := by
    sorry
  exact h₂
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    (∑ k in S, k) = -6 := by
  have h₁ : S = { -14, 8 } := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton, h₀]
    constructor
    · intro h
      have h₁ : (x + 3) ^ 2 = 121 := by simpa using h
      have h₂ : x + 3 = 11 ∨ x + 3 = -11 := by
        apply or_iff_not_imp_left.mpr
        intro h₃
        apply mul_left_cancel₀ (sub_ne_zero.mpr h₃)
        nlinarith
      cases h₂ with
      | inl h₂ =>
        have h₃ : x = 8 := by linarith
        simp [h₃]
      | inr h₂ =>
        have h₃ : x = -14 := by linarith
        simp [h₃]
    · intro h
      rcases h with (rfl | rfl)
      · -- Case x = 8
        norm_num
      · -- Case x = -14
        norm_num
  
  have h₂ : (∑ k in S, k) = -6 := by
    rw [h₁]
    norm_num
    <;>
    simp [Finset.sum_pair, add_comm]
    <;>
    norm_num
    <;>
    linarith
  
  exact h₂
