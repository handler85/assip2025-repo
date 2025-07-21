import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We are given two functions:
1. \( f(x) = 2x - 3 \)
2. \( g(x) = x + 1 \)

We need to find the value of \( g(f(5) - 1) \).

**Step 1: Compute \( f(5) \).**
\[ f(5) = 2 \cdot 5 - 3 = 10 - 3 = 7 \]

**Step 2: Compute \( f(5) - 1 \).**
\[ f(5) - 1 = 7 - 1 = 6 \]

**Step 3: Compute \( g(f(5) - 1) \).**
\[ g(6) = 6 + 1 = 7 \]

Thus, the final answer is \( 7 \).

### Step-by-Step Abstract Plan

1. **Compute \( f(5) \):**
   - Substitute \( x = 5 \) into \( f(x) = 2x - 3 \).
   - Calculate \( f(5) = 2 \cdot 5 - 3 = 7 \).

2. **Compute \( f(5) - 1 \):**
   - Subtract 1 from the result of \( f(5) \).
   - Calculate \( f(5) - 1 = 7 - 1 = 6 \).

3. **Compute \( g(f(5) - 1) \):**
   - Substitute \( x = 6 \) into \( g(x) = x + 1 \).
   - Calculate \( g(6) = 6 + 1 = 7 \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_346
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = 2 * x - 3)
  (h₁ : ∀ x, g x = x + 1) :
  g (f 5 - 1) = 7 := by
  have h₂ : f 5 = 7 := by sorry
  have h₃ : f 5 - 1 = 6 := by sorry
  have h₄ : g (f 5 - 1) = 7 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_346
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = 2 * x - 3)
  (h₁ : ∀ x, g x = x + 1) :
  g (f 5 - 1) = 7 := by
  have h₂ : f 5 = 7 := by
    have h₂₁ : f 5 = 2 * (5 : ℝ) - 3 := by rw [h₀]
    rw [h₂₁]
    norm_num
    <;> linarith
  
  have h₃ : f 5 - 1 = 6 := by
    have h₃₁ : f 5 = 7 := h₂
    rw [h₃₁]
    <;> norm_num
    <;> linarith
  
  have h₄ : g (f 5 - 1) = 7 := by
    have h₄₁ : f 5 - 1 = 6 := h₃
    have h₄₂ : g (f 5 - 1) = g 6 := by rw [h₄₁]
    rw [h₄₂]
    have h₄₃ : g 6 = 6 + 1 := by
      have h₄₄ : g 6 = 6 + 1 := by
        simp [h₁]
        <;> norm_num
      exact h₄₄
    rw [h₄₃]
    <;> norm_num
  
  exact h₄
```