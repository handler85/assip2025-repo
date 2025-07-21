import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We are given two functions:
1. \( f(x) = x + 1 \)
2. \( g(x) = x^2 + 3 \)

We need to compute \( f(g(2)) \) and show that it equals \( 8 \).

**Step 1: Compute \( g(2) \).**
By the definition of \( g \), we have:
\[ g(2) = 2^2 + 3 = 4 + 3 = 7. \]

**Step 2: Compute \( f(g(2)) = f(7) \).**
By the definition of \( f \), we have:
\[ f(7) = 7 + 1 = 8. \]

Thus, \( f(g(2)) = 8 \).

### Step-by-Step Abstract Plan

1. **Compute \( g(2) \):**
   - Substitute \( x = 2 \) into \( g(x) = x^2 + 3 \).
   - Calculate \( 2^2 + 3 = 4 + 3 = 7 \).

2. **Compute \( f(g(2)) = f(7) \):**
   - Substitute \( x = 7 \) into \( f(x) = x + 1 \).
   - Calculate \( 7 + 1 = 8 \).

3. **Conclusion:**
   - The final result is \( f(g(2)) = 8 \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_143
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = x + 1)
  (h₁ : ∀ x, g x = x^2 + 3) :
  f (g 2) = 8 := by
  have h₂ : g 2 = 7 := by sorry
  have h₃ : f (g 2) = 8 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_143
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = x + 1)
  (h₁ : ∀ x, g x = x^2 + 3) :
  f (g 2) = 8 := by
  have h₂ : g 2 = 7 := by
    rw [h₁]
    norm_num
  
  have h₃ : f (g 2) = 8 := by
    rw [h₂]
    have h₄ : f 7 = 8 := by
      rw [h₀]
      <;> norm_num
    simpa [h₀] using h₄
  
  exact h₃
```