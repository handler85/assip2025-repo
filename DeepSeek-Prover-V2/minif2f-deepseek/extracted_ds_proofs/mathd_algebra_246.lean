import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We are given a function \( f(x) = a x^4 - b x^2 + x + 5 \) and the condition \( f(-3) = 2 \). We need to find \( f(3) \).

**Approach:**
1. First, compute \( f(-3) \) using the given form of \( f(x) \). This will give us an equation involving \( a \) and \( b \).
2. Then, compute \( f(3) \) using the same form of \( f(x) \).
3. Use the equation from step 1 to eliminate \( a \) or \( b \) from the expression for \( f(3) \).
4. Simplify the resulting expression to find \( f(3) \).

**Detailed Steps:**

1. Compute \( f(-3) \):
   \[
   f(-3) = a (-3)^4 - b (-3)^2 + (-3) + 5 = a \cdot 81 - b \cdot 9 - 3 + 5.
   \]
   Simplifying:
   \[
   f(-3) = 81a - 9b + 2.
   \]
   Given that \( f(-3) = 2 \), we have:
   \[
   81a - 9b + 2 = 2 \implies 81a - 9b = 0 \implies 9a - b = 0 \implies b = 9a.
   \]

2. Compute \( f(3) \):
   \[
   f(3) = a \cdot 3^4 - b \cdot 3^2 + 3 + 5 = a \cdot 81 - b \cdot 9 + 8.
   \]
   Substitute \( b = 9a \):
   \[
   f(3) = 81a - 9 \cdot 9a + 8 = 81a - 81a + 8 = 8.
   \]
   Thus, \( f(3) = 8 \).

### Step-by-Step Abstract Plan

1. **Compute \( f(-3) \) using the given form of \( f(x) \):**
   - Substitute \( x = -3 \) into \( f(x) \).
   - Simplify the expression to get \( 81a - 9b + 2 \).
   - Set this equal to \( 2 \) and solve for \( b \) in terms of \( a \).

2. **Compute \( f(3) \) using the same form of \( f(x) \):**
   - Substitute \( x = 3 \) into \( f(x) \).
   - Simplify the expression using the relationship \( b = 9a \).
   - The result is \( f(3) = 8 \).

### Lean 4 `have` Statements

```lean4
theorem mathd_algebra_246
  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^4 - b * x^2 + x + 5)
  (h₂ : f (-3) = 2) :
  f 3 = 8 := by
  have h_b_in_terms_of_a : b = 9 * a := by sorry
  have h_f3 : f 3 = 8 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_246
  (a b : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^4 - b * x^2 + x + 5)
  (h₂ : f (-3) = 2) :
  f 3 = 8 := by
  have h_b_in_terms_of_a : b = 9 * a := by
    have h₃ : f (-3) = 2 := h₂
    have h₄ : f (-3) = a * (-3)^4 - b * (-3)^2 + (-3) + 5 := by
      rw [h₀]
      <;> ring
    rw [h₄] at h₃
    ring_nf at h₃
    linarith
  
  have h_f3 : f 3 = 8 := by
    have h₃ : f 3 = a * (3 : ℝ)^4 - b * (3 : ℝ)^2 + (3 : ℝ) + 5 := by
      rw [h₀]
      <;> ring
    rw [h₃]
    have h₄ : b = 9 * a := h_b_in_terms_of_a
    rw [h₄]
    norm_num
    <;> ring
    <;> nlinarith
  
  exact h_f3
```