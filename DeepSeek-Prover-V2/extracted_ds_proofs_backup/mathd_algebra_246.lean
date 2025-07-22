import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We are given a function \( f(x) = a x^4 - b x^2 + x + 5 \) and the condition \( f(-3) = 2 \). We need to find \( f(3) \).

**Approach:**
1. First, compute \( f(-3) \) using the given form of \( f(x) \). This will give us an equation involving \( a \) and \( b \).
2. Simplify the equation to find a relationship between \( a \) and \( b \).
3. Next, compute \( f(3) \) using the same form of \( f(x) \), and substitute the relationship from step 2 to find the value of \( f(3) \).

**Detailed Steps:**

1. Compute \( f(-3) \):
   \[
   f(-3) = a \cdot (-3)^4 - b \cdot (-3)^2 + (-3) + 5 = a \cdot 81 - b \cdot 9 - 3 + 5.
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
   Therefore, \( f(3) = 8 \).

### Step-by-Step Abstract Plan

1. **Compute \( f(-3) \) using the given polynomial form and simplify to find a relationship between \( a \) and \( b \).**
   - Substitute \( x = -3 \) into \( f(x) \).
   - Simplify the expression to \( 81a - 9b + 2 \).
   - Set this equal to \( 2 \) and solve for \( b \) in terms of \( a \).

2. **Compute \( f(3) \) using the same polynomial form and substitute the relationship from step 1.**
   - Substitute \( x = 3 \) into \( f(x) \).
   - Simplify the expression to \( 81a - 9b + 8 \).
   - Substitute \( b = 9a \) and simplify to get \( f(3) = 8 \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h_b_in_terms_of_a : b = 9 * a := by
    sorry
  have h_main : f 3 = 8 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  have h_b_in_terms_of_a : b = 9 * a := by
    have h₃ : f (-3) = 2 := h₂
    have h₄ : f (-3) = a * (-3) ^ 4 - b * (-3) ^ 2 + (-3) + 5 := by
      rw [h₀]
      <;> ring
    rw [h₄] at h₃
    ring_nf at h₃ ⊢
    linarith
  
  have h_main : f 3 = 8 := by
    have h₃ : f 3 = a * (3 : ℝ) ^ 4 - b * (3 : ℝ) ^ 2 + (3 : ℝ) + 5 := by
      rw [h₀]
      <;> ring
    rw [h₃]
    have h₄ : b = 9 * a := h_b_in_terms_of_a
    rw [h₄]
    norm_num
    <;> ring_nf
    <;> nlinarith
  
  exact h_main
```