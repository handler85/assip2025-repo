import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We are given a function \( f(x) = c x^3 - 9x + 3 \) and the condition that \( f(2) = 9 \). We need to find the value of \( c \).

**Approach:**
1. Substitute \( x = 2 \) into the expression for \( f(x) \).
2. Simplify the resulting equation to solve for \( c \).

**Detailed Steps:**
1. Substitute \( x = 2 \) into \( f(x) \):
   \[
   f(2) = c \cdot 2^3 - 9 \cdot 2 + 3 = 8c - 18 + 3 = 8c - 15.
   \]
2. Set this equal to \( 9 \):
   \[
   8c - 15 = 9.
   \]
3. Solve for \( c \):
   \[
   8c = 9 + 15 = 24 \implies c = \frac{24}{8} = 3.
   \]

**Verification:**
Substitute \( c = 3 \) back into the original function:
\[
f(x) = 3x^3 - 9x + 3.
\]
Check \( f(2) \):
\[
f(2) = 3 \cdot 8 - 9 \cdot 2 + 3 = 24 - 18 + 3 = 9,
\]
which matches the given condition.

### Step 1: Abstract Plan

1. **Substitute \( x = 2 \) into the function \( f(x) \)**:
   - Compute \( f(2) = c \cdot 2^3 - 9 \cdot 2 + 3 \).

2. **Simplify the expression for \( f(2) \)**:
   - \( f(2) = 8c - 18 + 3 = 8c - 15 \).

3. **Set \( f(2) = 9 \) and solve for \( c \)**:
   - \( 8c - 15 = 9 \).
   - \( 8c = 24 \).
   - \( c = 3 \).

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_algebra_148
  (c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = c * x^3 - 9 * x + 3)
  (h₁ : f 2 = 9) :
  c = 3 := by
  have h₂ : f 2 = 8 * c - 15 := by sorry
  have h₃ : 8 * c - 15 = 9 := by sorry
  have h₄ : c = 3 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_148
  (c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = c * x^3 - 9 * x + 3)
  (h₁ : f 2 = 9) :
  c = 3 := by
  have h₂ : f 2 = 8 * c - 15 := by
    have h₂₁ : f 2 = c * (2 : ℝ) ^ 3 - 9 * (2 : ℝ) + 3 := by
      rw [h₀]
      <;> ring
    rw [h₂₁]
    <;> ring
    <;> norm_num
    <;> linarith
  
  have h₃ : 8 * c - 15 = 9 := by
    linarith
  
  have h₄ : c = 3 := by
    linarith
  
  linarith
```