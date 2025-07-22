import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, we are given two equations:
1. \( n + x = 97 \) (Equation A)
2. \( n + 5x = 265 \) (Equation B)

We need to find \( n + 2x \).

#### Step 1: Solve for \( n \) in terms of \( x \) from Equation A
From Equation A:
\[ n + x = 97 \]
Subtract \( x \) from both sides:
\[ n = 97 - x \]

#### Step 2: Substitute \( n = 97 - x \) into Equation B
Substitute \( n = 97 - x \) into Equation B:
\[ (97 - x) + 5x = 265 \]
Simplify the left side:
\[ 97 - x + 5x = 97 + 4x \]
So:
\[ 97 + 4x = 265 \]

#### Step 3: Solve for \( x \)
Subtract 97 from both sides:
\[ 4x = 265 - 97 \]
\[ 4x = 168 \]
Divide both sides by 4:
\[ x = 42 \]

#### Step 4: Find \( n \)
Substitute \( x = 42 \) back into \( n = 97 - x \):
\[ n = 97 - 42 = 55 \]

#### Step 5: Find \( n + 2x \)
\[ n + 2x = 55 + 2 \times 42 = 55 + 84 = 139 \]

### Step-by-Step Abstract Plan

1. **Find \( n \) in terms of \( x \) from the first equation**:
   - Subtract \( x \) from both sides of \( n + x = 97 \) to get \( n = 97 - x \).

2. **Substitute \( n = 97 - x \) into the second equation**:
   - Replace \( n \) in \( n + 5x = 265 \) with \( 97 - x \).
   - Simplify to get \( 97 + 4x = 265 \).

3. **Solve for \( x \)**:
   - Subtract 97 from both sides: \( 4x = 168 \).
   - Divide by 4: \( x = 42 \).

4. **Find \( n \)**:
   - Substitute \( x = 42 \) back into \( n = 97 - x \): \( n = 55 \).

5. **Find \( n + 2x \)**:
   - Calculate \( n + 2x = 55 + 84 = 139 \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by
  have h_n : n = 97 - x := by sorry
  have h_x : x = 42 := by sorry
  have h_n_final : n = 55 := by sorry
  have h_main : n + 2 * x = 139 := by sorry
  exact h_main
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by
  have h_n : n = 97 - x := by
    have h₂ : n = 97 - x := by
      -- Solve for n in terms of x using the first equation
      linarith
    linarith
  
  have h_x : x = 42 := by
    have h₂ : n = 97 - x := h_n
    have h₃ : n + 5 * x = 265 := h₁
    -- Substitute n = 97 - x into the second equation
    rw [h₂] at h₃
    -- Simplify the equation to solve for x
    linarith
  
  have h_n_final : n = 55 := by
    have h₂ : n = 97 - x := h_n
    have h₃ : x = 42 := h_x
    rw [h₃] at h₂
    linarith
  
  have h_main : n + 2 * x = 139 := by
    have h₂ : n = 55 := h_n_final
    have h₃ : x = 42 := h_x
    rw [h₂, h₃]
    <;> norm_num
    <;> linarith
  
  exact h_main
```