import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, we are given two equations:
1. \( n + x = 97 \)  (Equation A)
2. \( n + 5x = 265 \)  (Equation B)

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
Thus:
\[ 97 + 4x = 265 \]

#### Step 3: Solve for \( x \)
Subtract 97 from both sides:
\[ 4x = 265 - 97 \]
\[ 4x = 168 \]
Divide both sides by 4:
\[ x = \frac{168}{4} = 42 \]

#### Step 4: Find \( n \)
Substitute \( x = 42 \) back into \( n = 97 - x \):
\[ n = 97 - 42 = 55 \]

#### Step 5: Find \( n + 2x \)
\[ n + 2x = 55 + 2 \times 42 = 55 + 84 = 139 \]

### Step-by-Step Abstract Plan

1. **Find \( n \) in terms of \( x \) from the first equation**:
   - Subtract \( x \) from both sides of \( n + x = 97 \) to get \( n = 97 - x \).

2. **Substitute \( n \) into the second equation**:
   - Replace \( n \) in \( n + 5x = 265 \) with \( 97 - x \) to get \( 97 - x + 5x = 265 \).

3. **Simplify the equation to find \( x \)**:
   - Combine like terms: \( 97 + 4x = 265 \).
   - Subtract 97 from both sides: \( 4x = 168 \).
   - Divide by 4: \( x = 42 \).

4. **Find \( n \) using \( x = 42 \)**:
   - Substitute \( x = 42 \) into \( n = 97 - x \) to get \( n = 55 \).

5. **Find \( n + 2x \)**:
   - Calculate \( n + 2x = 55 + 2 \times 42 = 139 \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_160
  (n x : ℝ)
  (h₀ : n + x = 97)
  (h₁ : n + 5 * x = 265) :
  n + 2 * x = 139 := by
  have h_x : x = 42 := by sorry
  have h_n : n = 55 := by sorry
  have h_main : n + 2 * x = 139 := by sorry
  exact h_main
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_160
  (n x : ℝ)
  (h₀ : n + x = 97)
  (h₁ : n + 5 * x = 265) :
  n + 2 * x = 139 := by
  have h_x : x = 42 := by
    have h₂ : x = 42 := by
      -- Solve for x using the given equations
      linarith
    exact h₂
  
  have h_n : n = 55 := by
    have h₂ : n = 55 := by
      -- Substitute x = 42 into the first equation to find n
      linarith
    exact h₂
  
  have h_main : n + 2 * x = 139 := by
    rw [h_n, h_x]
    <;> norm_num
    <;> linarith
  
  exact h_main
```