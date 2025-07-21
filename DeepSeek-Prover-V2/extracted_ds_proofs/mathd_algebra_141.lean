import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We are given a rectangle with:
1. Area: \( a \cdot b = 180 \),
2. Perimeter: \( 2(a + b) = 54 \),
and we need to find \( a^2 + b^2 \).

First, simplify the perimeter equation:
\[ 2(a + b) = 54 \implies a + b = 27. \]

Next, recall the identity for the sum of squares:
\[ a^2 + b^2 = (a + b)^2 - 2ab. \]

Substitute the known values:
\[ a^2 + b^2 = 27^2 - 2 \cdot 180 = 729 - 360 = 369. \]

This completes the proof.

### Step 1: Abstract Plan

1. **Simplify the Perimeter Equation**:
   - Given \( 2(a + b) = 54 \), divide both sides by 2 to get \( a + b = 27 \).

2. **Use the Sum of Squares Identity**:
   - Recall that \( a^2 + b^2 = (a + b)^2 - 2ab \).

3. **Substitute Known Values**:
   - Substitute \( a + b = 27 \) and \( ab = 180 \) into the identity to get \( a^2 + b^2 = 27^2 - 2 \cdot 180 = 729 - 360 = 369 \).

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_algebra_141
  (a b : ℝ)
  (h₁ : (a * b)=180)
  (h₂ : 2 * (a + b)=54) :
  (a^2 + b^2) = 369 := by
  have h_sum : a + b = 27 := by sorry
  have h_main : a^2 + b^2 = 369 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_141
  (a b : ℝ)
  (h₁ : (a * b)=180)
  (h₂ : 2 * (a + b)=54) :
  (a^2 + b^2) = 369 := by
  have h_sum : a + b = 27 := by
    have h₃ : 2 * (a + b) = 54 := h₂
    -- Divide both sides by 2 to solve for a + b
    linarith
  
  have h_main : a^2 + b^2 = 369 := by
    have h₃ : a^2 + b^2 = (a + b)^2 - 2 * (a * b) := by
      ring
    rw [h₃]
    rw [h_sum]
    rw [h₁]
    <;> norm_num
    <;> linarith
  
  exact h_main
```