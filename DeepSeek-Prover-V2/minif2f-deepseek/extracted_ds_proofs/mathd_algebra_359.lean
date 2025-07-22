import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof

**Problem Analysis:**
We are given an arithmetic sequence-like condition involving the real number `y`:
\[ y + 6 + y = 2 \times 12 \]
This can be simplified to:
\[ 2y + 6 = 24 \]
Our goal is to solve for `y` and show that `y = 9`.

**Step 1: Simplify the Equation**
First, combine the `y` terms and the constant terms on both sides:
\[ 2y + 6 = 24 \]

**Step 2: Isolate the Variable Term**
Subtract 6 from both sides to eliminate the constant term on the left:
\[ 2y = 24 - 6 \]
\[ 2y = 18 \]

**Step 3: Solve for `y`**
Divide both sides by 2 to solve for `y`:
\[ y = \frac{18}{2} \]
\[ y = 9 \]

**Verification:**
Substitute `y = 9` back into the original equation to verify:
\[ y + 6 + y = 2 \times 12 \]
\[ 9 + 6 + 9 = 2 \times 12 \]
\[ 24 = 24 \]
This confirms that `y = 9` is indeed the correct solution.

### Step-by-Step Abstract Plan

1. **Simplify the Equation**:
   - Combine like terms on the left-hand side to get `2y + 6 = 24`.

2. **Isolate the Variable Term**:
   - Subtract 6 from both sides to get `2y = 18`.

3. **Solve for `y`**:
   - Divide both sides by 2 to find `y = 9`.

4. **Verification**:
   - Substitute `y = 9` back into the original equation to ensure correctness.

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_359 (y : ℝ) (h₀ : y + 6 + y = 2 * 12) : y = 9 := by
  have h₁ : 2 * y + 6 = 24 := by sorry
  have h₂ : 2 * y = 18 := by sorry
  have h₃ : y = 9 := by sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_359 (y : ℝ) (h₀ : y + 6 + y = 2 * 12) : y = 9 := by
  have h₁ : 2 * y + 6 = 24 := by
    linarith
  
  have h₂ : 2 * y = 18 := by
    linarith
  
  have h₃ : y = 9 := by
    linarith
  
  exact h₃
