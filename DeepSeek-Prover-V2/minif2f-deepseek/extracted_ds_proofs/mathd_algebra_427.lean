import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We have three linear equations in three variables \(x, y, z\):
1. \(3x + y = 17\) (Equation A)
2. \(5y + z = 14\) (Equation B)
3. \(3x + 5z = 41\) (Equation C)

We need to find the value of \(x + y + z\) and show that it is \(12\).

**Approach:**
To solve for \(x, y, z\), we can use the given equations to eliminate variables step by step. Here's a systematic way to do it:

1. From Equation A, express \(y\) in terms of \(x\):
   \[ y = 17 - 3x \]

2. Substitute \(y = 17 - 3x\) into Equation B:
   \[ 5(17 - 3x) + z = 14 \]
   Simplify:
   \[ 85 - 15x + z = 14 \]
   \[ z = 14 - 85 + 15x \]
   \[ z = 15x - 71 \]

3. Substitute \(y = 17 - 3x\) and \(z = 15x - 71\) into Equation C:
   \[ 3x + 5(15x - 71) = 41 \]
   Simplify:
   \[ 3x + 75x - 355 = 41 \]
   \[ 78x - 355 = 41 \]
   \[ 78x = 396 \]
   \[ x = \frac{396}{78} = \frac{132}{26} = \frac{66}{13} \]

4. Now, find \(y\) and \(z\):
   \[ y = 17 - 3x = 17 - 3 \cdot \frac{66}{13} = \frac{221 - 198}{13} = \frac{23}{13} \]
   \[ z = 15x - 71 = 15 \cdot \frac{66}{13} - 71 = \frac{990 - 923}{13} = \frac{67}{13} \]

5. Finally, compute \(x + y + z\):
   \[ x + y + z = \frac{66}{13} + \frac{23}{13} + \frac{67}{13} = \frac{156}{13} = 12 \]

**Verification:**
Substitute \(x = \frac{66}{13}\), \(y = \frac{23}{13}\), and \(z = \frac{67}{13}\) back into the original equations to ensure they hold true.

### Step-by-Step Abstract Plan

1. **Express \(y\) in terms of \(x\) using Equation A:**
   - From \(3x + y = 17\), solve for \(y\): \(y = 17 - 3x\).

2. **Substitute \(y\) into Equation B to find \(z\) in terms of \(x\):**
   - Substitute \(y = 17 - 3x\) into \(5y + z = 14\):
     \(5(17 - 3x) + z = 14\) simplifies to \(z = 15x - 71\).

3. **Substitute \(y\) and \(z\) into Equation C to solve for \(x\):**
   - Substitute \(y = 17 - 3x\) and \(z = 15x - 71\) into \(3x + 5z = 41\):
     \(3x + 5(15x - 71) = 41\) simplifies to \(78x = 396\), so \(x = \frac{66}{13}\).

4. **Find \(y\) and \(z\) using the expressions from steps 1 and 2:**
   - Substitute \(x = \frac{66}{13}\) into \(y = 17 - 3x\) to get \(y = \frac{23}{13}\).
   - Substitute \(x = \frac{66}{13}\) into \(z = 15x - 71\) to get \(z = \frac{67}{13}\).

5. **Compute \(x + y + z\):**
   - \(x + y + z = \frac{66}{13} + \frac{23}{13} + \frac{67}{13} = \frac{156}{13} = 12\).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_427
  (x y z : ℝ)
  (h₀ : 3 * x + y = 17)
  (h₁ : 5 * y + z = 14)
  (h₂ : 3 * x + 5 * z = 41) :
  x + y + z = 12 := by
  have h_x : x = 66 / 13 := by sorry
  have h_y : y = 23 / 13 := by sorry
  have h_z : z = 67 / 13 := by sorry
  have h_sum : x + y + z = 12 := by sorry
  exact h_sum
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_427
  (x y z : ℝ)
  (h₀ : 3 * x + y = 17)
  (h₁ : 5 * y + z = 14)
  (h₂ : 3 * x + 5 * z = 41) :
  x + y + z = 12 := by
  have h_x : x = 66 / 13 := by
    -- We need to solve for x using the given equations.
    -- First, we express y in terms of x using the first equation.
    have h₃ : y = 17 - 3 * x := by linarith
    -- Substitute y into the second equation to find z in terms of x.
    have h₄ : z = 15 * x - 71 := by
      subst_vars
      linarith
    -- Substitute y and z into the third equation to solve for x.
    subst_vars
    linarith
  
  have h_y : y = 23 / 13 := by
    have h₃ : y = 17 - 3 * x := by linarith
    rw [h_x] at h₃
    norm_num at h₃ ⊢
    <;> linarith
  
  have h_z : z = 67 / 13 := by
    have h₃ : z = 15 * x - 71 := by
      linarith
    rw [h_x] at h₃
    norm_num at h₃ ⊢
    <;> linarith
  
  have h_sum : x + y + z = 12 := by
    subst_vars
    <;> norm_num
    <;> linarith
  
  exact h_sum
```