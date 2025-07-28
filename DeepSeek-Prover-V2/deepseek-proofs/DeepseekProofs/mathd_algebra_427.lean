import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, we are given three equations:
1. \( 3x + y = 17 \)  (1)
2. \( 5y + z = 14 \)  (2)
3. \( 3x + 5z = 41 \)  (3)

We need to find \( x + y + z \).

#### Step 1: Solve for \( x \) in terms of \( z \) from equation (1)
From equation (1):
\[ 3x + y = 17 \]
We can express \( y \) as:
\[ y = 17 - 3x \]

#### Step 2: Substitute \( y \) into equation (2)
Substitute \( y = 17 - 3x \) into equation (2):
\[ 5(17 - 3x) + z = 14 \]
\[ 85 - 15x + z = 14 \]
\[ -15x + z = 14 - 85 \]
\[ -15x + z = -71 \]
\[ z = 15x - 71 \]

#### Step 3: Substitute \( y \) and \( z \) into equation (3)
Substitute \( y = 17 - 3x \) and \( z = 15x - 71 \) into equation (3):
\[ 3x + 5(15x - 71) = 41 \]
\[ 3x + 75x - 355 = 41 \]
\[ 78x - 355 = 41 \]
\[ 78x = 41 + 355 \]
\[ 78x = 396 \]
\[ x = \frac{396}{78} = \frac{132}{26} = \frac{66}{13} \]

#### Step 4: Find \( y \) and \( z \)
Using \( x = \frac{66}{13} \):
\[ y = 17 - 3x = 17 - 3 \cdot \frac{66}{13} = \frac{221 - 198}{13} = \frac{23}{13} \]
\[ z = 15x - 71 = 15 \cdot \frac{66}{13} - 71 = \frac{990 - 923}{13} = \frac{67}{13} \]

#### Step 5: Find \( x + y + z \)
\[ x + y + z = \frac{66}{13} + \frac{23}{13} + \frac{67}{13} = \frac{156}{13} = 12 \]

### Step-by-Step Abstract Plan

1. **Express \( y \) in terms of \( x \) from the first equation**:
   - \( y = 17 - 3x \).

2. **Substitute \( y \) into the second equation to express \( z \) in terms of \( x \)**:
   - \( z = 15x - 71 \).

3. **Substitute \( y \) and \( z \) into the third equation to solve for \( x \)**:
   - \( x = \frac{66}{13} \).

4. **Find \( y \) and \( z \) using the value of \( x \)**:
   - \( y = \frac{23}{13} \),
   - \( z = \frac{67}{13} \).

5. **Compute \( x + y + z \)**:
   - \( x + y + z = 12 \).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
  have h_x : x = 66 / 13 := by sorry
  have h_y : y = 23 / 13 := by sorry
  have h_z : z = 67 / 13 := by sorry
  have h_sum : x + y + z = 12 := by sorry
  exact h_sum
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 := by
  have h_x : x = 66 / 13 := by
    -- We need to solve for x using the given equations.
    -- First, we use the equations to find a relationship between x and z.
    have h₃ : x = 66 / 13 := by
      -- Use the given equations to solve for x.
      ring_nf at h₀ h₁ h₂ ⊢
      nlinarith [sq_nonneg (x - 66 / 13), sq_nonneg (y - 23 / 13), sq_nonneg (z - 67 / 13)]
    exact h₃
  
  have h_y : y = 23 / 13 := by
    have h₃ : y = 23 / 13 := by
      -- Substitute the value of x into the first equation and solve for y.
      subst_vars
      ring_nf at h₀ h₁ h₂ ⊢
      <;> nlinarith
    exact h₃
  
  have h_z : z = 67 / 13 := by
    have h₃ : z = 67 / 13 := by
      -- Substitute the values of x and y into the second equation and solve for z.
      subst_vars
      ring_nf at h₀ h₁ h₂ ⊢
      <;> nlinarith
    exact h₃
  
  have h_sum : x + y + z = 12 := by
    subst_vars
    <;> norm_num
    <;> linarith
  
  exact h_sum
