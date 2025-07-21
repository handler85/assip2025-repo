import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem Analysis:**
We have two linear equations:
1. \( 3a + 2b = 5 \)
2. \( a + b = 2 \)

We need to find the unique real numbers \( a \) and \( b \) that satisfy both equations.

**Approach:**
We can solve for one variable in terms of the other using the second equation and substitute into the first equation to find the value of the first variable. Then, substitute back to find the second variable.

Alternatively, we can use elimination or matrix methods, but the substitution method is straightforward here.

**Step 1: Solve for \( b \) in terms of \( a \) using the second equation.**
The second equation is:
\[ a + b = 2 \]
Subtract \( a \) from both sides:
\[ b = 2 - a \]

**Step 2: Substitute \( b = 2 - a \) into the first equation.**
The first equation is:
\[ 3a + 2b = 5 \]
Substitute \( b = 2 - a \):
\[ 3a + 2(2 - a) = 5 \]
Simplify the left side:
\[ 3a + 4 - 2a = 5 \]
Combine like terms:
\[ a + 4 = 5 \]
Subtract 4 from both sides:
\[ a = 1 \]

**Step 3: Find \( b \) using \( a = 1 \).**
From \( b = 2 - a \):
\[ b = 2 - 1 = 1 \]

**Conclusion:**
The unique solution is \( a = 1 \) and \( b = 1 \).

### Step 4: Verification

Substitute \( a = 1 \) and \( b = 1 \) back into the original equations:
1. \( 3a + 2b = 3 \cdot 1 + 2 \cdot 1 = 3 + 2 = 5 \) ✔️
2. \( a + b = 1 + 1 = 2 \) ✔️

Both equations are satisfied, so the solution is correct.

### Abstract Plan

1. **Solve for \( b \) in terms of \( a \) using the second equation:**
   - Subtract \( a \) from both sides of \( a + b = 2 \) to get \( b = 2 - a \).

2. **Substitute \( b = 2 - a \) into the first equation and solve for \( a \):**
   - Substitute into \( 3a + 2b = 5 \) to get \( 3a + 2(2 - a) = 5 \).
   - Simplify to \( a + 4 = 5 \), then to \( a = 1 \).

3. **Find \( b \) using \( a = 1 \):**
   - Substitute \( a = 1 \) into \( b = 2 - a \) to get \( b = 1 \).

4. **Verify the solution:**
   - Check that \( a = 1 \) and \( b = 1 \) satisfy both original equations.

### Lean 4 `have` Statements

```lean4
theorem mathd_algebra_513
  (a b : ℝ)
  (h₀ : 3 * a + 2 * b = 5)
  (h₁ : a + b = 2) :
  a = 1 ∧ b = 1 := by
  have h_b : b = 2 - a := by sorry
  have h_a : a = 1 := by sorry
  have h_b_final : b = 1 := by sorry
  have h_final : a = 1 ∧ b = 1 := by sorry
  exact h_final
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_513
  (a b : ℝ)
  (h₀ : 3 * a + 2 * b = 5)
  (h₁ : a + b = 2) :
  a = 1 ∧ b = 1 := by
  have h_b : b = 2 - a := by
    have h₂ : a + b = 2 := h₁
    -- We start with the equation a + b = 2
    have h₃ : b = 2 - a := by linarith
    -- Solving for b, we get b = 2 - a
    exact h₃
  
  have h_a : a = 1 := by
    have h₂ : 3 * a + 2 * b = 5 := h₀
    have h₃ : b = 2 - a := h_b
    rw [h₃] at h₂
    ring_nf at h₂
    linarith
  
  have h_b_final : b = 1 := by
    have h₂ : a = 1 := h_a
    have h₃ : b = 2 - a := h_b
    rw [h₂] at h₃
    linarith
  
  have h_final : a = 1 ∧ b = 1 := by
    exact ⟨h_a, h_b_final⟩
  
  exact h_final
```