import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof

**Problem:** Evaluate \(\left(\frac{i}{2}\right)^2\) and show that it is \(-\frac{1}{4}\).

**Solution:**

1. Recall that \(i^2 = -1\) by the definition of the imaginary unit.
2. Compute \(\left(\frac{i}{2}\right)^2\) using the distributive property of exponents over multiplication:
   \[
   \left(\frac{i}{2}\right)^2 = \frac{i^2}{2^2} = \frac{-1}{4} = -\frac{1}{4}.
   \]

This completes the proof.

### Step-by-Step Abstract Plan

1. **Understand the Problem:**
   - We need to compute the square of the complex number \(\frac{i}{2}\).
   - The result should be \(-\frac{1}{4}\).

2. **Use the Definition of \(i\):**
   - Recall that \(i^2 = -1\).

3. **Apply the Exponent Rule:**
   - The square of a fraction is the square of the numerator divided by the square of the denominator.
   - Thus, \(\left(\frac{i}{2}\right)^2 = \frac{i^2}{2^2} = \frac{-1}{4}\).

4. **Final Result:**
   - The value is \(-\frac{1}{4}\).

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  have h_main : (Complex.I / 2) ^ 2 = -(1 / 4) := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by
  have h_main : (Complex.I / 2) ^ 2 = -(1 / 4) := by
    calc
      (Complex.I / 2) ^ 2 = (Complex.I ^ 2) / 2 ^ 2 := by
        -- Use the property of exponents to separate the powers
        rw [show (Complex.I / 2) ^ 2 = (Complex.I ^ 2) / 2 ^ 2 by ring]
      _ = (-1 : ℂ) / 4 := by
        -- Simplify using the known value of i^2 and the power of 2
        norm_num [Complex.ext_iff, pow_two, Complex.I_mul_I]
        <;>
        simp_all [Complex.ext_iff, pow_two, Complex.I_mul_I]
        <;>
        norm_num
        <;>
        ring_nf
        <;>
        norm_num
      _ = -(1 / 4) := by
        -- Simplify the expression to match the target
        norm_num [Complex.ext_iff, pow_two, Complex.I_mul_I]
        <;>
        simp_all [Complex.ext_iff, pow_two, Complex.I_mul_I]
        <;>
        norm_num
        <;>
        ring_nf
        <;>
        norm_num
  exact h_main
