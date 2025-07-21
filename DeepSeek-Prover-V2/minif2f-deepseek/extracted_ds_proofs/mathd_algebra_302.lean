import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem:** Evaluate \(\left(\frac{i}{2}\right)^2\) and show that it is \(-\frac{1}{4}\).

**Solution:**

1. Recall that \(i^2 = -1\) by definition of the imaginary unit.
2. Compute \(\left(\frac{i}{2}\right)^2\) using the property of exponents:
   \[
   \left(\frac{i}{2}\right)^2 = \frac{i^2}{4} = \frac{-1}{4} = -\frac{1}{4}.
   \]

This completes the proof.

### Step-by-Step Abstract Plan

1. **Understand the Problem:**
   - We need to compute the square of the complex number \(\frac{i}{2}\) and show that it equals \(-\frac{1}{4}\).

2. **Use the Definition of \(i\):**
   - Recall that \(i^2 = -1\).

3. **Apply the Exponent Rule:**
   - \(\left(\frac{i}{2}\right)^2 = \frac{i^2}{4}\).

4. **Substitute \(i^2\):**
   - \(\frac{i^2}{4} = \frac{-1}{4} = -\frac{1}{4}\).

5. **Conclusion:**
   - The result is \(-\frac{1}{4}\), as required.

### Lean 4 `have` Statements

```lean4
theorem mathd_algebra_302 :
  (Complex.I / 2)^2 = -(1 / 4) := by
  have h_main : (Complex.I / 2)^2 = -(1 / 4) := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_302 :
  (Complex.I / 2)^2 = -(1 / 4) := by
  have h_main : (Complex.I / 2)^2 = -(1 / 4) := by
    calc
      (Complex.I / 2) ^ 2 = (Complex.I ^ 2) / 4 := by
        ring_nf
        <;> simp [pow_two, Complex.ext_iff]
        <;> ring_nf
        <;> norm_num
      _ = (-1 : ℂ) / 4 := by
        rw [Complex.I_sq]
        <;> ring_nf
        <;> simp [Complex.ext_iff]
        <;> norm_num
      _ = -(1 / 4) := by
        ring_nf
        <;> simp [Complex.ext_iff]
        <;> norm_num
  exact h_main
```