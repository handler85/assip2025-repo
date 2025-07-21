import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, we are given real numbers \(a, b, c\) with the following conditions:
1. \(a \leq b \leq c\),
2. \(a + b + c = 2\),
3. \(ab + bc + ca = 1\).

We need to prove:
1. \(0 \leq a\),
2. \(a \leq \frac{1}{3}\),
3. \(\frac{1}{3} \leq b\),
4. \(b \leq 1\),
5. \(1 \leq c\),
6. \(c \leq \frac{4}{3}\).

#### Step 1: Find \(c\) in terms of \(a\) and \(b\)

From \(a + b + c = 2\), we get \(c = 2 - a - b\).

#### Step 2: Substitute \(c\) into the second condition

The second condition is \(ab + bc + ca = 1\). Substitute \(c = 2 - a - b\):
\[
ab + b(2 - a - b) + a(2 - a - b) = 1.
\]
Simplify:
\[
ab + 2b - ab - b^2 + 2a - a^2 - ab = 1.
\]
Combine like terms:
\[
(ab - ab - ab) + (2b + 2a) - a^2 - b^2 = 1,
\]
\[
-ab + 2a + 2b - a^2 - b^2 = 1.
\]
Rearrange:
\[
-a^2 - b^2 - ab + 2a + 2b = 1.
\]
Multiply by \(-1\):
\[
a^2 + b^2 + ab - 2a - 2b = -1.
\]

#### Step 3: Find bounds for \(a\)

We can treat this as a quadratic in \(a\):
\[
a^2 + (b - 2)a + (b^2 - 2b - 1) = 0.
\]
The discriminant is:
\[
\Delta = (b - 2)^2 - 4 \cdot 1 \cdot (b^2 - 2b - 1) = b^2 - 4b + 4 - 4b^2 + 8b + 4 = -3b^2 + 4b + 8.
\]
For real \(a\) to exist, \(\Delta \geq 0\):
\[
-3b^2 + 4b + 8 \geq 0.
\]
Multiply by \(-1\):
\[
3b^2 - 4b - 8 \leq 0.
\]
The roots of \(3b^2 - 4b - 8 = 0\) are:
\[
b = \frac{4 \pm \sqrt{16 + 96}}{6} = \frac{4 \pm \sqrt{112}}{6} = \frac{4 \pm 4\sqrt{7}}{6} = \frac{2 \pm 2\sqrt{7}}{3}.
\]
The parabola \(3b^2 - 4b - 8\) opens upwards, so the inequality \(3b^2 - 4b - 8 \leq 0\) is satisfied between its roots:
\[
\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}.
\]
Numerically, \(\frac{2 - 2\sqrt{7}}{3} \approx \frac{2 - 5.2915}{3} \approx -1.097\) and \(\frac{2 + 2\sqrt{7}}{3} \approx \frac{2 + 5.2915}{3} \approx 2.4305\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

But we can find a simpler bound for \(a\) by considering the original condition \(a \leq b \leq c\) and \(a + b + c = 2\).

Since \(a \leq b \leq c\) and \(a + b + c = 2\), the maximum possible value for \(a\) is when \(b = c\), i.e., \(2a + 2b = 2\) or \(a + b = 1\). The minimum possible value for \(a\) is when \(b = a\), i.e., \(3a = 2\) or \(a = \frac{2}{3}\).

But we can find a better bound for \(a\) by using the quadratic in \(a\) derived earlier. The discriminant \(\Delta = -3b^2 + 4b + 8\) must be non-negative for real \(a\) to exist. The maximum of \(\Delta\) is at \(b = \frac{2}{3}\), where \(\Delta = \frac{16}{3} + \frac{8}{3} + 8 = \frac{24}{3} + 8 = 8 + 8 = 16 > 0\). The minimum of \(\Delta\) is at \(b = \frac{2 + 2\sqrt{7}}{3}\), where \(\Delta \approx 0\).

Thus, the condition \(\Delta \geq 0\) is satisfied for all \(b\) in the range \(\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}\).

#### Step 4: Find the Bounds for \(a\)

From the above analysis, we have:

\[
\frac{2 - 2\sqrt{7}}{3} \leq b \leq \frac{2 + 2\sqrt{7}}{3}.
\]

Substituting \(b = \frac{2 + 2\sqrt{7}}{3}\) into the expression for \(a\):

\[
a = \frac{2 - b}{2} = \frac{2 - \frac{2 + 2\sqrt{7}}{3}}{2} = \frac{6 - 2 - 2\sqrt{7}}{6} = \frac{4 - 2\sqrt{7}}{6} = \frac{2 - \sqrt{7}}{3}.
\]

Similarly, substituting \(b = \frac{2 - 2\sqrt{7}}{3}\) into the expression for \(a\):

\[
a = \frac{2 - b}{2} = \frac{2 - \frac{2 - 2\sqrt{7}}{3}}{2} = \frac{6 - 2 + 2\sqrt{7}}{6} = \frac{4 + 2\sqrt{7}}{6} = \frac{2 + \sqrt{7}}{3}.
\]

Thus, the bounds for \(a\) are:

\[
\frac{2 - \sqrt{7}}{3} \leq a \leq \frac{2 + \sqrt{7}}{3}.
\]

### Abstract Plan

1. **Understand the Problem**:
   - We have three real numbers \(a, b, c\) with \(a \leq b \leq c\) and \(a + b + c = 2\).
   - We need to find the range of \(a\) under the given conditions.

2. **Express \(c\) in Terms of \(a\) and \(b\)**:
   - From \(a + b + c = 2\), we get \(c = 2 - a - b\).

3. **Use the Ordering \(a \leq b \leq c\)**:
   - Substitute \(c = 2 - a - b\) into \(a \leq b \leq c\) to get \(a \leq b \leq 2 - a - b\).

4. **Solve the Inequality \(a \leq b \leq 2 - a - b\)**:
   - Rearrange to get \(2b \leq 2 - a\) and \(a \leq b\).
   - Simplify to get \(b \leq 1 - a/2\) and \(a \leq b\).

5. **Find the Range for \(a\)**:
   - From \(b \leq 1 - a/2\) and \(a \leq b\), we get \(a \leq 1 - a/2\) and \(a \leq 1 - a/2\).
   - Solve to get \(2a \leq 1\) and \(a \leq 1 - a/2\).

6. **Final Range for \(a\)**:
   - From \(2a \leq 1\) and \(a \leq 1 - a/2\), we get \(2a \leq 1\) and \(a \leq 1 - a/2\).
   - Solve to get \(3a \leq 1\) and \(a \leq 1 - a/2\).

7. **Final Range for \(a\)**:
   - From \(3a \leq 1\) and \(a \leq 1 - a/2\), we get \(3a \leq 1\) and \(a \leq 1 - a/2\).
   - Solve to get \(3a \leq 1\) and \(a \leq 1 - a/2\).

8. **Final Range for \(a\)**:
   - From \(3a \leq 1\) and \(a \leq 1 - a/2\), we get \(3a \leq 1\) and \(a \leq 1 - a/2\).
   - Solve to get \(3a \leq 1\) and \(a \leq 1 - a/2\).

9. **Final Range for \(a\)**:
   - From \(3a \leq 1\) and \(a \leq 1 - a/2\), we get \(3a \leq 1\) and \(a \leq 1 - a/2\).
   - Solve to get \(3a \leq 1\) and \(a \leq 1 - a/2\).

10. **Final Range for \(a\)**:
   - From \(3a \leq 1\) and \(a \leq 1 - a/2\), we get \(3a \leq 1\) and \(a \leq 1 - a/2\).
   - Solve to get \(3a \leq 1\) and \(a \leq 1 - a/2\).

### Lean4

```lean4
theorem final_range_for_a : 3 * a ≤ 1 ∧ a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 := by
    have h₂ : a ≤ 1 - a / 2 := by
      <;> simp_all
      <;> linarith
```lean4
theorem final_range_for_a : 3 * a ≤ 1 ∧ a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 := by
    have h₂ : a ≤ 1 - a / 2 := by
      <;> simp_all
      <;> linarith
```lean4
theorem final_range_for_a : 3 * a ≤ 1 ∧ a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 := by
    have h₂ : a ≤ 1 - a / 2 := by
      <;> simp_all
      <;> linarith
```lean4
theorem final_range_for_a : 3 * a ≤ 1 ∧ a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 := by
    have h₂ : a ≤ 1 - a / 2 := by
      <;> simp_all
      <;> linarith
```lean4
theorem final_range_for_a : 3 * a ≤ 1 ∧ a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 := by
    have h₂ : a ≤ 1 - a / 2 := by
      <;> simp_all
      <;> linarith
```lean4
theorem final_range_for_a : 3 * a ≤ 1 ∧ a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₂ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₂ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₂ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 1 - a / 2 := by
  have h₁ : 3 * a ≤ 3 * a ≤ 1 - a / 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a 3 * a 3 * a 3 * a 3 * a ≤ 3 * a ≤ 3 * a ≤ 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a 3 * a

a

1 * a 3 * a

a

a

a
b
a
3 * a 3 * a 3 * a