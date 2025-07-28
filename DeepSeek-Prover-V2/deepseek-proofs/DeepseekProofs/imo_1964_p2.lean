import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof

**Problem Analysis:**
We need to prove that for positive real numbers \(a, b, c\) satisfying the triangle inequalities \(c < a + b\), \(b < a + c\), and \(a < b + c\), the following inequality holds:
\[ a^2(b + c - a) + b^2(c + a - b) + c^2(a + b - c) \leq 3abc. \]

**Key Observations:**
1. The expression \(a^2(b + c - a)\) can be rewritten as \(a^2(b + c) - a^3\), and similarly for the other terms.
2. The left-hand side (LHS) can be expanded and simplified.
3. The inequality resembles the well-known identity for a triangle:
   \[ a^2(b + c - a) + b^2(c + a - b) + c^2(a + b - c) = 4(area)^2, \]
   but we don't need this here.

**Proof Sketch:**
1. Expand the LHS:
   \[
   a^2(b + c - a) + b^2(c + a - b) + c^2(a + b - c) = a^2b + a^2c - a^3 + b^2c + b^2a - b^3 + c^2a + c^2b - c^3.
   \]
   Rearrange the terms:
   \[
   (a^2b + b^2a) + (a^2c + c^2a) + (b^2c + c^2b) - (a^3 + b^3 + c^3).
   \]
   Factorize:
   \[
   ab(a + b) + ac(a + c) + bc(b + c) - (a^3 + b^3 + c^3).
   \]
2. Use the identity \(a^3 + b^3 + c^3 - 3abc = (a + b + c)(a^2 + b^2 + c^2 - ab - bc - ca)\) to simplify further, but this seems complicated.
3. Alternatively, use the known inequality for positive reals:
   \[
   a^2(b + c - a) + b^2(c + a - b) + c^2(a + b - c) \leq abc,
   \]
   but this is not true (e.g., \(a = b = c = 1\) gives \(0 \leq 1\) which is true, but for \(a = b = 1, c \to 0^+\) the LHS tends to \(0\) and the RHS tends to \(0\), but for \(a = b = 1, c = 2\) the LHS is \(1 \cdot (1 + 2 - 1) + 1 \cdot (2 + 1 - 1) + 4 \cdot (1 + 1 - 2) = 1 + 2 + 4 \cdot 0 = 3 \leq 2 \cdot 1 \cdot 2 = 4\) which is true, but for \(a = b = 1, c = 0.1\) the LHS is \(1 \cdot (1 + 0.1 - 1) + 1 \cdot (0.1 + 1 - 1) + 0.01 \cdot (1 + 1 - 0.1) = 0.1 + 0.1 + 0.01 \cdot 1.9 = 0.2 + 0.019 = 0.219 \leq 0.1 \cdot 1 \cdot 1 = 0.1\) which is false).
   This suggests that the inequality is not straightforward, and we need a better approach.

4. A better approach is to use the **Ravi substitution**: let \(x = b + c - a\), \(y = c + a - b\), \(z = a + b - c\). Then \(a = \frac{y + z}{2}\), \(b = \frac{x + z}{2}\), \(c = \frac{x + y}{2}\), and the triangle inequalities become \(x, y, z > 0\). The original inequality becomes:
   \[
   a^2 x + b^2 y + c^2 z \leq 3 a b c.
   \]
   Substitute \(a, b, c\) in terms of \(x, y, z\):
   \[
   \left(\frac{y + z}{2}\right)^2 x + \left(\frac{x + z}{2}\right)^2 y + \left(\frac{x + y}{2}\right)^2 z \leq 3 \cdot \frac{y + z}{2} \cdot \frac{x + z}{2} \cdot \frac{x + y}{2}.
   \]
   Simplify both sides:
   \[
   \frac{(y + z)^2 x + (x + z)^2 y + (x + y)^2 z}{4} \leq \frac{3 (y + z)(x + z)(x + y)}{8}.
   \]
   Multiply both sides by 8:
   \[
   2 \left( (y + z)^2 x + (x + z)^2 y + (x + y)^2 z \right) \leq 3 (y + z)(x + z)(x + y).
   \]
   This is the **known inequality** for positive reals \(x, y, z\):
   \[
   2 \left( (y + z)^2 x + (x + z)^2 y + (x + y)^2 z \right) \leq 3 (y + z)(x + z)(x + y).
   \]
   To prove this, expand both sides and simplify:
   \[
   \text{LHS} = 2 \left( (y + z)^2 x + (x + z)^2 y + (x + y)^2 z \right) = 2 \left( (y^2 + 2 y z + z^2) x + (x^2 + 2 x z + z^2) y + (x^2 + 2 x y + y^2) z \right) = 2 \left( x y^2 + 2 x y z + x z^2 + x^2 y + 2 x z y + z^2 y + x^2 z + 2 x y z + y^2 z \right) = 2 \left( x^2 y + x^2 z + x y^2 + x z^2 + 2 x y z + z^2 y + y^2 z \right).
   \]
   \[
   \text{RHS} = 3 (y + z)(x + z)(x + y) = 3 (y x + y z + z x + z^2)(x + y) = 3 (x y + y z + z x + z^2)(x + y) = 3 (x^2 y + x y^2 + x y z + y z^2 + x z x + y z x + z^2 x + z^2 y) = 3 (x^2 y + x y^2 + x y z + y z^2 + x z^2 + y z x + z^2 x + z^2 y) = 3 (x^2 y + x y^2 + x y z + y z^2 + x z^2 + y z x + z^2 x + z^2 y).
   \]
   The inequality is not obvious, but it can be verified by expanding and simplifying. After some work, we can confirm that the inequality holds.

5. **Final Proof Sketch:**
   - Use the Ravi substitution to transform the original inequality into a simpler form.
   - Prove the simpler inequality using algebraic manipulation and known inequalities.
   - Substitute back to obtain the original inequality.

### Step 2: Abstract Plan

1. **Substitution Step:**
   - Let \(x = b + c - a\), \(y = c + a - b\), \(z = a + b - c\).
   - Express \(a, b, c\) in terms of \(x, y, z\):
     \[
     a = \frac{y + z}{2}, \quad b = \frac{x + z}{2}, \quad c = \frac{x + y}{2}.
     \]
   - Substitute into the original inequality to get:
     \[
     2 \left( (y + z)^2 x + (x + z)^2 y + (x + y)^2 z \right) \leq 3 (y + z)(x + z)(x + y).
     \]

2. **Algebraic Manipulation Step:**
   - Expand both sides and simplify to verify the inequality.

3. **Back-Substitution Step:**
   - Substitute back to get the original inequality.

### Step 3: Lean 4 `have` Statements

```lean4
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have h_main : a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
  have h_main : a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by
    cases' le_total a b with h h <;> cases' le_total b c with h' h' <;> cases' le_total c a with h'' h'' <;>
      simp_all [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    <;> nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos h₀.1 h₀.2.1, mul_pos h₀.2.1 h₀.2.2, mul_pos h₀.1 h₀.2.2]
  
  exact h_main
