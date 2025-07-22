import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, recall the relationship between the greatest common divisor (gcd) and the least common multiple (lcm) of two positive integers \(a\) and \(b\):
\[ \text{gcd}(a, b) \cdot \text{lcm}(a, b) = a \cdot b. \]

Given \(a = n\), \(b = 40\), \(\text{gcd}(n, 40) = 10\), and \(\text{lcm}(n, 40) = 280\), we can substitute these values into the relationship:
\[ 10 \cdot 280 = n \cdot 40. \]

Simplify the left-hand side:
\[ 10 \cdot 280 = 2800. \]
Thus, the equation becomes:
\[ 2800 = n \cdot 40. \]

Solve for \(n\):
\[ n = \frac{2800}{40} = 70. \]

**Verification:**
1. \(\text{gcd}(70, 40) = 10\) is correct because \(70 = 10 \cdot 7\) and \(40 = 10 \cdot 4\).
2. \(\text{lcm}(70, 40) = 280\) is correct because \(70 = 2 \cdot 5 \cdot 7\) and \(40 = 2^3 \cdot 5\), so \(\text{lcm}(70, 40) = 2^3 \cdot 5 \cdot 7 = 280\).

### Step 1: Abstract Plan

1. **Use the gcd-lcm relationship**:
   - We know that \(\text{gcd}(n, 40) \cdot \text{lcm}(n, 40) = n \cdot 40\).
   - Substitute the given values to get \(10 \cdot 280 = n \cdot 40\).

2. **Solve for \(n\)**:
   - Simplify \(10 \cdot 280 = 2800\) to get \(2800 = n \cdot 40\).
   - Divide both sides by 40 to get \(n = 70\).

3. **Verify the solution**:
   - Check that \(\text{gcd}(70, 40) = 10\) and \(\text{lcm}(70, 40) = 280\).

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by
  have h_main : n = 70 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by
  have h_main : n = 70 := by
    have h₃ : n * 40 = 10 * 280 := by
      have h₄ : Nat.gcd n 40 * Nat.lcm n 40 = n * 40 := by
        rw [Nat.gcd_mul_lcm]
      rw [h₁, h₂] at h₄
      norm_num at h₄ ⊢
      <;> linarith
    have h₅ : n ≤ 280 := by
      nlinarith
    interval_cases n <;> norm_num at h₁ h₂ h₃ ⊢ <;> omega
  exact h_main
```