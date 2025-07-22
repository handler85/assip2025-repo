import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

**Problem:** Prove that the fraction \(\frac{21n + 4}{14n + 3}\) is irreducible for every natural number \(n > 0\). This is equivalent to proving that \(\gcd(21n + 4, 14n + 3) = 1\) for all \(n \in \mathbb{N}\), \(n > 0\).

**Approach:**
We can use the Euclidean algorithm to compute the GCD of \(21n + 4\) and \(14n + 3\). The Euclidean algorithm repeatedly applies the identity \(\gcd(a, b) = \gcd(b, a \mod b)\) until the GCD is found.

1. Let \(a = 21n + 4\) and \(b = 14n + 3\).
2. Compute \(a \mod b\):
   \[
   a = 21n + 4 = (14n + 3) + (7n + 1).
   \]
   Thus, \(a \mod b = 7n + 1\).
3. Now, \(\gcd(a, b) = \gcd(b, a \mod b) = \gcd(14n + 3, 7n + 1)\).
4. Repeat the process for \(b = 14n + 3\) and \(a' = 7n + 1\):
   \[
   b = 14n + 3 = (7n + 1) \cdot 2 + 1.
   \]
   Thus, \(b \mod a' = 1\).
5. Now, \(\gcd(b, a') = \gcd(7n + 1, 1) = 1\).
6. Therefore, \(\gcd(21n + 4, 14n + 3) = 1\) for all \(n \in \mathbb{N}\), \(n > 0\).

### Step 1: Abstract Plan

1. **Apply the Euclidean Algorithm:**
   - Compute \(21n + 4 \mod (14n + 3)\).
   - Simplify to get \(7n + 1\).
   - Now, \(\gcd(21n + 4, 14n + 3) = \gcd(14n + 3, 7n + 1)\).

2. **Repeat the Process:**
   - Compute \(14n + 3 \mod (7n + 1)\).
   - Simplify to get \(1\).
   - Now, \(\gcd(14n + 3, 7n + 1) = \gcd(7n + 1, 1) = 1\).

3. **Conclusion:**
   - The GCD is \(1\), so the fraction is irreducible.

### Step 2: Lean 4 `have` Statements

```lean4
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h_main : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h_main : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    have h₁ : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
      have h₂ : 21 * n + 4 = 1 * (14 * n + 3) + (7 * n + 1) := by
        ring_nf
        <;> omega
      rw [h₂]
      rw [Nat.gcd_comm]
      <;> simp [Nat.gcd_comm]
      <;> ring_nf
      <;> omega
    rw [h₁]
    have h₃ : Nat.gcd (14 * n + 3) (7 * n + 1) = 1 := by
      have h₄ : 14 * n + 3 = 2 * (7 * n + 1) + 1 := by
        ring_nf
        <;> omega
      rw [h₄]
      simp [Nat.gcd_comm]
      <;> ring_nf
      <;> omega
    rw [h₃]
    <;> simp
  exact h_main
```