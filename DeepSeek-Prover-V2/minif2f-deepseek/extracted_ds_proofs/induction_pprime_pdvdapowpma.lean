import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

**Problem:** Let \( p \) be a prime number and \( a \) a positive integer. Show that \( p \) divides \( a^p - a \).

**Approach:**
We can use Fermat's Little Theorem, which states that for a prime \( p \) and an integer \( a \), \( a^p \equiv a \mod p \). This directly implies that \( p \mid a^p - a \).

Alternatively, we can use the fact that \( a^p - a = a(a^{p-1} - 1) \). If \( p \mid a \), then \( p \mid a^p - a \). If \( p \nmid a \), then \( a \) and \( p \) are coprime, and by Fermat's Little Theorem, \( a^{p-1} \equiv 1 \mod p \), so \( a^{p-1} - 1 \equiv 0 \mod p \), and thus \( p \mid a^p - a \).

However, the first approach is more straightforward for this problem, and we will use it.

**Proof:**
1. By Fermat's Little Theorem, for a prime \( p \) and an integer \( a \), we have \( a^p \equiv a \mod p \).
2. This means that \( p \mid a^p - a \).

**Conclusion:** \( p \mid a^p - a \).

### Step 1: Abstract Plan

1. **Use Fermat's Little Theorem:**
   - For a prime \( p \) and integer \( a \), \( a^p \equiv a \mod p \).
   - This is equivalent to \( p \mid a^p - a \).

2. **Conclude the Proof:**
   - The result follows directly from Fermat's Little Theorem.

### Step 2: Lean 4 `have` Statements

```lean4
theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) : p ∣ a ^ p - a := by
  have h_main : p ∣ a ^ p - a := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) : p ∣ a ^ p - a := by
  have h_main : p ∣ a ^ p - a := by
    haveI := Fact.mk h₁
    simpa using nat_sub_dvd_pow_sub_pow _ a p
  exact h_main
