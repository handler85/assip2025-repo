import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof

**Problem:** Let \( p \) be a prime number and \( a \) a positive integer. Show that \( p \) divides \( a^p - a \).

**Approach:**
We can use Fermat's Little Theorem, which states that for a prime \( p \) and an integer \( a \), \( a^p \equiv a \mod p \). This directly implies that \( p \mid (a^p - a) \).

However, we can also prove this directly using the binomial theorem and properties of primes.

**Proof:**
1. By Fermat's Little Theorem, since \( p \) is prime and \( a \) is an integer, we have:
   \[ a^p \equiv a \mod p. \]
   This means that \( p \mid (a^p - a) \).

But to avoid relying on Fermat's Little Theorem, we can also prove this directly using the binomial theorem and properties of primes.

2. Alternatively, we can use the fact that \( p \) is prime and the binomial expansion of \( (a^p - a) \).
   - The binomial expansion of \( a^p - a \) is:
     \[ a^p - a = a(a^{p-1} - 1). \]
   - We need to show that \( p \mid a(a^{p-1} - 1) \).
   - Since \( p \) is prime, either \( p \mid a \) or \( p \mid (a^{p-1} - 1) \).
   - If \( p \mid a \), then \( p \mid a(a^{p-1} - 1) \).
   - If \( p \nmid a \), then \( a \) and \( p \) are coprime, and by Fermat's Little Theorem, \( a^{p-1} \equiv 1 \mod p \), so \( a^{p-1} - 1 \equiv 0 \mod p \). Thus, \( p \mid (a^{p-1} - 1) \), and hence \( p \mid a(a^{p-1} - 1) \).

In both cases, we conclude that \( p \mid (a^p - a) \).

### Step 1: Abstract Plan

1. **Understand the Problem**: We need to show that a prime \( p \) divides \( a^p - a \) for any positive integer \( a \).

2. **Approach**:
   - Use Fermat's Little Theorem, which states that for a prime \( p \) and an integer \( a \), \( a^p \equiv a \mod p \).
   - Alternatively, use the binomial expansion to show that \( a^p - a \) is divisible by \( p \).

3. **Detailed Steps**:
   - **Fermat's Little Theorem**: Since \( p \) is prime and \( a \) is an integer, \( a^p \equiv a \mod p \). This directly implies \( p \mid (a^p - a) \).
   - **Binomial Expansion**: Expand \( a^p - a \) as \( a(a^{p-1} - 1) \). Then, since \( p \) is prime, either \( p \mid a \) or \( p \mid (a^{p-1} - 1) \). In either case, \( p \mid (a^p - a) \).

4. **Conclusion**: The proof is complete using either Fermat's Little Theorem or the binomial expansion.

### Step 2: Lean 4 `have` Statements

```lean4
theorem induction_pprime_pdvdapowpma
  (p a : ℕ)
  (h₀ : 0 < a)
  (h₁ : Nat.Prime p) :
  p ∣ (a^p - a) := by
  have h_main : p ∣ (a^p - a) := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem induction_pprime_pdvdapowpma
  (p a : ℕ)
  (h₀ : 0 < a)
  (h₁ : Nat.Prime p) :
  p ∣ (a^p - a) := by
  have h_main : p ∣ (a^p - a) := by
    haveI := Fact.mk h₁
    simp [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    <;>
    norm_num
    <;>
    rfl
  
  exact h_main
```