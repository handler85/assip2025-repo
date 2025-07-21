import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, recall the following properties of gcd and lcm:
1. For any two positive integers \(a\) and \(b\), we have:
   \[
   \gcd(a, b) \cdot \text{lcm}(a, b) = a \cdot b.
   \]
2. If \(d = \gcd(a, b)\), then \(a = d \cdot a'\) and \(b = d \cdot b'\), where \(\gcd(a', b') = 1\).

**Given:**
- \(n > 0\),
- \(\gcd(n, 40) = 10\),
- \(\text{lcm}(n, 40) = 280\).

**To Prove:** \(n = 70\).

---

#### Step 1: Factorize 40 and 280
First, factorize 40 and 280:
\[
40 = 2^3 \cdot 5, \quad 280 = 2^3 \cdot 5 \cdot 7.
\]

#### Step 2: Express \(n\) in terms of its prime factors
Since \(\gcd(n, 40) = 10 = 2 \cdot 5\), \(n\) must include the factors \(2\) and \(5\) in its prime factorization. Let:
\[
n = 2^a \cdot 5^b \cdot k,
\]
where \(a, b \geq 1\) and \(\gcd(k, 10) = 1\) (i.e., \(k\) is not divisible by \(2\) or \(5\)).

#### Step 3: Use the gcd and lcm conditions
1. \(\gcd(n, 40) = 10\):
   \[
   \gcd(2^a \cdot 5^b \cdot k, 2^3 \cdot 5) = 2 \cdot 5 = 10.
   \]
   This implies:
   - \(a \leq 3\) (since \(2^a\) divides \(10\)),
   - \(b \leq 1\) (since \(5^b\) divides \(10\)),
   - \(k\) is not divisible by \(2\) or \(5\) (i.e., \(\gcd(k, 10) = 1\)).

2. \(\text{lcm}(n, 40) = 280\):
   \[
   \text{lcm}(2^a \cdot 5^b \cdot k, 2^3 \cdot 5) = 2^3 \cdot 5 \cdot 7 = 280.
   \]
   This implies:
   - \(a \geq 3\) (since \(2^3\) divides \(280\)),
   - \(b \geq 1\) (since \(5\) divides \(280\)),
   - \(k\) divides \(7\) (since \(280\) is divisible by \(k\)).

#### Step 4: Determine \(k\) and \(n\)
From the above, we have:
1. \(a \leq 3\) and \(a \geq 3\) implies \(a = 3\).
2. \(b \leq 1\) and \(b \geq 1\) implies \(b = 1\).
3. \(k\) is a divisor of \(7\) and \(\gcd(k, 10) = 1\). The only positive integer \(k\) satisfying this is \(k = 7\) (since \(7\) is prime and does not divide \(10\)).

Thus, \(n = 2^3 \cdot 5^1 \cdot 7 = 8 \cdot 5 \cdot 7 = 280\).

But wait, this contradicts the given \(\text{lcm}(n, 40) = 280\) and our earlier conclusion that \(n = 280\). However, we must have made a mistake in our reasoning.

#### Step 5: Re-examining the lcm condition
The mistake is in the interpretation of the lcm condition. The lcm of \(n\) and \(40\) is \(280\), not \(280\) itself. 

Given that \(n = 280\) is a solution, we can verify:
1. \(\gcd(280, 40) = 40 \neq 10\) (this is incorrect).

But we know that \(n = 70\) is a solution:
1. \(\gcd(70, 40) = 10\),
2. \(\text{lcm}(70, 40) = 280\).

Thus, the correct \(n\) is \(70\).

#### Step 6: Prove \(n = 70\) is the only solution
We can use the fact that:
\[
\gcd(n, 40) \cdot \text{lcm}(n, 40) = n \cdot 40.
\]
Given \(\gcd(n, 40) = 10\) and \(\text{lcm}(n, 40) = 280\), we have:
\[
10 \cdot 280 = n \cdot 40 \implies 2800 = 40n \implies n = 70.
\]

### Step 7: Abstract Plan
1. **Use the gcd-lcm product relation**:
   - \(\gcd(n, 40) \cdot \text{lcm}(n, 40) = n \cdot 40\).
   - Substitute the given values to find \(n\).

2. **Calculate \(n\)**:
   - \(10 \cdot 280 = n \cdot 40\).
   - \(2800 = 40n\).
   - \(n = 70\).

### Lean 4 Proof Sketch with `have`

```lean4
theorem mathd_numbertheory_100
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Nat.gcd n 40 = 10)
  (h₂ : Nat.lcm n 40 = 280) :
  n = 70 := by
  have h_main : n = 70 := by sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_numbertheory_100
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Nat.gcd n 40 = 10)
  (h₂ : Nat.lcm n 40 = 280) :
  n = 70 := by
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