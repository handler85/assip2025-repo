import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, recall the relationship between the greatest common divisor (gcd) and the least common multiple (lcm) of two positive integers \( m \) and \( n \):
\[ \text{gcd}(m, n) \cdot \text{lcm}(m, n) = m \cdot n. \]

Given:
1. \(\text{gcd}(m, n) = 8\),
2. \(\text{lcm}(m, n) = 112\),
3. \(m, n > 0\).

From the relationship, we have:
\[ 8 \cdot 112 = m \cdot n \implies m \cdot n = 896. \]

We need to find the minimum possible value of \( m + n \). 

#### Approach to Minimize \( m + n \)

To minimize \( m + n \), we should consider the pairs \((m, n)\) that are divisors of \( 896 \) and satisfy the gcd condition. 

First, factorize \( 896 \):
\[ 896 = 8 \times 112 = 8 \times 8 \times 14 = 8 \times 2 \times 7 \times 4 = 2^7 \times 7. \]

The positive divisors of \( 896 \) are all numbers of the form \( 2^a \times 7^b \), where \( 0 \leq a \leq 7 \) and \( 0 \leq b \leq 1 \). 

The possible pairs \((m, n)\) (up to ordering) are:
1. \( (8, 112) \),
2. \( (16, 56) \),
3. \( (28, 32) \).

We can verify that these pairs satisfy \( m \cdot n = 896 \) and \( \text{gcd}(m, n) = 8 \):
1. \( \text{gcd}(8, 112) = 8 \),
2. \( \text{gcd}(16, 56) = 8 \),
3. \( \text{gcd}(28, 32) = 4 \). 

The third pair does not satisfy the gcd condition, so we discard it. The other two pairs are:
1. \( (8, 112) \),
2. \( (16, 56) \).

The sum \( m + n \) is:
1. \( 8 + 112 = 120 \),
2. \( 16 + 56 = 72 \).

The minimum sum is \( 72 \), achieved by \( (m, n) = (16, 56) \).

#### Verification

1. \( \text{gcd}(16, 56) = 8 \),
2. \( \text{lcm}(16, 56) = \frac{16 \times 56}{8} = 112 \),
3. \( 16 \times 56 = 896 \).

Thus, the solution is correct.

### Step 1: Abstract Plan

1. **Use the gcd-lcm relationship**:
   - From \( \text{gcd}(m, n) = 8 \) and \( \text{lcm}(m, n) = 112 \), derive \( m \cdot n = 896 \).

2. **Find all pairs \((m, n)\) with \( m \cdot n = 896 \) and \( \text{gcd}(m, n) = 8 \)**:
   - Factorize \( 896 \) and list all possible pairs \((m, n)\).

3. **Check the pairs for the condition \( \text{gcd}(m, n) = 8 \)**:
   - The valid pairs are \((8, 112)\), \((16, 56)\), and \((28, 32)\).
   - The pair \((28, 32)\) does not satisfy \( \text{gcd}(28, 32) = 4 \neq 8 \), so it is invalid.

4. **Compute the sum \( m + n \) for the valid pairs**:
   - \((8, 112) \Rightarrow 8 + 112 = 120\),
   - \((16, 56) \Rightarrow 16 + 56 = 72\),
   - \((28, 32) \Rightarrow 28 + 32 = 60\).

5. **Find the minimum sum**:
   - The minimum sum is \( 72 \), achieved by \((16, 56)\).

### Step 2: Lean 4 `have` Statements

```lean4
theorem mathd_numbertheory_711 (m n : ℕ) (h₀ : 0 < m ∧ 0 < n) (h₁ : Nat.gcd m n = 8)
    (h₂ : Nat.lcm m n = 112) : 72 ≤ m + n := by
  have h_main : 72 ≤ m + n := by
    sorry
  sorry
```

### Complete Lean 4 Proof

lean4
-/
theorem mathd_numbertheory_711 (m n : ℕ) (h₀ : 0 < m ∧ 0 < n) (h₁ : Nat.gcd m n = 8)
    (h₂ : Nat.lcm m n = 112) : 72 ≤ m + n := by
  have h_main : 72 ≤ m + n := by
    have h₃ : m * n = 896 := by
      have h₄ : Nat.gcd m n * Nat.lcm m n = m * n := by
        rw [Nat.gcd_mul_lcm]
      rw [h₁, h₂] at h₄
      norm_num at h₄ ⊢
      <;> nlinarith
    have h₄ : m ∣ 896 := by
      use n
      linarith
    have h₅ : n ∣ 896 := by
      use m
      linarith
    have h₆ : m ≤ 896 := Nat.le_of_dvd (by norm_num) h₄
    have h₇ : n ≤ 896 := Nat.le_of_dvd (by norm_num) h₅
    interval_cases m <;> norm_num at h₁ h₂ h₃ ⊢ <;>
      (try omega) <;>
      (try {
        have h₈ : n ≤ 896 := by omega
        interval_cases n <;> norm_num at h₁ h₂ h₃ ⊢ <;> omega
      }) <;>
      (try {
        omega
      })
    <;>
    omega
  
  exact h_main
