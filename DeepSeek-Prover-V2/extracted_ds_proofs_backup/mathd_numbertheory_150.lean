import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, we need to find the smallest positive integer \( n \) such that \( 7 + 30n \) is not a prime number. We are to show that this smallest \( n \) is 6. 

#### Step 1: Understand the condition
The number \( 7 + 30n \) is not a prime if and only if it is divisible by some integer greater than 1 and less than or equal to \( \sqrt{7 + 30n} \). 

However, checking all possible divisors is tedious. Instead, we can find the smallest \( n \) such that \( 7 + 30n \) is not prime by testing small values of \( n \).

#### Step 2: Test small values of \( n \)
We compute \( 7 + 30n \) for small positive integers \( n \):
1. \( n = 1 \): \( 7 + 30 \times 1 = 37 \) (prime)
2. \( n = 2 \): \( 7 + 30 \times 2 = 67 \) (prime)
3. \( n = 3 \): \( 7 + 30 \times 3 = 97 \) (prime)
4. \( n = 4 \): \( 7 + 30 \times 4 = 127 \) (prime)
5. \( n = 5 \): \( 7 + 30 \times 5 = 157 \) (prime)
6. \( n = 6 \): \( 7 + 30 \times 6 = 187 \) (not prime, since \( 187 = 11 \times 17 \))

Thus, the smallest \( n \) for which \( 7 + 30n \) is not a prime is \( n = 6 \).

#### Step 3: Prove that \( n \geq 6 \)
Assume for contradiction that \( n \leq 5 \). Then \( n \) is one of \( 1, 2, 3, 4, 5 \). For each of these \( n \), \( 7 + 30n \) is a prime number, as verified above. This contradicts the assumption that \( 7 + 30n \) is not a prime. Hence, \( n \geq 6 \).

### Step 4: Abstract Plan

1. **Understand the condition**: \( 7 + 30n \) is not a prime if and only if it is divisible by some integer greater than 1 and less than or equal to \( \sqrt{7 + 30n} \).

2. **Test small values of \( n \)**:
   - Compute \( 7 + 30n \) for \( n = 1 \) to \( n = 6 \).
   - Verify that \( 7 + 30n \) is prime for \( n = 1 \) to \( n = 5 \), and not prime for \( n = 6 \).

3. **Prove minimality**:
   - Assume \( n \leq 5 \).
   - For each \( n \leq 5 \), \( 7 + 30n \) is prime, leading to a contradiction.
   - Conclude \( n \geq 6 \).

### Lean 4 Proof Sketch with `have`

```lean4
theorem mathd_numbertheory_150 (n : ℕ) (h₀ : ¬Nat.Prime (7 + 30 * n)) : 6 ≤ n := by
  have h_main : 6 ≤ n := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_numbertheory_150 (n : ℕ) (h₀ : ¬Nat.Prime (7 + 30 * n)) : 6 ≤ n := by
  have h_main : 6 ≤ n := by
    by_contra! h
    have h₁ : n ≤ 5 := by linarith
    have h₂ : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases h₂ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num [Nat.Prime] at h₀ <;>
    (try contradiction) <;>
    (try omega) <;>
    (try linarith)
  exact h_main
```