import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, recall the problem: for any integer \( n \geq 3 \), we have \( n! < n^{n-1} \).

#### Key Observations:
1. The factorial \( n! \) is the product of all positive integers up to \( n \).
2. The expression \( n^{n-1} \) is \( n \) multiplied by itself \( n-1 \) times.
3. For \( n \geq 3 \), \( n^{n-1} \) grows much faster than \( n! \).

#### Proof Sketch:
We will prove this by induction on \( n \geq 3 \).

**Base Case (\( n = 3 \)):**
- \( 3! = 6 \).
- \( 3^{3-1} = 3^2 = 9 \).
- Clearly, \( 6 < 9 \).

**Inductive Step (\( n \geq 3 \)):**
Assume that \( n! < n^{n-1} \) holds for some \( n \geq 3 \). We need to show that \( (n+1)! < (n+1)^{n} \).

First, note that:
\[
(n+1)! = (n+1) \cdot n! < (n+1) \cdot n^{n-1}.
\]
We need to show that:
\[
(n+1) \cdot n^{n-1} \leq (n+1)^n.
\]
This simplifies to:
\[
n^{n-1} \leq (n+1)^{n-1},
\]
which is true because \( n \leq n+1 \) and the function \( x \mapsto x^{n-1} \) is strictly increasing for \( x > 0 \).

Thus, the inductive step is complete, and the proof is correct.

### Step 1: Abstract Plan

1. **Base Case (\( n = 3 \))**:
   - Compute \( 3! = 6 \).
   - Compute \( 3^{2} = 9 \).
   - Verify \( 6 < 9 \).

2. **Inductive Step (\( n \geq 3 \))**:
   - Assume \( n! < n^{n-1} \) for some \( n \geq 3 \).
   - Show \( (n+1)! = (n+1) \cdot n! < (n+1) \cdot n^{n-1} \).
   - Show \( (n+1) \cdot n^{n-1} \leq (n+1)^n \).
   - Conclude \( (n+1)! < (n+1)^n \).

### Step 2: Lean 4 `have` Statements

```lean4
theorem induction_nfactltnexpnm1ngt3
  (n : ℕ)
  (h₀ : 3 ≤ n) :
  n! < n^(n - 1) := by
  have h_main : n! < n^(n - 1) := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem induction_nfactltnexpnm1ngt3
  (n : ℕ)
  (h₀ : 3 ≤ n) :
  n! < n^(n - 1) := by
  have h_main : n! < n^(n - 1) := by
    have h₁ : ∀ n : ℕ, 3 ≤ n → n! < n ^ (n - 1) := by
      intro n hn
      induction' hn with n hn IH
      · -- Base case: n = 3
        norm_num [Nat.factorial]
      · -- Inductive step: assume the statement holds for n, prove for n + 1
        cases n with
        | zero => contradiction -- n cannot be zero since hn : 3 ≤ n
        | succ n =>
          cases n with
          | zero => contradiction -- n cannot be one since hn : 3 ≤ n
          | succ n =>
            cases n with
            | zero => contradiction -- n cannot be two since hn : 3 ≤ n
            | succ n =>
              simp_all [Nat.factorial, Nat.pow_succ, Nat.mul_assoc]
              -- Use nlinarith to prove the inequality
              <;>
                nlinarith [pow_pos (by norm_num : (0 : ℕ) < 2) n,
                  pow_pos (by norm_num : (0 : ℕ) < 2) (n - 1),
                  Nat.mul_le_mul_left (2 ^ (n - 1)) (by linarith : (1 : ℕ) ≤ 2)]
    exact h₁ n h₀
  exact h_main
```