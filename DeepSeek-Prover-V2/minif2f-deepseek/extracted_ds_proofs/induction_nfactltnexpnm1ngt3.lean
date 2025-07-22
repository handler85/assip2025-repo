import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
/- ### Detailed Proof and Analysis

First, recall the problem: for any integer \( n \geq 3 \), we have \( n! < n^{n-1} \).

#### Key Observations:
1. The inequality \( n! < n^{n-1} \) can be rewritten as \( n! < n \cdot n^{n-2} \), which is equivalent to \( n! < n^{n-1} \).
2. For \( n \geq 3 \), \( n^{n-1} \) grows much faster than \( n! \).
3. The inequality can be proven by induction or by using known inequalities.

#### Proof Sketch:
We will use induction on \( n \geq 3 \).

**Base Case (\( n = 3 \)):**
- \( 3! = 6 \).
- \( 3^{3-1} = 3^2 = 9 \).
- Clearly, \( 6 < 9 \).

**Inductive Step:**
Assume that for some \( k \geq 3 \), \( k! < k^{k-1} \). We need to show that \( (k+1)! < (k+1)^{k} \).

First, note that:
\[
(k+1)! = (k+1) \cdot k! < (k+1) \cdot k^{k-1}
\]
We need to show that:
\[
(k+1) \cdot k^{k-1} < (k+1)^k
\]
This simplifies to:
\[
k^{k-1} < (k+1)^{k-1}
\]
Since \( k \geq 3 \), \( k+1 > k \), and thus \( (k+1)^{k-1} > k^{k-1} \). Therefore, the inequality holds.

### Step 1: Abstract Plan

1. **Base Case (\( n = 3 \))**:
   - Compute \( 3! = 6 \) and \( 3^{2} = 9 \).
   - Verify \( 6 < 9 \).

2. **Inductive Step**:
   - Assume \( k! < k^{k-1} \) for some \( k \geq 3 \).
   - Prove \( (k+1)! < (k+1)^{k} \):
     - Expand \( (k+1)! = (k+1) \cdot k! \).
     - Use the inductive hypothesis to get \( (k+1) \cdot k! < (k+1) \cdot k^{k-1} \).
     - Prove \( (k+1) \cdot k^{k-1} < (k+1)^k \):
       - This is equivalent to \( k^{k-1} < (k+1)^{k-1} \), which is true because \( k+1 > k \) and \( k \geq 3 \).

### Step 2: Lean 4 `have` Statements

```lean4
theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  have h_main : ∀ (k : ℕ), 3 ≤ k → k ! < k ^ (k - 1) := by
    sorry
  have h_final : n ! < n ^ (n - 1) := by
    sorry
  exact h_final
```

### Complete Lean 4 Proof

lean4
-/
theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) := by
  have h_main : ∀ (k : ℕ), 3 ≤ k → k ! < k ^ (k - 1) := by
    intro k hk
    induction' hk with k hk IH
    · -- Base case: k = 3
      norm_num [Nat.factorial]
    · -- Inductive step: assume the statement holds for k, prove for k + 1
      cases k with
      | zero => contradiction -- k cannot be zero since hk : 3 ≤ k
      | succ k' =>
        cases k' with
        | zero => contradiction -- k cannot be one since hk : 3 ≤ k
        | succ k'' =>
          simp_all [Nat.factorial, Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
          <;>
            (try omega) <;>
            (try
              {
                nlinarith [pow_pos (by norm_num : (0 : ℕ) < 2) k'', pow_pos (by norm_num : (0 : ℕ) < 2) k'',
                  pow_pos (by norm_num : (0 : ℕ) < 2) (k'' + 1), pow_pos (by norm_num : (0 : ℕ) < 2) (k'' + 1)]
              }) <;>
            (try
              {
                ring_nf at *
                <;>
                  nlinarith [pow_pos (by norm_num : (0 : ℕ) < 2) k'', pow_pos (by norm_num : (0 : ℕ) < 2) k'',
                    pow_pos (by norm_num : (0 : ℕ) < 2) (k'' + 1), pow_pos (by norm_num : (0 : ℕ) < 2) (k'' + 1)]
              })
  have h_final : n ! < n ^ (n - 1) := by
    have h₁ : 3 ≤ n := h₀
    have h₂ : n ! < n ^ (n - 1) := h_main n h₁
    exact h₂
  exact h_final
