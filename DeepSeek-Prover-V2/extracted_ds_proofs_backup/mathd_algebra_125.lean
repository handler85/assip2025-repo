import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, let's restate the problem clearly:
1. We have two positive integers `x` and `y` (`x > 0`, `y > 0`).
2. The father's age is `5 * x` and the son's age is `x`.
3. Three years ago, the sum of their ages was `30`.
4. We need to prove that the son's current age is `6`, i.e., `x = 6`.

#### Step 1: Translate the Problem into Equations

1. The father's current age is `5 * x` and the son's current age is `x`.
2. Three years ago:
   - Father's age: `5 * x - 3`
   - Son's age: `x - 3`
3. The sum of their ages three years ago was `30`:
   \[
   (5 * x - 3) + (x - 3) = 30
   \]
4. Simplify the equation:
   \[
   6 * x - 6 = 30
   \]
   \[
   6 * x = 36
   \]
   \[
   x = 6
   \]

#### Step 2: Verify the Solution

Given `x = 6`, we have `y = 5 * x = 30`.

Check the sum of ages three years ago:
- Father's age: `30 - 3 = 27`
- Son's age: `6 - 3 = 3`
- Sum: `27 + 3 = 30` ✔️

#### Step 3: Abstract Plan

1. **Translate the Problem**:
   - The sum of their ages three years ago is `30`.
   - The father's current age is `5 * x` and the son's is `x`.
   - Three years ago, the father's age was `5 * x - 3` and the son's was `x - 3`.

2. **Set Up the Equation**:
   - The sum of their ages three years ago is `(5 * x - 3) + (x - 3) = 30`.

3. **Simplify the Equation**:
   - `6 * x - 6 = 30` → `6 * x = 36` → `x = 6`.

4. **Verify the Solution**:
   - Plug `x = 6` back into the original conditions to ensure correctness.

### Lean 4 Proof Sketch with `have` Statements

```lean4
theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  have h_main : x = 6 := by
    sorry
  sorry
```

### Complete Lean 4 Proof

```lean4
theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by
  have h_main : x = 6 := by
    have h₃ : (x : ℤ) - 3 + (y - 3) = 30 := by
      simpa [add_assoc, add_comm, add_left_comm] using h₂
    have h₄ : y = 5 * x := by omega
    rw [h₄] at h₃
    norm_num at h₃
    ring_nf at h₃
    norm_num at h₃
    have h₅ : x ≤ 36 := by
      by_contra h
      have h₆ : x ≥ 37 := by omega
      have h₇ : (x : ℤ) ≥ 37 := by exact_mod_cast h₆
      nlinarith
    interval_cases x <;> norm_num at h₃ ⊢ <;> omega
  exact h_main
```