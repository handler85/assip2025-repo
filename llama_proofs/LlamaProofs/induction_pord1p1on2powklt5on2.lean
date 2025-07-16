-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Show that for positive integer $n$, $(\prod_{k=1}^{n} (1 + 1/2^k)) < 5/2$.-/
theorem induction_pord1p1on2powklt5on2 (n : ℕ) (h₀ : 0 < n) :
    ∏ k in Finset.Icc 1 n, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := by


-- Formal statement 
induction n using Nat.strongInductionOn with 
  n IHn 
  { 
    intro n IHn 
    have IHn' : ∀ m, 0 < m → ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := IHn; 
    have IHn'' : ∀ m, 0 < m → ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := IHn'; 
    have IHn''' : ∀ m, 0 < m → ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := IHn''; 
    have IHn'''' : ∀ m, 0 < m → ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := IHn'''; 
    have IHn''''' : ∀ m, 0 < m → ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := IHn''''; 
    have IHn''''' : ∀ m, 0 < m → ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := IHn'''''; 
    have IHn''''' : ∀ m, 0 < m → ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := IHn''''''; 
    have IHn''''' : ∀ m, 0 < m → ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := IHn''''''; 
    have IHn''''' : ∀ m, 0 < m → ∏ k in Finset.Icc 1 m, (1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := IHn''''''; 
    have IHn''''' :