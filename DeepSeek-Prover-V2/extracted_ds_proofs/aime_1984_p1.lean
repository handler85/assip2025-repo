import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem aime_1984_p1
  (u : ℕ → ℚ)
  (h₀ : ∀ n, u (n + 1) = u n + 1)
  (h₁ : ∑ k in Finset.range 98, u k.succ = 137) :
  ∑ k in Finset.range 49, u (2 * k.succ) = 93 := by
  have h_u_form : ∀ n, u n = u 0 + n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h₂ := h₀ n
      simp [ih] at h₂ ⊢
      <;> linarith

  have h_sum_main : ∑ k in Finset.range 49, u (2 * k.succ) = 93 := by
    have h₂ : ∑ k in Finset.range 49, u (2 * k.succ) = 93 := by
      have h₃ : ∑ k in Finset.range 49, u (2 * k.succ) = ∑ k in Finset.range 49, (u 0 + (2 * k.succ : ℚ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [h_u_form (2 * k.succ)]
        <;> simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
        <;> ring_nf
        <;> norm_cast
        <;> omega
      rw [h₃]
      simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Finset.sum_const, Finset.card_range]
      <;> ring_nf
      <;> norm_cast
      <;> rfl
    exact h₂

  exact h_sum_main
