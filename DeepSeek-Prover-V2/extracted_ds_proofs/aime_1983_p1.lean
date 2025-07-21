import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have h3 : Real.log x > 0 := by
    apply Real.log_pos
    norm_num
    linarith

  have h4 : Real.log y > 0 := by
    apply Real.log_pos
    norm_num
    linarith

  have h5 : Real.log z > 0 := by
    apply Real.log_pos
    norm_num
    linarith

  have h6 : Real.log w = 24 * Real.log x := by
    have h6 : Real.log w / Real.log x = 24 := h0
    have h7 : Real.log x ≠ 0 := by linarith
    field_simp [h7] at h6 ⊢
    <;> nlinarith

  have h7 : Real.log w = 40 * Real.log y := by
    have h7 : Real.log w / Real.log y = 40 := h1
    have h8 : Real.log y ≠ 0 := by linarith
    field_simp [h8] at h7 ⊢
    <;> nlinarith

  have h8 : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
    have h8 : Real.log w / Real.log (x * y * z) = 12 := h2
    have h9 : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      <;> ring
    rw [h9] at h8
    have h10 : Real.log x + Real.log y + Real.log z ≠ 0 := by
      intro h
      have h11 : Real.log x + Real.log y + Real.log z = 0 := h
      have h12 : Real.log x > 0 := h3
      have h13 : Real.log y > 0 := h4
      have h14 : Real.log z > 0 := h5
      linarith
    field_simp [h10] at h8 ⊢
    <;> nlinarith

  have h9 : 3 * Real.log x = 5 * Real.log y := by
    have h9 : Real.log w = 24 * Real.log x := h6
    have h10 : Real.log w = 40 * Real.log y := h7
    have h11 : 24 * Real.log x = 40 * Real.log y := by linarith
    have h12 : 3 * Real.log x = 5 * Real.log y := by
      ring_nf at h11 ⊢
      nlinarith
    exact h12

  have h10 : Real.log x = (5 / 3) * Real.log y := by
    have h10 : 3 * Real.log x = 5 * Real.log y := h9
    have h11 : Real.log x = (5 / 3) * Real.log y := by
      apply Eq.symm
      field_simp at h10 ⊢
      <;> nlinarith
    exact h11

  have h11 : Real.log x = Real.log y + Real.log z := by
    have h11 : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := h8
    have h12 : Real.log w = 24 * Real.log x := h6
    have h13 : Real.log w = 40 * Real.log y := h7
    have h14 : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by linarith
    have h15 : 40 * Real.log y = 12 * (Real.log x + Real.log y + Real.log z) := by linarith
    have h16 : Real.log x = Real.log y + Real.log z := by
      apply Eq.symm
      ring_nf at h14 h15 ⊢
      <;> nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2), Real.log_pos (by norm_num : (1 : ℝ) < 2),
        Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    exact h16

  have h12 : Real.log z = (2 / 3) * Real.log y := by
    have h12 : Real.log x = Real.log y + Real.log z := h11
    have h13 : Real.log x = (5 / 3) * Real.log y := h10
    have h14 : Real.log y + Real.log z = (5 / 3) * Real.log y := by linarith
    have h15 : Real.log z = (5 / 3) * Real.log y - Real.log y := by linarith
    have h16 : Real.log z = (2 / 3) * Real.log y := by
      ring_nf at h15 ⊢
      <;> nlinarith
    exact h16

  have h13 : Real.log w / Real.log z = 60 := by
    have h13 : Real.log w = 40 * Real.log y := h7
    have h14 : Real.log z = (2 / 3) * Real.log y := h12
    have h15 : Real.log w / Real.log z = (40 * Real.log y) / ((2 / 3) * Real.log y) := by rw [h13, h14]
    have h16 : (40 * Real.log y) / ((2 / 3) * Real.log y) = 60 := by
      have h17 : Real.log y ≠ 0 := by
        intro h18
        have h19 : Real.log y = 0 := h18
        have h20 : y = 1 := by
          rw [← Real.exp_log (show 0 < (y : ℝ) by norm_cast; linarith)]
          simp [h19]
        norm_num at h20
        <;> simp_all
      field_simp [h17]
      <;> ring
    linarith

  exact h13
