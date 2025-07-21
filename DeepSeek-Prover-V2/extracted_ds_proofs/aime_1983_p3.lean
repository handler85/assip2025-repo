import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

theorem aime_1983_p3
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (x^2 + (18 * x +  30) - 2 * Real.sqrt (x^2 + (18 * x + 45))))
  (h₁ : Fintype (f⁻¹' {0})) :
  ∏ x in (f⁻¹' {0}).toFinset, x = 20 := by
  have h_main : ∏ x in (f⁻¹' {0}).toFinset, x = 20 := by
    have h₂ : f⁻¹' {0} = { -9 + Real.sqrt 61, -9 - Real.sqrt 61 } := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
        Set.mem_insert_iff]
      constructor
      · intro h
        have h₃ : f x = 0 := h
        have h₄ : x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 := by
          simp_all [h₀]
        have h₅ : x ^ 2 + (18 * x + 30) = 2 * Real.sqrt (x ^ 2 + (18 * x + 45)) := by linarith
        have h₆ : Real.sqrt (x ^ 2 + (18 * x + 45)) ≥ 0 := Real.sqrt_nonneg _
        have h₇ : (x ^ 2 + (18 * x + 45)) ≥ 0 := by
          by_contra h
          have h₈ : x ^ 2 + (18 * x + 45) < 0 := by linarith
          have h₉ : Real.sqrt (x ^ 2 + (18 * x + 45)) = 0 := by
            apply Real.sqrt_eq_zero_of_nonpos
            nlinarith
          nlinarith
        have h₈ : (x ^ 2 + (18 * x + 45)) ≥ 0 := by linarith
        have h₉ : Real.sqrt (x ^ 2 + (18 * x + 45)) ≥ 0 := Real.sqrt_nonneg _
        have h₁₀ : (Real.sqrt (x ^ 2 + (18 * x + 45))) ^ 2 = x ^ 2 + (18 * x + 45) := by
          rw [Real.sq_sqrt] <;> nlinarith
        have h₁₁ : x = -9 + Real.sqrt 61 ∨ x = -9 - Real.sqrt 61 := by
          apply or_iff_not_imp_left.mpr
          intro h₁₂
          apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₂)
          nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num),
            Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ x ^ 2 + (18 * x + 45) by nlinarith)]
        cases h₁₁ with
        | inl h₁₁ =>
          simp_all
        | inr h₁₁ =>
          simp_all
      · intro h
        rcases h with (rfl | rfl)
        · -- Case x = -9 + Real.sqrt 61
          have h₃ : Real.sqrt 61 ≥ 0 := Real.sqrt_nonneg _
          have h₄ : (-9 + Real.sqrt 61) ^ 2 + (18 * (-9 + Real.sqrt 61) + 30) - 2 * Real.sqrt (((-9 + Real.sqrt 61)) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45)) = 0 := by
            have h₅ : Real.sqrt (((-9 + Real.sqrt 61)) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45)) = Real.sqrt 61 := by
              have h₆ : ((-9 + Real.sqrt 61)) ^ 2 + (18 * (-9 + Real.sqrt 61) + 45) = 61 := by
                nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
              rw [h₆]
              <;>
                simp [Real.sqrt_eq_iff_sq_eq] <;>
                  nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
            nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num), Real.sqrt_nonneg 61, h₅]
          simp_all [h₀]
        · -- Case x = -9 - Real.sqrt 61
          have h₃ : Real.sqrt 61 ≥ 0 := Real.sqrt_nonneg _
          have h₄ : (-9 - Real.sqrt 61) ^ 2 + (18 * (-9 - Real.sqrt 61) + 30) - 2 * Real.sqrt (((-9 - Real.sqrt 61)) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45)) = 0 := by
            have h₅ : Real.sqrt (((-9 - Real.sqrt 61)) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45)) = Real.sqrt 61 := by
              have h₆ : ((-9 - Real.sqrt 61)) ^ 2 + (18 * (-9 - Real.sqrt 61) + 45) = 61 := by
                nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
              rw [h₆]
              <;>
                simp [Real.sqrt_eq_iff_sq_eq] <;>
                  nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show 0 ≤ 61 by norm_num)]
            nlinarith [Real.sq_sqrt (show 0 ≤ 61 by norm_num), Real.sqrt_nonneg 61, h₅]
          simp_all [h₀]
      <;> aesop
    have h₃ : f⁻¹' {0} = { -9 + Real.sqrt 61, -9 - Real.sqrt 61 } := by rw [h₂]
    have h₄ : ∏ x in (f⁻¹' {0}).toFinset, x = 20 := by
      rw [h₃]
      simp [Finset.prod_pair, Real.sqrt_eq_iff_sq_eq, sq, mul_comm]
      <;> ring_nf
      <;> norm_num
      <;> field_simp [Real.sqrt_eq_iff_sq_eq, sq, mul_comm]
      <;> ring_nf
      <;> norm_num
      <;> linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 61 by norm_num)]
    exact h₄
  exact h_main
