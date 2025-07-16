-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Prove that $\cos{\frac{\pi}{7}}-\cos{\frac{2\pi}{7}}+\cos{\frac{3\pi}{7}}=\frac{1}{2}$.-/
theorem imo_1963_p5 : Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7) = 1 / 2 := by


-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Prove that $\cos{\frac{\pi}{7}}-\cos{\frac{2\pi}{7}}+\cos{\frac{3\pi}{7}}=\frac{1}{2}$.-/
theorem imo_1963_p5 : Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7) = 1 / 2 := by
  simp [Real.cos_add, Real.cos_pi_div, Real.cos_two_pi_div, Real.cos_three_pi_div, Real.cos_half_pi, Real.cos_half_pi_div_two, Real.cos_half_pi_div_three, Real.cos_half_pi_div_two_div_three, Real.cos_half_pi_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real.cos_half_pi_div_two_div_two_div_two_div_two_div_two, Real