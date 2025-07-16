-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Let $x$, $y$ and $z$ all exceed $1$ and let $w$ be a positive number such that $\log_x w = 24$, $\log_y w = 40$ and $\log_{xyz} w = 12$. Find $\log_z w$. Show that it is 060.-/
theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by


  /- First, note that $\log_x w$ is positive. -/
  have h3 : 0 < Real.log w / Real.log x := by linarith [h0, hw, ht.1]

  /- Now note that $\log_x w$ is an integer. -/
  have h4 : Real.log w / Real.log x ∈ ℤ := by linarith [h3, h0]

  /- Similarly, $\log_y w$ and $\log_{xyz} w$ are integers. -/
  have h5 : Real.log w / Real.log y ∈ ℤ := by linarith [h1, hw, ht.2]
  have h6 : Real.log w / Real.log (x * y * z) ∈ ℤ := by linarith [h2, hw, ht.1, ht.2, ht.3]

  /- Now note that $\log_x w$, $\log_y w$ and $\log_{xyz} w$ are all positive. -/
  have h7 : 0 < Real.log w / Real.log x ∧ 0 < Real.log w / Real.log y ∧ 0 < Real.log w / Real.log (x * y * z) := by linarith [h0, h1, h2, hw]

  /- Now note that $\log_x w$, $\log_y w$ and $\log_{xyz} w$ are all integers. -/
  have h8 : Real.log w / Real.log x ∈ ℤ ∧ Real.log w / Real.log y ∈ ℤ ∧ Real.log w / Real.log (x * y * z) ∈ ℤ := by linarith [h4, h5, h6]

  /- Now note that $\log_x w$, $\log_y w$ and $\log_{xyz} w$ are all positive integers. -/
  have h9 : 0 < Real.log w / Real.log x ∧ 0 < Real.log w / Real.log y ∧ 0 < Real.log w / Real.log (x * y * z) ∧
      Real.log w / Real.log x ∈ ℤ ∧ Real.log w / Real.log y ∈ ℤ ∧ Real.log w / Real.log (x * y * z) ∈ ℤ := by linarith [h7, h8]

  /- Now note that $\log_z w$ is positive. -/
  have h10 : 0 < Real.log w / Real.log z := by