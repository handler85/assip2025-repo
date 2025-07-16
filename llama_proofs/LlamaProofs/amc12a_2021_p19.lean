-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- How many solutions does the equation $\sin \left( \frac{\pi}2 \cos x\right)=\cos \left( \frac{\pi}2 \sin x\right)$ have in the closed interval $[0,\pi]$?

$\textbf{(A) }0 \qquad \textbf{(B) }1 \qquad \textbf{(C) }2 \qquad \textbf{(D) }3\qquad \textbf{(E) }4$ Show that it is \textbf{(C) }2.-/
theorem amc12a_2021_p19 (S : Finset ℝ)
    (h₀ :
      ∀ x : ℝ,
        x ∈ S ↔
          0 ≤ x ∧
            x ≤ Real.pi ∧
              Real.sin (Real.pi / 2 * Real.cos x) = Real.cos (Real.pi / 2 * Real.sin x)) :
    S.card = 2 := by


  /- First, we note that $\sin \left( \frac{\pi}2 \cos x\right)$ and $\cos \left( \frac{\pi}2 \sin x\right)$ are both continuous functions of $x$.-/
  have cont_sin_cos :
    ∀ x : ℝ,
      Real.sin (Real.pi / 2 * Real.cos x) = Real.cos (Real.pi / 2 * Real.sin x) →
        ContinuousAt (λ x, Real.sin (Real.pi / 2 * Real.cos x)) x ∧
          ContinuousAt (λ x, Real.cos (Real.pi / 2 * Real.sin x)) x :=
    by
  intros x H
  split; try { apply ContinuousAt.sin }
  try { apply ContinuousAt.cos }

  /- Now, we note that $\sin \left( \frac{\pi}2 \cos x\right)$ and $\cos \left( \frac{\pi}2 \sin x\right)$ both have a maximum value of $1$.-/
  have max_sin_cos :
    ∀ x : ℝ,
      Real.sin (Real.pi / 2 * Real.cos x) ≤ 1 ∧
        Real.cos (Real.pi / 2 * Real.sin x) ≤ 1 :=
    by
  intros x
  split; try { apply Real.sin_le_one }
  try { apply Real.cos_le_one }

  /- Now, we note that $\sin \left( \frac{\pi}2 \cos x\right)$ and $\cos \left( \frac{\pi}2 \sin x\right)$ both have a minimum value of $-1$.-/
  have min_sin_cos :
    ∀ x : ℝ,
      Real.sin (Real.pi / 2 * Real.cos x) ≥ -1 ∧
        Real.cos (Real.pi / 2 * Real.sin x) ≥ -1 :=
    by
  intros x
  split; try { apply Real.sin_ge_minus_one }
  try { apply Real.cos_ge_minus_one }

  /- Now, we note that $\sin \left( \frac{\pi}2 \cos x\right)$ and $\cos \left( \frac{\pi}2 \sin x\right)$ both have a range of $[-1,1]$.-/
  have range_sin_cos :
    ∀ x : ℝ,
      Real.sin (Real.pi / 2 * Real.cos x) ∈