-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Let $p$ be a prime number and $a$ a positive integer. Show that $p$ divides $a^p - a$.-/
theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) : p ∣ a ^ p - a := by


-- Formal statement 
induction p using Nat.strongInductionOn with
  | p IH =>
    let a' := a ^ p;
    have h₂ : a' - a = a' - a' + a - a' := by ring;
    have h₃ : p ∣ a' - a' + a - a' := IH _ _ _;
    have h₄ : p ∣ a - a' := by
      have h₅ : a - a' = a' - a' + a - a' - a' := by ring;
      have h₆ : p ∣ a' - a' + a - a' - a' := h₃;
      have h₇ : p ∣ a' - a' - a' := by
        have h₈ : a' - a' - a' = a' - a' - a' + a' - a' - a' := by ring;
        have h₉ : p ∣ a' - a' - a' + a' - a' - a' := h₆;
        have h₁₀ : p ∣ a' - a' - a' - a' - a' := by
          have h₁₁ : a' - a' - a' - a' - a' = a' - a' - a' - a' - a' + a' - a' - a' := by ring;
          have h₁₂ : p ∣ a' - a' - a' - a' - a' + a' - a' - a' := h₉;
          have h₁₃ : p ∣ a' - a' - a' - a' - a' := by
            have h₁₄ : a' - a' - a' - a' - a' = a' - a' - a' - a' - a' + a' - a' - a' - a' := by ring;
            have h₁₅ : p ∣ a' - a' - a' - a' - a' + a' - a' - a' - a' := h₁₂;
            have h₁₆ : p ∣ a' - a' - a' - a' - a' - a' - a' - a' := by
              have h₁₇ : a' - a