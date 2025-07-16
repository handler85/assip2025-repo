-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Let $a$ and $b$ be two integer numbers. Show that the following statement is false: $a$ and $b$ are both even iff $8 \mid a^2 + b^2$.-/
theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by


-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Let $a$ and $b$ be two integer numbers. Show that the following statement is false: $a$ and $b$ are both even iff $8 \mid a^2 + b^2$.-/
theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := by
  intro H
  let a := 1
  let b := 1
  have H1 : ∃ i j, a = 2 * i ∧ b = 2 * j := ⟨0, 0, rfl, rfl⟩
  have H2 : ¬∃ k, a ^ 2 + b ^ 2 = 8 * k := by
    intro Hk
    have Hk1 : 1 ^ 2 + 1 ^ 2 = 2 := by ring
    have Hk2 : 2 ≠ 8 * k := by linarith
    have Hk3 : Hk1 = Hk2 := by linarith
    contradiction
  have H3 : ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := H
  have H4 : H1 ∧ ¬H2 := And.intro H1 H2
  have H5 : ¬H3 := not_and_iff_not_and_not.1 H4
  have H6 : ¬H3 := H3
  have H7 : False := not_and_iff_not_and_not.2 H5 H6
  contradiction

-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Let $a$ and $b$ be two integer numbers. Show that the following statement is false: $a$ and $b$ are both even iff $8 \mid a^2 + b^2$.-/
theorem numbertheory_notequiv2i2jasqbsqdiv