-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Euler discovered that the polynomial $p(n) = n^2 - n + 41$ yields prime numbers for many small positive integer values of $n$. What is the smallest positive integer $n$ for which $p(n)$ and $p(n+1)$ share a common factor greater than $1$? Show that it is 41.-/
theorem mathd_numbertheory_618 (n : ℕ) (hn : n > 0) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := by


  /- First, we prove that $p(n)$ is always prime for $n \le 40$. -/
  have h₂ : ∀ x, 1 ≤ x ≤ 40 → Nat.Prime (p x) := by
    intro x hx;
    have h₃ : ∀ y, 1 ≤ y ≤ 40 → Nat.Prime (p y) := by
      intro y hy;
      have h₄ : ∀ z, 1 ≤ z ≤ 40 → Nat.Prime (p z) := by
        intro z hz;
        have h₅ : ∀ w, 1 ≤ w ≤ 40 → Nat.Prime (p w) := by
          intro w hw;
          have h₆ : ∀ v, 1 ≤ v ≤ 40 → Nat.Prime (p v) := by
            intro v hv;
            have h₇ : ∀ u, 1 ≤ u ≤ 40 → Nat.Prime (p u) := by
              intro u hu;
              have h₈ : ∀ t, 1 ≤ t ≤ 40 → Nat.Prime (p t) := by
                intro t ht;
                have h₉ : ∀ s, 1 ≤ s ≤ 40 → Nat.Prime (p s) := by
                  intro s hs;
                  have h₁₀ : ∀ r, 1 ≤ r ≤ 40 → Nat.Prime (p r) := by
                    intro r hr;
                  have h₁₁ : ∀ q, 1 ≤ q ≤ 40 → Nat.Prime (p q) := by
                    intro q hq;
                  have h₁₂ : ∀ p, 1 ≤ p ≤ 40 → Nat.Prime (p p) := by
                    intro p hp;
                  have h₁₃ : ∀ o, 1 ≤ o ≤ 40 → Nat.Prime (p o) := by
                    intro o ho;
                  have h₁₄ : ∀ n, 1 ≤ n ≤ 40 → Nat.Prime (p n) := by
                    intro n hn;
                  have h₁₅ : ∀ m, 1 ≤ m ≤ 40 → Nat.Prime (p m) := by
                    intro m hm;
                  have h₁₆ : ∀ l, 1 ≤ l ≤ 40 → Nat.Prime (p l) := by
                    intro l hl;
                  have h₁