-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- A positive integer $n$ is nice if there is a positive integer $m$ with exactly four positive divisors (including $1$ and $m$) such that the sum of the four divisors is equal to $n.$ Find the sum of all the nice numbers in the set $\{ 2010,2011,2012,\dots,2019 \}.$ Show that it is 2016.-/
theorem mathd_numbertheory_451 (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n) :
    (∑ k in S, k) = 2016 := by


  let S' : Finset ℕ := S.filter (λ n, 2010 ≤ n ∧ n ≤ 2019)

  have h₁ : ∀ n : ℕ, n ∈ S' → ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n :=
    λ n, Finset.mem_filter.mp (h₀ n)

  have h₂ : ∀ m : ℕ, (Nat.divisors m).card = 4 → ∑ p in Nat.divisors m, p = m :=
    λ m, Nat.divisors_divisors_sum_eq_self

  have h₃ : ∀ m : ℕ, (Nat.divisors m).card = 4 → 2010 ≤ m ∧ m ≤ 2019 :=
    λ m, Finset.mem_filter.mp (h₀ m)

  have h₄ : ∀ m : ℕ, (Nat.divisors m).card = 4 → 2010 ≤ m ∧ m ≤ 2019 →
      ∑ k in Finset.filter (λ n, 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n),
          k =
      2016 := by
    intro m; intro h₅; intro h₆; intro h₇; intro h₈;
    have h₉ : ∀ n : ℕ, n ∈ Finset.filter (λ n, 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n) →
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n :=
      λ n, Finset.mem_filter.mp

    have h₁₀ : ∀ n : ℕ, n ∈ Finset.filter (λ n, 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n) →
          ∑ k in Finset.filter (λ n, 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m