import Mathlib.Data.Int.Modeq
import Mathlib.Tactic.Ring

/-
Prove that for any integer n, n⁵ - n is divisible by 30.
This problem is a classic from number theory and is present in the miniF2F dataset.
The strategy is to prove that the expression is divisible by 2, 3, and 5.
Since 2, 3, and 5 are coprime, if it's divisible by each, it must be
divisible by their product, 30.
-/
theorem miniF2F_number_theory_ex (n : ℤ) : 30 ∣ n^5 - n := by
  -- The core idea is to show divisibility by 2, 3, and 5 separately.
  -- We can use `Int.dvd_of_dvd_coprimes` but it's more direct to prove
  -- each case with modular arithmetic. The `ring` tactic is useful for
  -- simplifying polynomial expressions.
  have h_factored : n^5 - n = (n - 1) * n * (n + 1) * (n^2 + 1) := by
    ring

  rw [h_factored]

  -- We need to show that the expression is a multiple of 30.
  -- This is equivalent to showing `(n^5 - n) % 30 = 0`, but we will
  -- prove divisibility by 2, 3, and 5 and combine them.
  -- Mathlib's `Int.dvd_of_dvd_coprimes` is perfect for this.
  -- Let's show divisibility by 3 first, as it's a factor of n(n-1)(n+1).
  have h3 : 3 ∣ (n - 1) * n * (n + 1) := by
    -- The product of any three consecutive integers is divisible by 3.
    exact Int.dvd_of_mod_eq_zero (Int.mod_prod_consecutive n 3 1)

  have h3_full : 3 ∣ (n - 1) * n * (n + 1) * (n^2 + 1) := by
    apply Dvd.dvd.mul_right
    exact h3

  -- Now let's show divisibility by 2.
  -- The product of two consecutive integers (n-1)*n is always even.
  have h2 : 2 ∣ (n - 1) * n := by
    exact Int.dvd_of_mod_eq_zero (Int.mod_prod_consecutive n 2 0)

  have h2_full : 2 ∣ (n - 1) * n * (n + 1) * (n^2 + 1) := by
    apply Dvd.dvd.mul_right
    -- We need to show 2 | (n-1)*n * ((n+1)*(n^2+1))
    -- We already have 2 | (n-1)*n
    exact Dvd.dvd.mul_right h2 ((n + 1) * (n^2 + 1))

  -- Finally, let's show divisibility by 5 using case analysis on `n % 5`.
  have h5 : 5 ∣ (n - 1) * n * (n + 1) * (n^2 + 1) := by
    -- We can use Fermat's Little Theorem: n^5 ≡ n (mod 5)
    -- which is equivalent to 5 ∣ n^5 - n.
    -- Let's prove it directly with case analysis for clarity.
    let m := n % 5
    have hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by
      -- This is true by the properties of integers mod 5.
      int_cases n % 5 <;> simp [*]

    rcases hm with hm | hm | hm | hm | hm
    -- Case 1: n % 5 = 0
    · rw [show n % 5 = 0 by assumption] at h_factored
      rw [← Int.dvd_iff_mod_eq_zero] at hm
      apply Dvd.dvd.mul_left
      apply Dvd.dvd.mul_right
      exact hm
    -- Case 2: n % 5 = 1
    · have h_m1 : (n - 1) % 5 = 0 := by
        rw [Int.sub_mod, hm]
        norm_num
      rw [← Int.dvd_iff_mod_eq_zero] at h_m1
      apply Dvd.dvd.mul_right
      apply Dvd.dvd.mul_right
      exact h_m1
    -- Case 3: n % 5 = 2
    · have h_n2p1 : (n^2 + 1) % 5 = 0 := by
        rw [Int.add_mod, Int.pow_mod, hm]
        norm_num -- 2^2 + 1 = 5, which is 0 mod 5
      rw [← Int.dvd_iff_mod_eq_zero] at h_n2p1
      apply Dvd.dvd.mul_left
      exact h_n2p1
    -- Case 4: n % 5 = 3
    · have h_n2p1 : (n^2 + 1) % 5 = 0 := by
        rw [Int.add_mod, Int.pow_mod, hm]
        norm_num -- 3^2 + 1 = 10, which is 0 mod 5
      rw [← Int.dvd_iff_mod_eq_zero] at h_n2p1
      apply Dvd.dvd.mul_left
      exact h_n2p1
    -- Case 5: n % 5 = 4
    · have h_p1 : (n + 1) % 5 = 0 := by
        rw [Int.add_mod, hm]
        norm_num
      rw [← Int.dvd_iff_mod_eq_zero] at h_p1
      apply Dvd.dvd.mul_left
      apply Dvd.dvd.mul_right
      exact h_p1

  -- Now, combine the divisibility results.
  -- Since 2, 3, and 5 are coprime, their product must divide the expression.
  -- 30 = 2 * 3 * 5
  have h_coprime_3_2 : Int.Coprime 3 2 := by norm_num
  have h_dvd_6 : 6 ∣ (n - 1) * n * (n + 1) * (n^2 + 1) := by
    exact Int.Coprime.dvd_of_dvd h_coprime_3_2 h3_full h2_full

  have h_coprime_6_5 : Int.Coprime 6 5 := by norm_num

  exact Int.Coprime.dvd_of_dvd h_coprime_6_5 h_dvd_6 h5
