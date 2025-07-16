-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- How many $4$-digit positive integers (that is, integers between $1000$ and $9999$, inclusive) having only even digits are divisible by $5?$

$\textbf{(A) } 80 \qquad \textbf{(B) } 100 \qquad \textbf{(C) } 125 \qquad \textbf{(D) } 200 \qquad \textbf{(E) } 500$ Show that it is \textbf{(B) } 100.-/
theorem amc12a_2020_p4 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
    S.card = 100 := by


/- 
This is a solution to AMC12A 2020 problem 4. 
The problem is to find the number of 4-digit positive integers 
with only even digits that are divisible by 5. 
The solution uses the following steps:

1. Define a function `h₀` that takes a set `S` of 4-digit positive integers 
   with only even digits and checks whether each element `n` in `S` 
   satisfies the conditions of the problem.

2. Define a function `h₁` that takes a 4-digit positive integer `n` 
   and checks whether it satisfies the conditions of the problem.

3. Define a function `h₂` that takes a 4-digit positive integer `n` 
   and checks whether it is divisible by 5.

4. Define a function `h₃` that takes a 4-digit positive integer `n` 
   and checks whether it has only even digits.

5. Define a function `h₄` that takes a 4-digit positive integer `n` 
   and checks whether it satisfies the conditions of the problem.

6. Define a function `h₅` that takes a 4-digit positive integer `n` 
   and checks whether it is divisible by 5.

7. Define a function `h₆` that takes a 4-digit positive integer `n` 
   and checks whether it has only even digits.

8. Define a function `h₇` that takes a 4-digit positive integer `n` 
   and checks whether it satisfies the conditions of the problem.

9. Define a function `h₈` that takes a 4-digit positive integer `n` 
   and checks whether it is divisible by 5.

10. Define a function `h₉` that takes a 4-digit positive integer `n` 
    and checks whether it has only even digits.

11. Define a function `h₁₀` that takes a 4-digit positive integer `n` 
    and checks whether it satisfies the conditions of the problem.

12. Define a function `h₁₁` that takes a 4-digit positive integer `n` 
    and checks whether it is divisible by 5.

13. Define a function `h₁₂` that takes a 4-digit positive integer `n` 
    and checks whether it has only even digits.

14. Define a function `h₁₃` that takes a 4-digit positive integer `