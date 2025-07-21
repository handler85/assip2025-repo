import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
### Detailed Proof and Analysis

First, recall the problem:
We have a polynomial \( p(n) = n^2 - n + 41 \). We are to show that if \( \gcd(p(n), p(n+1)) > 1 \), then \( n \geq 41 \).

#### Key Observations:
1. The polynomial \( p(n) = n^2 - n + 41 \) is famous because it is known to produce prime numbers for \( n = 1, 2, \dots, 40 \).
2. The condition \( \gcd(p(n), p(n+1)) > 1 \) is equivalent to \( p(n) \) and \( p(n+1) \) sharing a common prime factor.
3. We can compute \( p(n+1) = (n+1)^2 - (n+1) + 41 = n^2 + 2n + 1 - n - 1 + 41 = n^2 + n + 41 \).
   - So, \( p(n+1) = p(n) + n \).
4. The condition \( \gcd(p(n), p(n+1)) > 1 \) becomes \( \gcd(p(n), p(n) + n) > 1 \).
   - Since \( \gcd(a, b) = \gcd(a, b - a) \), we have \( \gcd(p(n), p(n) + n) = \gcd(p(n), n) \).
   - Therefore, the condition is equivalent to \( \gcd(p(n), n) > 1 \).
5. We can further simplify \( p(n) = n^2 - n + 41 \). Since \( n \geq 1 \), \( p(n) \geq 41 \).
   - The condition \( \gcd(p(n), n) > 1 \) is equivalent to \( n \) having a prime factor that divides \( p(n) \).
   - But \( p(n) \equiv 41 \mod n \) is not directly helpful. Instead, we can consider the possible values of \( n \).

#### Strategy:
We will show that if \( n < 41 \), then \( \gcd(p(n), n) = 1 \). This will imply that \( n \geq 41 \).

1. For \( n = 1 \), \( p(1) = 1 - 1 + 41 = 41 \), \( \gcd(41, 1) = 1 \).
2. For \( n = 2 \), \( p(2) = 4 - 2 + 41 = 43 \), \( \gcd(43, 2) = 1 \).
3. For \( n = 3 \), \( p(3) = 9 - 3 + 41 = 47 \), \( \gcd(47, 3) = 1 \).
4. For \( n = 4 \), \( p(4) = 16 - 4 + 41 = 53 \), \( \gcd(53, 4) = 1 \).
5. For \( n = 5 \), \( p(5) = 25 - 5 + 41 = 61 \), \( \gcd(61, 5) = 1 \).
6. For \( n = 6 \), \( p(6) = 36 - 6 + 41 = 71 \), \( \gcd(71, 6) = 1 \).
7. For \( n = 7 \), \( p(7) = 49 - 7 + 41 = 83 \), \( \gcd(83, 7) = 1 \).
8. For \( n = 8 \), \( p(8) = 64 - 8 + 41 = 97 \), \( \gcd(97, 8) = 1 \).
9. For \( n = 9 \), \( p(9) = 81 - 9 + 41 = 113 \), \( \gcd(113, 9) = 1 \).
10. For \( n = 10 \), \( p(10) = 100 - 10 + 41 = 131 \), \( \gcd(131, 10) = 1 \).
11. For \( n = 11 \), \( p(11) = 121 - 11 + 41 = 151 \), \( \gcd(151, 11) = 1 \).
12. For \( n = 12 \), \( p(12) = 144 - 12 + 41 = 173 \), \( \gcd(173, 12) = 1 \).
13. For \( n = 13 \), \( p(13) = 169 - 13 + 41 = 197 \), \( \gcd(197, 13) = 1 \).
14. For \( n = 14 \), \( p(14) = 196 - 14 + 41 = 223 \), \( \gcd(223, 14) = 1 \).
15. For \( n = 15 \), \( p(15) = 225 - 15 + 41 = 251 \), \( \gcd(251, 15) = 1 \).
16. For \( n = 16 \), \( p(16) = 256 - 16 + 41 = 281 \), \( \gcd(281, 16) = 1 \).
17. For \( n = 17 \), \( p(17) = 289 - 17 + 41 = 313 \), \( \gcd(313, 17) = 1 \).
18. For \( n = 18 \), \( p(18) = 324 - 18 + 41 = 347 \), \( \gcd(347, 18) = 1 \).
19. For \( n = 19 \), \( p(19) = 361 - 19 + 41 = 383 \), \( \gcd(383, 19) = 1 \).
20. For \( n = 20 \), \( p(20) = 400 - 20 + 41 = 421 \), \( \gcd(421, 20) = 1 \).
21. For \( n = 21 \), \( p(21) = 441 - 21 + 41 = 461 \), \( \gcd(461, 21) = 1 \).
22. For \( n = 22 \), \( p(22) = 484 - 22 + 41 = 503 \), \( \gcd(503, 22) = 1 \).
23. For \( n = 23 \), \( p(23) = 529 - 23 + 41 = 547 \), \( \gcd(547, 23) = 1 \).
24. For \( n = 24 \), \( p(24) = 576 - 24 + 41 = 593 \), \( \gcd(593, 24) = 1 \).
25. For \( n = 25 \), \( p(25) = 625 - 25 + 41 = 641 \), \( \gcd(641, 25) = 1 \).
26. For \( n = 26 \), \( p(26) = 676 - 26 + 41 = 691 \), \( \gcd(691, 26) = 1 \).
27. For \( n = 27 \), \( p(27) = 729 - 27 + 41 = 743 \), \( \gcd(743, 27) = 1 \).
28. For \( n = 28 \), \( p(28) = 784 - 28 + 41 = 797 \), \( \gcd(797, 28) = 1 \).
29. For \( n = 29 \), \( p(29) = 841 - 29 + 41 = 853 \), \( \gcd(853, 29) = 1 \).
30. For \( n = 30 \), \( p(30) = 900 - 30 + 41 = 911 \), \( \gcd(911, 30) = 1 \).
31. For \( n = 31 \), \( p(31) = 961 - 31 + 41 = 971 \), \( \gcd(971, 31) = 1 \).
32. For \( n = 32 \), \( p(32) = 1024 - 32 + 41 = 1033 \), \( \gcd(1033, 32) = 1 \).
33. For \( n = 33 \), \( p(33) = 1089 - 33 + 41 = 1097 \), \( \gcd(1097, 33) = 1 \).
34. For \( n = 34 \), \( p(34) = 1156 - 34 + 41 = 1163 \), \( \gcd(1163, 34) = 1 \).
35. For \( n = 35 \), \( p(35) = 1225 - 35 + 41 = 1231 \), \( \gcd(1231, 35) = 1 \).
36. For \( n = 36 \), \( p(36) = 1296 - 36 + 41 = 1291 \), \( \gcd(1291, 36) = 1 \).
37. For \( n = 37 \), \( p(37) = 1369 - 37 + 41 = 1373 \), \( \gcd(1373, 37) = 1 \).
38. For \( n = 38 \), \( p(38) = 1444 - 38 + 41 = 1447 \), \( \gcd(1447, 38) = 1 \).
39. For \( n = 39 \), \( p(39) = 1521 - 39 + 41 = 1523 \), \( \gcd(1523, 39) = 1 \).
40. For \( n = 40 \), \( p(40) = 1600 - 40 + 41 = 1601 \), \( \gcd(1601, 40) = 1 \).

From the above calculations, we observe that for \( n \geq 41 \), \( p(n) \) is a prime number. Therefore, if \( n < 41 \), \( p(n) \) is not a prime number.

#### Conclusion:
The smallest positive integer \( n \) for which \( \gcd(p(n), p(n+1)) > 1 \) is \( 41 \).

### Abstract Plan

1. **Understand the Problem**:
   - We need to find the smallest \( n \) such that \( \gcd(p(n), p(n+1)) > 1 \), where \( p(n) = n^2 - n + 41 \).

2. **Calculate \( p(n) \) for Small \( n \)**:
   - Compute \( p(n) \) for \( n = 1 \) to \( n = 40 \) and check if \( \gcd(p(n), p(n+1)) > 1 \).

3. **Check for \( n \geq 41 \)**:
   - Verify that for \( n \geq 41 \), \( p(n) \) is prime, ensuring no smaller \( n \) satisfies the condition.

4. **Conclusion**:
   - The smallest \( n \) is \( 41 \).

### Lean 4 Proof Sketch

```lean4
theorem mathd_numbertheory_618
  (n : ℕ)
  (p : ℕ → ℕ)
  (h₀ : ∀ x, p x = x^2 - x + 41)
  (h₁ : 1 < Nat.gcd (p n) (p (n+1))) :
  41 ≤ n := by
  have h₂ : ∀ x, p x = x^2 - x + 41 := by simpa using h₀
  have h₃ : 1 < Nat.gcd (p n) (p (n+1)) := h₁
  have h₄ : 41 ≤ n := by
    by_contra h
    have h₅ : n ≤ 40 := by linarith
    have h₆ : n ≥ 1 := by
      by_contra h₇
      have h₈ : n = 0 := by omega
      simp_all [h₈, h₂, Nat.gcd_eq_right]
    interval_cases n <;> simp_all [h₂, Nat.gcd_eq_right]
  exact h₄
```