-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Solve the congruence $3n \equiv 2 \pmod{11}$, as a residue modulo 11.  (Give an answer between 0 and 10.) Show that it is 8.-/
theorem mathd_numbertheory_247 (n : ℕ) (h₀ : 3 * n % 11 = 2) : n % 11 = 8 := by


# Formal statement 
# 
# The goal is to solve the congruence $3n \equiv 2 \pmod{11}$, 
# which means we want to find the smallest non-negative integer $n$ 
# such that $3n \equiv 2 \pmod{11}$. 
# 
# We start by rewriting the congruence as $3n \equiv 2 \pmod{11}$ 
# which is equivalent to $3n - 2 \equiv 0 \pmod{11}$. 
# 
# Now we can use the extended Euclidean algorithm to find 
# the coefficients $a$ and $b$ such that $11a + 3b = 1$. 
# 
# Once we have these coefficients, we can write 
# $n \equiv 2 \pmod{11}$ as $n \equiv 2a \pmod{11}$. 
# 
# Now we can substitute $n \equiv 2a \pmod{11}$ into 
# $3n \equiv 2 \pmod{11}$ to get 
# $3(2a) \equiv 2 \pmod{11}$. 
# 
# Simplifying this gives $6a \equiv 2 \pmod{11}$, 
# which is equivalent to $6a \equiv 10 \pmod{11}$. 
# 
# Now we can use the fact that $6 \equiv -5 \pmod{11}$ 
# to rewrite this as $-5a \equiv 10 \pmod{11}$. 
# 
# Adding 5 to both sides gives $a \equiv 8 \pmod{11}$. 
# 
# Since $n \equiv 2a \pmod{11}$, we can substitute 
# $a \equiv 8 \pmod{11}$ into $n \equiv 2a \pmod{11}$ 
# to get $n \equiv 2(8) \pmod{11}$. 
# 
# Simplifying this gives $n \equiv 16 \pmod{11}$. 
# 
# Since $n \equiv 16 \pmod{11}$, we know that 
# $n \equiv 5 \pmod{11}$, which means that 
# $n \equiv 5 \pmod{11}$ is the smallest 
# non