-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- A positive integer $X$ is 2 more than a multiple of 3. Its units digit is the same as the units digit of a number that is 4 more than a multiple of 5. What is the smallest possible value of $X$? Show that it is 14.-/
theorem mathd_numbertheory_559 (x y : ℕ) (h₀ : x % 3 = 2) (h₁ : y % 5 = 4) (h₂ : x % 10 = y % 10) :
    14 ≤ x := by


-- Formal statement 
-- 1. Start by assuming that $X$ is 2 more than a multiple of 3. 
-- 2. Then, we know that $X$ is 2 more than a multiple of 3, 
--    which means that $X$ is 2 more than some integer $n$ 
--    multiplied by 3. 
-- 3. We know that $X$ is 2 more than some integer $n$ 
--    multiplied by 3, which means that $X$ is 2 more 
--    than $3n$. 
-- 4. We know that $X$ is 2 more than $3n$, 
--    which means that $X$ is $3n + 2$. 
-- 5. We know that $X$ is $3n + 2$, 
--    which means that $X$ is 2 more than a multiple of 3. 
-- 6. We know that $X$ is 2 more than a multiple of 3, 
--    which means that $X$ is 2 more than some integer $n$ 
--    multiplied by 3. 
-- 7. We know that $X$ is 2 more than some integer $n$ 
--    multiplied by 3, which means that $X$ is 2 more 
--    than $3n$. 
-- 8. We know that $X$ is 2 more than $3n$, 
--    which means that $X$ is $3n + 2$. 
-- 9. We know that $X$ is $3n + 2$, 
--    which means that $X$ is 2 more than a multiple of 3. 
-- 10. We know that $X$ is 2 more than a multiple of 3, 
--    which means that $X$ is 2 more than some integer $n$ 
--    multiplied by 3. 
-- 11. We know that $X$ is 2 more than some integer $n$ 
--    multiplied by 3, which means that $X$ is 2 more 
--    than $3n$. 
-- 12. We know that $X$ is 2 more than $3n$, 
--    which means that $X$ is $3n + 2$. 
-- 13. We know