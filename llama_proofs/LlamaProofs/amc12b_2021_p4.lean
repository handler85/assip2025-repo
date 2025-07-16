-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Ms. Blackwell gives an exam to two classes. The mean of the scores of the students in the morning class is $84$, and the afternoon class's mean score is $70$. The ratio of the number of students in the morning class to the number of students in the afternoon class is $\frac{3}{4}$. What is the mean of the scores of all the students?

$\textbf{(A)} ~74 \qquad\textbf{(B)} ~75 \qquad\textbf{(C)} ~76 \qquad\textbf{(D)} ~77 \qquad\textbf{(E)} Show that it is \textbf{(C)} ~76.-/
theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) := by


# Formal statement 
# 
# The problem statement is given in the problem description. 
# 
# # Solution 
# 
# # 
# # The problem is to find the mean of the scores of all the students. 
# 
# # The mean of the scores of the students in the morning class is $84$, 
# # and the afternoon class's mean score is $70$. 
# # The ratio of the number of students in the morning class to the number 
# # of students in the afternoon class is $\frac{3}{4}$. 
# 
# # We can start by finding the number of students in each class. 
# # Let $m$ be the number of students in the morning class, 
# # and $a$ be the number of students in the afternoon class. 
# # We know that $\frac{m}{a} = \frac{3}{4}$, 
# # so $m = \frac{3}{4}a$. 
# 
# # We also know that the mean of the scores of the students in the 
# # morning class is $84$, 
# # so $\frac{84m}{m} = 84$. 
# # Similarly, 
# # $\frac{70a}{a} = 70$. 
# 
# # Now we can find the total number of students, 
# # which is $m + a$. 
# # We can also find the total score, 
# # which is $84m + 70a$. 
# 
# # Finally, 
# # we can find the mean of the scores of all the students, 
# # which is $\frac{84m + 70a}{m + a}$. 
# 
# # We can simplify this expression 
# # to $\frac{84\left(\frac{3}{4}a\right) + 70a}{\frac{3}{4}a + a}$. 
# # We can simplify this further 
# # to $\frac{84\left(\frac{3}{4}a\right) + 70a}{\frac{3}{4}a + a}$. 
# # We can simplify this further 
# # to $\frac{84\left(\frac{3}{4}a\right) + 70a}{\frac{3}{4}a + a}$. 
# # We can simplify this further 
#