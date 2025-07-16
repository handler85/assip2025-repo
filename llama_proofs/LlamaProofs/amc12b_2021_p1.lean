-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- How many integer values of $x$ satisfy $|x|<3\pi$?

$\textbf{(A)} ~9 \qquad\textbf{(B)} ~10 \qquad\textbf{(C)} ~18 \qquad\textbf{(D)} ~19 \qquad\textbf{(E)} Show that it is \textbf{(D)} ~19.-/
theorem amc12b_2021_p1 (S : Finset ℤ) (h₀ : ∀ x : ℤ, x ∈ S ↔ ↑(abs x) < 3 * Real.pi) :
    S.card = 19 := by


/- 
This is a solution to AMC12B 2021 problem 1. 
The problem is to find the number of integer values of $x$ satisfying $|x|<3\pi$.

The solution is based on the following idea: 
We can write $|x|<3\pi$ as $x^2<9\pi^2$. 
Since $x^2$ is always nonnegative, we can rewrite this inequality as $x^2-9\pi^2<0$. 
This inequality defines a circle centered at $(0,9\pi^2)$ with radius $\sqrt{9\pi^2}$. 
The number of integer points inside this circle is the number of integer values of $x$ satisfying $|x|<3\pi$.

The key observation is that the circle centered at $(0,9\pi^2)$ with radius $\sqrt{9\pi^2}$ is contained in the rectangle $[0,9\pi^2]\times[0,9\pi^2]$. 
This means that the number of integer points inside the circle is equal to the number of integer points inside the rectangle minus the number of integer points outside the circle.

The number of integer points inside the rectangle $[0,9\pi^2]\times[0,9\pi^2]$ is $(9\pi^2+1)^2$. 
The number of integer points outside the circle is equal to the number of integer points on the circle minus the number of integer points inside the circle. 
The number of integer points on the circle is equal to the number of integer points on the circle centered at $(0,9\pi^2)$ with radius $\sqrt{9\pi^2}$. 
The number of integer points on the circle centered at $(0,9\pi^2)$ with radius $\sqrt{9\pi^2}$ is equal to the number of integer points on the circle centered at $(0,0)$ with radius $\sqrt{9\pi^2}$. 
The number of integer points on the circle centered at $(0,0)$ with radius $\sqrt{9\pi^2}$ is equal to the number of integer points on the circle centered at $(0,0)$ with radius $\sqrt{9\pi^2}$. 
The number of integer points on the circle centered at $(0,0)$ with radius $\sqrt{9\pi^2