-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Show that there exist real numbers $a$ and $b$ such that $a$ is irrational, $b$ is irrational, and $a^b$ is rational.-/
theorem algebra_others_exirrpowirrrat : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by


  /- First, we need to show that there exist real numbers $a$ and $b$ such that $a$ is irrational, $b$ is irrational, and $a^b$ is rational.-/
  /- We start by considering the set $S$ of all real numbers $x$ such that $x^2$ is rational.-/
  let S : Set ℚ := {x : ℚ | x ^ 2 ∈ ℚ}

  /- We claim that $S$ is non-empty.-/
  have S_nonempty : S.Nonempty := by
    /- To see this, note that $2$ is clearly in $S$, since $2^2 = 4$ is rational.-/
    /- Now, suppose $x \in S$.  We claim that $-x \in S$ as well.-/
    /- Indeed, $(-x)^2 = x^2$, which is rational since $x \in S$.  Hence, $-x \in S$.-/
    /- Now, suppose $x \in S$.  We claim that $x + 1 \in S$ as well.-/
    /- Indeed, $(x + 1)^2 = x^2 + 2x + 1$, which is rational since $x \in S$.  Hence, $x + 1 \in S$.-/
    /- Now, suppose $x \in S$.  We claim that $x - 1 \in S$ as well.-/
    /- Indeed, $(x - 1)^2 = x^2 - 2x + 1$, which is rational since $x \in S$.  Hence, $x - 1 \in S$.-/
    /- Now, suppose $x \in S$.  We claim that $x \cdot 2 \in S$ as well.-/
    /- Indeed, $(x \cdot 2)^2 = 4x^2$, which is rational since $x \in S$.  Hence, $x \cdot 2 \in S$.-/
    /- Now, suppose $x \in S$.  We claim that $x / 2 \in S$ as well.-/
    /- Indeed, $(x / 2)^2 = x^2 / 4$, which is rational since $x \in S$.  Hence, $x /