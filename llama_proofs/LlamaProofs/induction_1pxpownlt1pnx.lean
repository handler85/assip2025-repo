-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Show that for any real number $x$ and any natural number $n$, if $x > -1$, then $(1+nx)\leq (1+x)^n$.-/
theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by


-- Formal statement 
induction n using Nat.strongInductionOn

-- Induction hypothesis 
h : ∀ (n : ℕ), 1 + ↑n * x ≤ (1 + x) ^ n

-- Induction step 
show 1 + ↑(n + 1) * x ≤ (1 + x) ^ (n + 1) from 
calc 
    1 + ↑(n + 1) * x 
    = 1 + (1 + x) * (n + 1) 
    ≤ (1 + x) * (1 + x) ^ n 
    ≤ (1 + x) * (1 + x) ^ n 
    ≤ (1 + x) * (1 + x) ^ n 
    ≤ (1 + x) ^ (n + 1) 
    : 
    by 
    calc 
        1 + (1 + x) * (n + 1) 
        ≤ (1 + x) * (1 + x) ^ n 
        : 
        calc 
            1 + (1 + x) * (n + 1) 
            = 1 + (1 + x) * n + (1 + x) 
            ≤ 1 + (1 + x) * n + (1 + x) * n 
            ≤ 1 + (1 + x) * n + (1 + x) * n 
            ≤ (1 + x) * (1 + x) ^ n 
            : 
            calc 
                1 + (1 + x) * n + (1 + x) * n 
                ≤ (1 + x) * (1 + x) ^ n 
                : 
                calc 
                    1 + (1 + x) * n + (1 + x) * n 
                    ≤ (1 + x) * (1 + x) * (1 + x) ^ n 
                    : 
                    calc 
                        1 + (1 + x) * n + (1 + x) * n 
                        ≤ 1 + (1 + x) * n + (1 + x) * n 
                        ≤ 1 + (1 + x) * n + (1 + x) * n 
                        ≤ (1 + x) * (1 + x) * (1 + x) ^ n 
                        : 
                        calc 
                            1 + (1 + x) *