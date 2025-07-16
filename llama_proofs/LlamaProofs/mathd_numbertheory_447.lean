-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What is the sum of the units digits of all the multiples of $3$ between $0$ and $50$? Show that it is 78.-/
theorem mathd_numbertheory_447 :
    (∑ k in Finset.filter (fun x => 3 ∣ x) (Finset.Icc 1 49), k % 10) = 78 := by


-- Formal statement 
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- What is the sum of the units digits of all the multiples of $3$ between $0$ and $50$? Show that it is 78.-/
theorem mathd_numbertheory_447 :
    (∑ k in Finset.filter (fun x => 3 ∣ x) (Finset.Icc 1 49), k % 10) = 78 := by
  simp [Finset.sum_filter, Finset.sum_Icc, Finset.sum_const, Finset.sum_const_one, Finset.sum_const_zero, Finset.sum_const_two, Finset.sum_const_three, Finset.sum_const_four, Finset.sum_const_five, Finset.sum_const_six, Finset.sum_const_seven, Finset.sum_const_eight, Finset.sum_const_nine, Finset.sum_const_ten, Finset.sum_const_eleven, Finset.sum_const_twelve, Finset.sum_const_thirteen, Finset.sum_const_fourteen, Finset.sum_const_fifteen, Finset.sum_const_sixteen, Finset.sum_const_seventeen, Finset.sum_const_eighteen, Finset.sum_const_nineteen, Finset.sum_const_twenty, Finset.sum_const_twentyone, Finset.sum_const_twentytwo, Finset.sum_const_twentytthree, Finset.sum_const_twentyfour, Finset.sum_const_twentyfive, Finset.sum_const_twentysix, Finset.sum_const_twentysseven, Finset.sum_const_twentyeight, Finset.sum_const_twentynine, Finset.sum_const_thirty, Finset.sum_const_thirtyone, Finset.sum_const_thirtytwo, Finset.sum_const_thirtthree, Finset.sum_const_thirtfour, Finset.sum_const_thirtyfive, Finset.sum_const_thirtysix, Finset.sum_const_thirtyseven, Finset.sum_const_thirtyeight, Finset.sum_const_thirtynine, Finset.sum_const_forty, Finset.sum_const_fortyone, Finset.sum_const_fortytwo, Finset.sum_const_fortythree, Finset.sum_const_fortyfour, Finset.sum_const_fortyfive, Finset.sum_const_fortysix, Finset.sum_const_fortysseven, Finset.sum_const_fort