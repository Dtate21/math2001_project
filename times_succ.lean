import natural_numbers
import plus_assoc
import plus_comm

theorem times_succ ( m n : ℕ )
: m * n.succ = m + m * n := by
  induction m with
  | zero =>
    rfl
  | succ m ih =>
    unfold times
    rw [ih]
    unfold plus
    congr 1
    calc
      n + (m + m * n) = (n + m) + m * n := by rw [plus_assoc]
      _ = (m + n) + m * n := by rw [plus_comm n m]
      _ = m + (n + m * n) := by rw [plus_assoc]
