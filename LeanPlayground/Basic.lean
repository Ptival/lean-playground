import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Even

theorem add_even_halves (h : Even n) : (n / 2) + (n / 2) = n :=
by
  obtain ⟨k, Hk⟩ := h
  rw [←Nat.two_mul] at Hk
  rw [Hk]
  rw [Nat.mul_div_right]
  rw [Nat.two_mul]
  simp

def foo (even: Even n) : Vector Nat n :=
  let v' := Vector.range (n/2)
  cast (congrArg (Vector Nat) (add_even_halves even)) (Vector.append v' v')
