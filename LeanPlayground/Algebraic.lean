import Mathlib

-- It is well-known that:
-- (a + b)² = a² + b² + 2ab
-- Let us witness it:

inductive sum (A B : Type) : Type where
| left (l : A)
| right (r : B)

abbrev factored A B := Bool → sum A B
abbrev expanded A B := sum (Bool → A) (sum (Bool → B) (Bool × A × B))

def square_of_sum_fw (f : factored A B) : expanded A B :=
  match (f true, f false) with
  | (.left l1, .left l2) => .left (fun b => if b then l1 else l2)
  | (.right r1, .right r2) => .right (.left (fun b => if b then r1 else r2))
  | (.left l1, .right r2) => .right (.right (true, l1, r2))
  | (.right r1, .left l2) => .right (.right (false, l2, r1))

def square_of_sum_bw (e : expanded A B) : factored A B :=
  match e with
  | .left f => .left ∘ f
  | .right (.left f) => .right ∘ f
  | .right (.right (flip, l, r)) => fun b =>
    if flip == b then .left l else .right r

theorem fw_of_bw : square_of_sum_fw (square_of_sum_bw e) = e := by
  unfold square_of_sum_bw square_of_sum_fw
  cases e with
  | left l =>
    simp
    ext x
    cases x <;> simp
  | right r =>
    cases r with
    | left l => aesop
    | right r => aesop

theorem bw_of_fw : square_of_sum_bw (square_of_sum_fw e) = e := by
  unfold square_of_sum_bw square_of_sum_fw
  cases H1 : e true with
  | left l1 =>
    cases H2 : e false with
    | left l2 => aesop
    | right r2 => aesop
  | right r =>
    cases H2 : e false with
    | left l2 => aesop
    | right r2 => aesop
