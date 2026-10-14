import Std.Data.HashSet.Basic
import Std.Tactic.Do
import Std.Tactic.Do.Syntax

open Std.Do

def pairsSumToZero (l : List Int) : Id Bool := do
  let mut seen : Std.HashSet Int := ∅

  for x in l do
    if -x ∈ seen then
      return true
    seen := seen.insert x

  return false

def countdown : StateM Nat Nat := do
  let n <- get
  if n = 0
    then pure 0
    else do
      put (n - 1)
      countdown

-- theorem pairsSumToZero_spec (l : List Int) :
--     ⦃⌜True⌝⦄ pairsSumToZero l ⦃⇓r => r = true ↔ l.ExistsPair (fun a b => a + b = 0)⦄
