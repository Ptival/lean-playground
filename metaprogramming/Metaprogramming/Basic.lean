import Lean

open Lean
open Lean.Elab.Tactic

def three : 1 + 2 = 2 + 1 := by rfl

-- #check TacticM

def myRewriteTactic : TacticM Unit := do
  let mvarId ← getMainGoal
  mvarId.withContext do
    for localDecl in ← getLCtx do
      let _ ← mvarId.replaceLocalDecl
        localDecl.fvarId
        (Expr.app (Expr.app (Expr.const ``Nat.add []) (Expr.lit (.natVal 1))) (Expr.lit (.natVal 2)))
        (Expr.const ``three [])

elab "myRewrite" : tactic => do
  myRewriteTactic

-- def goal (H : 1 + 2 = 2 + 1) : False := by
--   myRewrite

-- -- def asNonEmptyList (e : Expr) : MetaM (Expr × Expr) := do
-- --   match e with
-- --   | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons _) _) hd) tl => return (hd, tl)
-- --   | _ => throwError "not a list, or empty"
