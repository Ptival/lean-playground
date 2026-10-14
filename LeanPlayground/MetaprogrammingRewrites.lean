-- open Lean PrettyPrinter Parser Elab
-- open Lean Elab Tactic Meta Quote

open Lean
open Lean.Elab.Tactic
open Lean.Elab.Tactic.Basic
open Lean.Meta

def a : TacticM Unit := do
  let lctx ← Lean.MonadLCtx.getLCtx
  return ()

-- def asNonEmptyList (e : Expr) : MetaM (Expr × Expr) := do
--   match e with
--   | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons _) _) hd) tl => return (hd, tl)
--   | _ => throwError "not a list, or empty"
