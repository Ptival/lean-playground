import Lean.Meta.Basic

theorem test (a b : ℕ) : a < b := by
  liftMetaM do
    let goal ← Lean.Elab.Tactic.getMainTarget
    match goal with
    | (``LE.le, #[_, _, lhs, rhs]) => error "yes"
  rfl

-- open Lean PrettyPrinter Parser Elab

-- open Delaborator SubExpr in
-- @[delab LLProp]
-- def stateFnsDelab : Delab :=
--   whenNotPPOption getPPExplicit <| withMDataExpr do
--     `("???")
--     -- if (← getExpr).isAppOfArity ``LLProp 1 then
--     --   `("???")
--     -- else
--     --   failure


-- section

-- open Lean Elab Tactic Meta Quote Term

-- def asNonEmptyList (e : Expr) : MetaM (Expr × Expr) := do
--   match e with
--   | Expr.app (Expr.app (Expr.app (Expr.const ``List.cons _) _) hd) tl => return (hd, tl)
--   | _ => throwError "not a list, or empty"

-- end

-- From:
-- [X, X ⊸ Y, ...]
-- To:
-- [Y, ...]
-- elab "applyLollipop" : tactic => unsafe do
--   let goal ← Lean.Elab.Tactic.getMainTarget
--   match goal with
--   | Expr.app (Expr.app (Expr.const ``LL _) Γ) _ =>
--     let (itemToSpend, Γ₁) ← asNonEmptyList Γ
--     let (lollipopExpr, _) ← asNonEmptyList Γ₁
--     match lollipopExpr with
--     | Expr.app (Expr.app (Expr.const ``lollipop _) lollipopLHSExpr) _ =>
--       if itemToSpend == lollipopLHSExpr
--         then do evalTactic (← `(tactic| apply applyLollipop))
--         else logInfo s!"Your first context item ({itemToSpend}) should be matching the next item's lollipop LHS ({lollipopLHSExpr})"
--     | _ => throwError "Your second context item"
--   | _ => throwError "no match (not a LL goal?)"


-- def chooseLeft :
--     A :: Γ ⊢ Goal →
--   -------------------
--   (A & B) :: Γ ⊢ Goal
--   := by

-- Sadly, this does not seem to work for `cases`
macro_rules
  | `(match $e:term with
      | $a ⅋ $b => $rhs) =>
    `(match $e:term with
      | LLProp.MulDisj $a $b => $rhs)

  | `(fun
      | $a ⅋ $b => $rhs) =>
    `(fun
      | LLProp.MulDisj $a $b => $rhs)
