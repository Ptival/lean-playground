inductive ITE where
| ITEFalse
| ITETrue
-- ⟦ITETest n t f⟧ ≡ v[n] ? ⟦t⟧ : ⟦f⟧
| ITETest : Nat → ITE → ITE → ITE

def is_true (n : Nat) : ITE := .ITETest n .ITETrue .ITEFalse
def is_false (n : Nat) : ITE := .ITETest n .ITEFalse .ITETrue

partial def ite_and (a b : ITE) : ITE :=
  match a, b with
  | .ITEFalse, _ => .ITEFalse
  | _, .ITEFalse => .ITEFalse
  | .ITETrue, _ => b
  | _, .ITETrue => a
  | .ITETest n1 t1 f1, .ITETest n2 t2 f2 =>
    match compare n1 n2 with
    | .lt => .ITETest n1 (ite_and t1 b) (ite_and f1 b)
    | .gt => .ITETest n2 (ite_and a t2) (ite_and a f2)
    | .eq => .ITETest n1 (ite_and t1 t2) (ite_and f1 f2)

#eval ite_and (is_true 3) (is_false 1)

inductive AX where
| AXFalse
| AXTrue
-- ⟦AXNode x a b⟧ ≡ v[x].a + b
| AXNode : Nat → AX → AX → AX

def axNode (n : Nat) (l : AX) (r : AX) : AX :=
  match l with
  | .AXFalse => r
  | _ => .AXNode n l r

def axEval (env : Nat → Bool) (a : AX) : Bool :=
  match a with
  | .AXFalse => false
  | .AXTrue => true
  | .AXNode x a b => env x && axEval env a ≠ axEval env b

def axNeg (a : AX) : AX :=
  match a with
  | .AXFalse => .AXTrue
  | .AXTrue => .AXFalse
  -- ~(ax + b)
  | .AXNode x a b => .AXNode x a (axNeg b)

def axXor (l r : AX) : AX :=
  match l, r with
  | .AXFalse, _ => r
  | _, .AXFalse => l
  | .AXTrue, _ => axNeg r
  | _, .AXTrue => axNeg l
  | .AXNode x a b, .AXNode y c d =>
    match compare x y with
    | .lt => .AXNode x a (axXor b r)
    | .gt => .AXNode y c (axXor l d)
    | .eq => _
