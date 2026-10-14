import Mathlib.Data.List.AList
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.FixedPoints
import Mathlib.Order.Hom.Basic

abbrev Field := String
  -- deriving DecidableEq

abbrev Value := ℕ
  -- deriving DecidableEq

inductive TestPolarity where | TestEqual | TestNotEqual
  deriving DecidableEq

inductive BoolAlgebra where
  | And : BoolAlgebra → BoolAlgebra → BoolAlgebra
  | False
  | Neg : BoolAlgebra → BoolAlgebra
  | Or : BoolAlgebra → BoolAlgebra → BoolAlgebra
  | TestField : TestPolarity → Field → Value → BoolAlgebra
  | True
  deriving DecidableEq

-- A Kleene Algebra with tests
inductive KAT where
  | Assign : Field → Value → KAT
  | Drop
  | Sequence : KAT → KAT → KAT
  | Skip
  | Star : KAT → KAT
  | Test : BoolAlgebra → KAT
  | Union : KAT → KAT → KAT
  deriving DecidableEq

structure KATState where
  fields : AList (α := Field) (fun _ => Value)
  deriving DecidableEq

instance : ToString KATState where
  toString s := toString (AList.entries s.fields)

def initKATState : KATState where
  fields := ∅

def interpBA (ba : BoolAlgebra) (s : KATState) : Bool :=
  match ba with
  | .And a b => interpBA a s && interpBA b s
  | .False => false
  | .Neg a => !interpBA a s
  | .Or a b => interpBA a s || interpBA b s
  | .TestField .TestEqual f v => AList.lookup f s.fields == some v
  | .TestField .TestNotEqual f v => AList.lookup f s.fields != some v
  | .True => true

-- Single-state monad

class MonadNondet (m : Type → Type) [Monad m] where
  mzero : m a
  mplus : m a → m a → m a

class LiftNondet (t : (Type → Type) → Type → Type) where
  liftMplus : ∀ {m}, [Monad m] → (∀ {a}, m a → m a → m a) → (∀ {a}, t m a → t m a → t m a)

instance : LiftNondet (ReaderT r) where
  liftMplus mplus _ a b := fun r => mplus (ReaderT.run a r) (ReaderT.run b r)

instance : LiftNondet (StateT s) where
  liftMplus mplus _ a b := fun s => mplus (StateT.run a s) (StateT.run b s)

instance : MonadNondet List where
  mzero := []
  mplus ma mb := ma ++ mb

instance [Monad m] [MonadNondet m] : MonadNondet (ReaderT r m) where
  mzero := MonadNondet.mzero (m := m)
  mplus ma mb := LiftNondet.liftMplus (t := ReaderT r) MonadNondet.mplus ma mb

instance [Monad m] [MonadNondet m] : MonadNondet (StateT s m) where
  mzero := MonadNondet.mzero (m := m)
  mplus ma mb := LiftNondet.liftMplus (t := StateT s) MonadNondet.mplus ma mb

abbrev KATM := StateT KATState List

def minusOne (n : ℕ) := n - 1

def interpKATM (fuel : Nat) (e : KAT) : KATM Unit := do
  if fuel = 0
  then return ()
  else
    match e with
    | .Assign f v => modify $ fun s => { s with fields := s.fields.insert f v }
    | .Drop => []
    | .Sequence a b => do { interpKATM fuel a; interpKATM fuel b }
    | .Skip => pure ()
    | .Star e => MonadNondet.mplus (return ()) (do interpKATM fuel e; interpKATM (fuel - 1) (KAT.Star e))
    | .Test t => modify $ fun s => if interpBA t s then s else s
    | .Union a b => MonadNondet.mplus (interpKATM fuel a) (interpKATM fuel b)

def interpKAT (fuel : ℕ) (kat : KAT) (s : KATState) : List KATState :=
  List.map Prod.snd (StateT.run (interpKATM fuel kat) s)

def stateXis2 : KATState := { fields := AList.insert "x" 2 ∅ }

#eval! interpKAT 0 .Drop stateXis2
#eval! interpKAT 0 .Skip stateXis2
#eval! interpKAT 1 (.Union .Skip (.Assign "y" 3)) stateXis2
#eval! interpKAT 1 (.Star (.Union .Skip (.Assign "y" 3))) stateXis2

-- Collecting monad

structure FiniteSet (a : Type) where
  elems : List a
  instLE : LE a
  nodup : List.Nodup elems
  sorted : List.Sorted LE.le elems

instance [ToString a] : ToString (FiniteSet a) where
  toString s := "{" ++ String.mk (List.flatMap (β := Char) (fun a => (toString a).data) s.elems) ++ "}"

instance [instLE : LE a] : Singleton a (FiniteSet a) where
  singleton a := {
    elems := [a],
    instLE,
    nodup := by aesop,
    sorted := by aesop,
  }

-- abbrev KATCM := StateT (FiniteSet KATState) List

-- def extendSet [DecidableEq a] (f : a → FiniteSet a) (s : FiniteSet a) : FiniteSet a :=
--   {
--     elems := List.dedup (s.elems ++ List.flatMap (FiniteSet.elems ∘ f) s.elems),
--     instLE := s.instLE,
--     nodup := by aesop,
--     sorted := by _,
--   }

-- def interpKATCM (fuel : Nat) (e : KAT) : KATCM Unit := do
--   if fuel = 0
--   then return ()
--   else
--     match e with
--     | .Assign f v => do
--       modify $ extendSet (fun s => { elems := [{ s with fields := s.fields.insert f v }]})
--     | .Drop => []
--     | .Sequence a b => do interpKATCM fuel a; interpKATCM fuel b
--     | .Skip => pure ()
--     | .Star e => MonadNondet.mplus (return ()) (do interpKATCM fuel e; interpKATCM (fuel - 1) (KAT.Star e))
--     | .Test t => modify $ extendSet (fun s => { elems := if interpBA t s then [s] else []})
--     | .Union a b => MonadNondet.mplus (interpKATCM fuel a) (interpKATCM fuel b)

-- def interpKATC (fuel : Nat) (kat : KAT) (s : FiniteSet KATState) : List (FiniteSet KATState) :=
--   List.map Prod.snd (StateT.run (interpKATCM fuel kat) s)

-- #eval interpKATC 10 .Drop (singleton stateXis2)
-- #eval interpKATC 10 .Skip (singleton stateXis2)
-- #eval interpKATC 10 (.Union .Skip (.Assign "y" 3)) (singleton stateXis2)

-- -- Collecting fixpoint monad

-- abbrev KATCFM := StateT (FiniteSet KATState) List

-- def isSubsetOf [DecidableEq T] (a b : FiniteSet T) : Bool :=
--   match (FiniteSet.elems a, FiniteSet.elems b) with
--   | ([], _) => true
--   | (_, []) => false
--   | (List.cons ha ta, List.cons hb tb) => _

-- instance [LE a] : Preorder (FiniteSet a) where
--   le a b := isSubsetOf a b
--   le_refl := sorry
--   le_trans := sorry

-- def bump : OrderHom (FiniteSet KATState) (FiniteSet KATState) := sorry

-- def interpKATCFM (e : KAT) : KATCM Unit := do
--   match e with
--   | .Assign f v => do
--     modify $ extendSet (fun s => { elems := [{ s with fields := s.fields.insert f v }]})
--   | .Drop => []
--   | .Sequence a b => do interpKATCFM a; interpKATCFM b
--   | .Skip => pure ()
--   | .Star e => modify $ fun s => OrderHom.lfp
--       { toFun := _
--       , monotone := _
--       }
--   | .Test t => modify $ extendSet (fun s => { elems := if interpBA t s then [s] else []})
--   | .Union a b => MonadNondet.mplus (interpKATCFM a) (interpKATCFM b)
