import Mathlib.Analysis.Convex.Hull

class MonadAlt (m : Type u → Type v) : Type (max (u + 1) v)
  extends Monad m
  where
    alt : m a → m a → m a
    alt_assoc : Std.Associative (α := m a) alt
    alt_comm : Std.Commutative (α := m a) alt
    alt_idemp : Std.IdempotentOp (α := m a) alt
    comp_distr_left : ∀ (p q : m a) (k : a → m a),
      Eq
      (do
        let x ← alt p q
        k x) (k x)

class MonadProb (m : Type u → Type v) : Type (max (u + 1) v)
  extends Monad m
  where
    alt : m a → m a → m a
    alt_assoc : Std.Associative (α := m a) alt
