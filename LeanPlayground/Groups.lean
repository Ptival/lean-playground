import Mathlib
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.SemidirectProduct

abbrev C2 := Multiplicative (Fin 2)
instance : Mul C2 := Multiplicative.mul
abbrev C3 := Multiplicative (Fin 3)
instance : Mul C3 := Multiplicative.mul

/-   λx ⇒ x . y . x⁻¹   -/

/-
φ sense the generator of C3 to a 3-cycle

V4 = {1, a, b, c} with a² = b² = c² = 1, and ab = c
C3 = t with t³ = 1

φ(id) = id

φ(t) : a ↦ b
       b ↦ c
       c ↦ a

φ(t²) = φ(t) ⋆ φ(t)

-/

def thing (x : C2) : C2 :=
  match x with
  | ⟨0, _⟩ => x
  | ⟨1, _⟩ => _

def φ' (x : C3) : MulAut (C2 × C2) :=
  { toFun :=
      match x with
      | ⟨0, _⟩ => id
      | ⟨1, _⟩ => (y⁻¹, z)
      | ⟨2, _⟩ => (y, z⁻¹)
  , invFun := fun (y, z) =>
      match x with
      | ⟨0, _⟩ => (y, z)
      | ⟨1, _⟩ => (y⁻¹, z)
      | ⟨2, _⟩ => (y, z⁻¹)
  , left_inv :=
      match x with
      | ⟨0, _⟩ => by simp; trivial
      | ⟨1, _⟩ => by simp; trivial
      | ⟨2, _⟩ => by simp; trivial
  , right_inv :=
      match x with
      | ⟨0, _⟩ => by simp; trivial
      | ⟨1, _⟩ => by simp; trivial
      | ⟨2, _⟩ => by simp; trivial
  , map_mul' :=
      match x with
      | ⟨0, _⟩ => by simp
      | ⟨1, _⟩ => by simp; trivial
      | ⟨2, _⟩ => by simp; trivial
  }

  -- x * y * x⁻¹
  -- match x with
  -- | ⟨0, _⟩ => _
  -- | ⟨1, _⟩ => _
  -- | ⟨2, _⟩ => _
  -- match y.1, y.2 with
  -- | ⟨0, _⟩, ⟨0, _⟩ => 1
  -- | ⟨0, _⟩, ⟨1, _⟩ => 1
  -- | ⟨1, _⟩, ⟨0, _⟩ => 1
  -- | ⟨1, _⟩, ⟨1, _⟩ => 1

-- def c2_0 : C2 := ⟨0, by grind⟩
-- def c2_1 : C2 := ⟨1, by grind⟩

-- def c3_0 : C3 := ⟨0, by grind⟩
-- def c3_1 : C3 := ⟨1, by grind⟩
-- def c3_2 : C3 := ⟨2, by grind⟩

-- #eval (c2_0 * c2_0)
-- #eval (c2_0 * c2_1)
-- #eval (c2_1 * c2_0)
-- #eval (c2_1 * c2_1)
-- #eval φ' (c2_1, c2_1)
-- #eval ((c2_1, c2_1) * (c2_1, c2_1))
-- #eval φ' ((c2_1, c2_1) * (c2_1, c2_1))

def φ : C3 →* MulAut (C2 × C2) :=
  { toFun := φ'
  , map_one' := rfl
  , map_mul' := fun x y =>
      match x, y with
      | ⟨0, _⟩, ⟨0, _⟩ => rfl
      | ⟨0, _⟩, ⟨1, _⟩ => rfl
      | ⟨0, _⟩, ⟨2, _⟩ => rfl
      | ⟨1, _⟩, ⟨0, _⟩ => rfl
      | ⟨1, _⟩, ⟨1, _⟩ => rfl
      | ⟨1, _⟩, ⟨2, _⟩ => rfl
      | ⟨2, _⟩, ⟨0, _⟩ => rfl
      | ⟨2, _⟩, ⟨1, _⟩ => rfl
      | ⟨2, _⟩, ⟨2, _⟩ => rfl
  }

theorem bensGroup [Group G] (x y : G)
  (Hx : x*x*x = 1)
  (Hy : y*y = 1)
  (Hxy : (x*y)^3 = 1)
  :
  Nonempty (G ≃* (C2 × C2) ⋊[φ] C3)
  := by
  constructor
  refine
    { toFun := by
        sorry
    , invFun := by
        sorry
    , map_mul' := by
        sorry
    , left_inv := by
        sorry
    , right_inv := by
        sorry
    }
