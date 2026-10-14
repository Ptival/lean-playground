import Mathlib.CategoryTheory.Category.Basic
-- import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types

-- Unit type with a top hat and a mustache
inductive Proxy (obj : Type) where | MkProxy
class Monoid (obj : Type) where

instance [Monoid obj] : CategoryTheory.Category (Proxy obj) where
  Hom Proxy.MkProxy _ := obj
  id _ := by sorry
  comp g f := by sorry
  id_comp f := by sorry
  comp_id f := by sorry
  assoc := by sorry
