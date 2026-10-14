import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types

class Magma (obj : Type) where
  op : obj → obj → obj

class Monoid (obj : Type) extends Magma obj where
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  id_elt : obj
  id_l : ∀ e, op id_elt e = e
  id_r : ∀ e, op e id_elt = e

-- Unit type with a top hat and a mustache.
inductive Proxy (obj : Type) where
  | MkProxy : Proxy obj

-- A monoid can be viewed as a category, with a single object (using `Proxy obj` to stand for the
-- singular object corresponding to `obj`).
instance monoidAsCategory [Monoid obj] : CategoryTheory.Category (Proxy obj) where
  Hom | .MkProxy, .MkProxy => obj
  id | .MkProxy => Monoid.id_elt
  comp g f := Magma.op g f
  id_comp f := by
    simp
    rw [Monoid.id_l]
  comp_id f := by
    simp
    rw [Monoid.id_r]
  assoc f g h := by
    simp
    rw [Monoid.assoc]

-- First version of finite state machine, with just an alphabet, a state space, and a `next`
-- function.  Might add a start state, and maybe accept states, later.
structure FSM (Alphabet : Type) (State : Type) where
  next_state : Alphabet → State → State

-- Building towards viewing a FSM as a functor from the free monoid over its alphabet to the types
-- category.  For this, we first need to define the free monoid construction.
instance freeMonoid (obj : Type) : Monoid (List obj) where
  op := List.append
  id_elt := List.nil
  assoc := by simp
  id_l := by simp
  id_r := by simp

-- Iterated `next_state` over a string from `Alphabet`.
def nexts_state (fsm : FSM Alphabet State) (string : List Alphabet) : State → State :=
  match string with
  | List.nil => id
  | List.cons h t => nexts_state fsm t ∘ fsm.next_state h

theorem nexts_state_append (fsm : FSM Alphabet State) (s1 s2 : List Alphabet)
  : nexts_state fsm (List.append s1 s2) = nexts_state fsm s2 ∘ nexts_state fsm s1 := by
  induction s1 with
  | nil => rfl
  | cons h t IH =>
    simp [nexts_state]
    unfold_projs
    rw [IH]
    rfl

-- Now we can finally view a FSM as a functor from the free monoid.
def fsmAsFunctor (fsm : FSM Alphabet State) : CategoryTheory.Functor (Proxy (List Alphabet)) Type where
  obj _ := State
  map l := nexts_state fsm l
  map_id x := by rfl
  map_comp := by
    simp
    intros _ _ _ f g
    rw [CategoryTheory.types_comp]
    unfold_projs
    rw [nexts_state_append]

-- And we can interpret a functor from the free monoid over some alphabet to types as a FSM
-- whose state type is the image of the single object in the monoid category.
def functorAsFSM
  (F : CategoryTheory.Functor (Proxy (List Alphabet)) Type)
  : FSM Alphabet (F.obj Proxy.MkProxy) where
  next_state symbol := @F.map Proxy.MkProxy Proxy.MkProxy [symbol]

-- For instance, the Wikipedia coin-operated turnstile
inductive TurnstileAlphabet where | Coin | Push
inductive TurnstileState where | Locked | Unlocked

def coinOperatedTurnstileFSM : FSM TurnstileAlphabet TurnstileState where
  next_state
    | .Coin, .Locked => .Unlocked
    | .Push, .Locked => .Locked
    | .Coin, .Unlocked => .Unlocked
    | .Push, .Unlocked => .Locked

def coinOperatedTurnstileFunctor := fsmAsFunctor coinOperatedTurnstileFSM

def coinOperatedTurnstileFSMRoundtrip := functorAsFSM coinOperatedTurnstileFunctor

#reduce (FSM.next_state coinOperatedTurnstileFSMRoundtrip .Coin .Locked)
#reduce (FSM.next_state coinOperatedTurnstileFSMRoundtrip .Push .Locked)
#reduce (FSM.next_state coinOperatedTurnstileFSMRoundtrip .Coin .Unlocked)
#reduce (FSM.next_state coinOperatedTurnstileFSMRoundtrip .Push .Unlocked)
