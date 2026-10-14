import Batteries.Data.Rat.Basic
import Batteries.Data.AssocList
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Control.Combinators
import Mathlib.Data.List.Monad

open Batteries

deriving instance Repr for AssocList

instance : Functor (AssocList K) where
  map f := AssocList.mapVal (fun _ => f)

theorem sizeOf_AssocList_lt_sizeOf_List [SizeOf K] [SizeOf V] (a : AssocList K V) : sizeOf a ≤ sizeOf a.toList := by
  induction a
  simp
  simp
  grind

theorem sizeOf_AssocList_toList [SizeOf K] [SizeOf V] (a : AssocList K V)
  : sizeOf a.toList = sizeOf a + a.length := by
  induction a
  simp
  simp
  grind

theorem sizeOf_Mem_AssocList_lt [SizeOf K] [SizeOf V] (a : AssocList K V) : e ∈ a.toList → sizeOf e < sizeOf a := by
  induction a with
  | nil => simp
  | cons _ _ tail IH =>
    simp
    intros D
    cases D
    subst e
    simp
    cases tail; simp
    simp; grind
    grind

structure Distribution (A : Type a) : Type a where
  dist : List (Rat × A)
  deriving Repr

instance : Pure Distribution where
  pure a := { dist := [(1, a)] }
instance : Functor Distribution where
  map f a := { dist := a.dist.map (Prod.map id f) }
instance : Bind Distribution where
  bind a k := { dist := do
    let (p1, x) ← a.dist
    let (p2, y) ← (k x).dist
    return (p1 * p2, y)
  }
instance : Monad Distribution where

structure NondetDist (A : Type a) : Type a where
  nondet : List (Distribution A)
  deriving Repr

def distributeNondet (d : Distribution (List A)) : List (Distribution A) :=
  List.map Distribution.mk
    (d.dist.foldr
      (fun (p, xs) acc => do
        let x ← xs
        let xps ← acc
        return (List.append [(p, x)] xps))
      [[]])

def displayResult (result : List (Distribution A)) : List (List (Rat × A)) :=
  result.map (fun r => r.dist)

#eval! displayResult (distributeNondet
  { dist := [ (1/3, ["a", "b"])
            , (2/3, ["c", "d"])
            ] })

instance : Pure NondetDist where
  pure a := { nondet := [pure a] }
instance : Functor NondetDist where
  map f a := { nondet := a.nondet.map (Functor.map f) }
instance : Bind NondetDist where
  bind a k := { nondet := do
    -- Idea: go from List (Dist (List (Dist A)))
    let ldld := (Functor.map (fun x => (k x).nondet) a).nondet
    -- to:           List (List (Dist (Dist A)))
    let lldd := ldld.map distributeNondet
    -- then join to  List (Dist A)
    Functor.map joinM (joinM lldd)
  }
instance : Monad NondetDist where

instance : Mul (NondetDist A) where
  mul a b := { nondet := List.append a.nondet b.nondet }
instance : One (NondetDist A) where
  one := { nondet := [] }
instance : MulOneClass (NondetDist A) where
  one_mul := sorry
  mul_one := sorry
instance : Semigroup (NondetDist A) where
  mul_assoc := sorry
instance : Monoid (NondetDist A) where

inductive SymAction (K : Type k) (V : Type v) : Type (max k v) where
  | Leaf : Bool → SymAction K V
  | Node :
      K →
      AssocList V (NondetDist (AssocList V (SymAction K V))) →
      NondetDist (AssocList (Option V) (SymAction K V)) →
      SymAction K V
  deriving Repr

abbrev KATState := AssocList String Nat

def interpretSymAction : SymAction String Nat → KATState → List (Rat × KATState)
  | .Leaf .true => fun s => [(1, s)]
  | .Leaf .false => fun s => []
  | .Node key branches default => fun s =>
    let interpretDefault :=
      default.nondet.attach.flatMap (fun {val := nd, property := _P1} =>
        nd.dist.attach.flatMap (fun {val := (p, sa), property := _P2} =>
          sa.toList.attach.flatMap (fun {val := assign, property := _P3} =>
            (interpretSymAction assign.snd s).map (fun (q, s) =>
              match assign.fst with
              | .none => (p * q, s)
              | .some assign => (p * q, s.replace key assign)
            )
          )))
     let interpretNonDeterministic
          (ndList : NondetDist (AssocList Nat (SymAction String Nat)))
          (_forTermination : ∃ x, (x, ndList) ∈ branches.toList)
          :=
      ndList.nondet.attach.flatMap (fun {val := nd, property := _P1} =>
        nd.dist.attach.flatMap (fun {val := (p, sa), property := _P2} =>
          sa.toList.attach.flatMap (fun {val := assign, property := _P3} =>
            let s' := s.replace key assign.fst
            (interpretSymAction assign.snd s').map (fun (q, s) => (p * q, s))
            -- (interpretSymAction assign.snd s).map (fun (q, s) => (p * q, s.replace key assign.fst))
          )))
    match s.findEntryP? (fun k _ => key = k) with
    | none => interpretDefault
    | some (_, val) =>
      match _SP : List.find? (fun (x, _) => x = val) branches.toList with
      | none => interpretDefault
      | some (_x, sp) => interpretNonDeterministic sp ⟨_x, List.mem_of_find?_eq_some _SP⟩
termination_by sa => sizeOf sa
decreasing_by
  sorry
  sorry

def seqSymAction : SymAction String Nat → SymAction String Nat → SymAction String Nat
  | .Leaf .true, sa₂ => sa₂
  | .Leaf .false, sa₂ => .Leaf .false
  | sa₁, .Leaf .true => sa₁
  | sa₁, .Leaf .false => .Leaf .false
  | sa₁@(.Node k1 bs1 ds1), sa₂@(.Node k2 bs2 ds2) =>
    match H : compare k1 k2 with
    | .lt =>
      .Node k1
        (bs1.mapVal (fun _ => Functor.map (AssocList.mapVal (fun _ sa => seqSymAction sa sa₂))))
        (Functor.map (AssocList.mapVal (fun _ sa => seqSymAction sa sa₂)) ds1)
    | .gt =>
      .Node k2
        (bs2.mapVal (fun _ => Functor.map (AssocList.mapVal (fun _ sa => seqSymAction sa₁ sa))))
        (Functor.map (AssocList.mapVal (fun _ sa => seqSymAction sa₁ sa)) ds2)
    | .eq =>
      .Node k1
        (bs1.mapVal (fun _testedValue vasM => do
          let vas ← vasM
          List.prod (
            vas.toList.map (fun (vs, a) =>
              Functor.map (Functor.map (seqSymAction a))
                (
                  match _SP : List.find? ((fun n => n == vs) ∘ Prod.fst) bs2.toList with
                  | none => do
                    let vasi ← ds2
                    return List.toAssocList (List.flatMap (fun (k, v) =>
                      match k with
                      | .none => []
                      | .some k => [(k, v)]
                    ) (AssocList.toList vasi))
                  | some (_x, sp) => sp
                )))))
        (do
          let vas ← ds1
          List.prod (
            vas.toList.map (fun (vsO, a) =>
              match vsO with
              | .none => ds2
              | .some vs =>
                  Functor.map (Functor.map (seqSymAction a))
                    (
                      match _SP : List.find? ((fun n => n == vs) ∘ Prod.fst) bs2.toList with
                      | .none => ds2
                      | .some (_x, sp) => do
                          let vasi ← sp
                          return List.toAssocList
                            (List.flatMap (fun (k, v) => [(.some k, v)]) (AssocList.toList vasi))
                    ))))
termination_by sa₁ sa₂ => sizeOf sa₁ + sizeOf sa₂
decreasing_by
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry

-- Lean doesn't know how to display AssocLists, so transforming to List
def display (result : List (Rat × KATState)) : List (Rat × List (String × Nat)) :=
  result.map (fun (r, s) => (r, s.toList))

def drop : SymAction K V := .Leaf .false
def skip : SymAction K V := .Leaf .true

def defaultDrop : NondetDist (AssocList (Option V) (SymAction K V)) :=
  { nondet := [] }
def defaultSkip : NondetDist (AssocList (Option V) (SymAction K V)) :=
  { nondet := [ { dist := [ (1, List.toAssocList [(.none, skip)]) ] } ] }

def dropInDisguise : SymAction String Nat := .Node "A" .nil defaultDrop
def skipInDisguise : SymAction String Nat := .Node "A" .nil defaultSkip

#eval! (display (interpretSymAction dropInDisguise (List.toAssocList [("A", 1)])))
#eval! (display (interpretSymAction dropInDisguise (List.toAssocList [("A", 2)])))
#eval! (display (interpretSymAction dropInDisguise (List.toAssocList [("A", 3)])))

#eval! (display (interpretSymAction skipInDisguise (List.toAssocList [("A", 1), ("B", 2)])))
#eval! (display (interpretSymAction skipInDisguise (List.toAssocList [("A", 2), ("B", 2)])))
#eval! (display (interpretSymAction skipInDisguise (List.toAssocList [("A", 3), ("B", 2)])))

def skipSkip := seqSymAction skipInDisguise skipInDisguise
#eval! skipSkip
#eval! (display (interpretSymAction skipSkip (List.toAssocList [("A", 1), ("B", 2)])))
#eval! (display (interpretSymAction skipSkip (List.toAssocList [("A", 2), ("B", 2)])))
#eval! (display (interpretSymAction skipSkip (List.toAssocList [("A", 3), ("B", 2)])))

def dropSkip := seqSymAction dropInDisguise skipInDisguise
#eval! dropSkip
#eval! (display (interpretSymAction dropSkip (List.toAssocList [("A", 1), ("B", 2)])))
#eval! (display (interpretSymAction dropSkip (List.toAssocList [("A", 2), ("B", 2)])))
#eval! (display (interpretSymAction dropSkip (List.toAssocList [("A", 3), ("B", 2)])))

def skipDrop := seqSymAction skipInDisguise dropInDisguise
#eval! skipDrop
#eval! (display (interpretSymAction skipDrop (List.toAssocList [("A", 1), ("B", 2)])))
#eval! (display (interpretSymAction skipDrop (List.toAssocList [("A", 2), ("B", 2)])))
#eval! (display (interpretSymAction skipDrop (List.toAssocList [("A", 3), ("B", 2)])))

def single_option (k : (Nat × SymAction String Nat)) : NondetDist (AssocList Nat (SymAction String Nat)) :=
  { nondet := [ { dist := [(1, [k].toAssocList)] } ] }

-- if A ≡ 1, A ← 2, else skip
def ifAIsOneSetToTwoElseSkip : SymAction String Nat :=
  .Node "A" [ (1, single_option (2, skip)) ].toAssocList
            defaultSkip

-- if A ≡ 1, A ← 2, else drop
def ifAIsOneSetToTwoElseDrop : SymAction String Nat :=
  .Node "A" [ (1, single_option (2, skip)) ].toAssocList
            defaultDrop

#eval! (display (interpretSymAction ifAIsOneSetToTwoElseSkip [("A", 1)].toAssocList))
#eval! (display (interpretSymAction ifAIsOneSetToTwoElseSkip [("A", 2)].toAssocList))
#eval! (display (interpretSymAction ifAIsOneSetToTwoElseSkip [("A", 3)].toAssocList))

-- if A ≡ 2, A ← 3 else skip
def ifAIsTwoSetToThreeElseSkip : SymAction String Nat :=
  .Node "A" [(2, single_option (3, skip))].toAssocList
            defaultSkip

-- if A ≡ 2, A ← 3 else drop
def ifAIsTwoSetToThreeElseDrop : SymAction String Nat :=
  .Node "A" [(2, single_option (3, skip))].toAssocList
            defaultDrop

#eval! (display (interpretSymAction ifAIsTwoSetToThreeElseSkip [("A", 1)].toAssocList))
#eval! (display (interpretSymAction ifAIsTwoSetToThreeElseSkip [("A", 2)].toAssocList))
#eval! (display (interpretSymAction ifAIsTwoSetToThreeElseSkip [("A", 3)].toAssocList))

#eval! (seqSymAction ifAIsOneSetToTwoElseSkip ifAIsTwoSetToThreeElseSkip)
#eval! (seqSymAction ifAIsOneSetToTwoElseDrop ifAIsTwoSetToThreeElseSkip)
#eval! (seqSymAction ifAIsOneSetToTwoElseSkip ifAIsTwoSetToThreeElseDrop)
#eval! (seqSymAction ifAIsOneSetToTwoElseDrop ifAIsTwoSetToThreeElseDrop)

def dropOrSetAToOne : SymAction String Nat :=
  .Node "A" .nil { nondet := [{ dist := [ (1/2, [(.some 1, skip)].toAssocList)
                                        , (1/2, [(.none, drop)].toAssocList)
                                        ] }] }

#eval! (display (interpretSymAction dropOrSetAToOne [("A", 1)].toAssocList))


-- if A ≡ 1, A ← 2 ⊕{½} 3, else drop
def ifAIsOneSetToTwoOrThreeElseDrop : SymAction String Nat :=
  .Node "A"
    [ (1, { nondet := [ { dist := [ (1/2, List.toAssocList [(2, .Leaf .true)])
                                  , (1/2, List.toAssocList [(3, .Leaf .true)])
                                  ]} ] }) ].toAssocList
    defaultDrop

-- if A ≡ 2, A ← 3 ⊕{½} 4, else skip
def ifAIsTwoSetToThreeOrFourElseSkip : SymAction String Nat :=
  .Node "A"
    [ (2, { nondet := [ { dist := [ (1/2, List.toAssocList [(3, .Leaf .true)])
                                  , (1/2, List.toAssocList [(4, .Leaf .true)])
                                  ]} ] }) ].toAssocList
    defaultSkip

#eval! (display (interpretSymAction ifAIsOneSetToTwoOrThreeElseDrop [("A", 1)].toAssocList))
#eval! (display (interpretSymAction ifAIsOneSetToTwoOrThreeElseDrop [("A", 2)].toAssocList))
#eval! (display (interpretSymAction ifAIsOneSetToTwoOrThreeElseDrop [("A", 3)].toAssocList))

#eval! (display (interpretSymAction ifAIsTwoSetToThreeOrFourElseSkip [("A", 1)].toAssocList))
#eval! (display (interpretSymAction ifAIsTwoSetToThreeOrFourElseSkip [("A", 2)].toAssocList))
#eval! (display (interpretSymAction ifAIsTwoSetToThreeOrFourElseSkip [("A", 3)].toAssocList))

#eval! (seqSymAction ifAIsOneSetToTwoOrThreeElseDrop ifAIsOneSetToTwoOrThreeElseDrop)

#eval! (display (interpretSymAction
  (seqSymAction ifAIsOneSetToTwoOrThreeElseDrop ifAIsOneSetToTwoOrThreeElseDrop)
  [("A", 1)].toAssocList))

def sa1 : SymAction String Nat :=
  .Node "A"
    (List.toAssocList
      [ (1, { nondet :=
              [ { dist :=
                  [ (1/2, List.toAssocList [(2, .Leaf .true), (3, .Leaf .true)])
                  , (1/2, List.toAssocList [(4, .Leaf .true)]) ] }
              , { dist := [ (1, List.toAssocList []) ] }
              ]})
      , (2, { nondet :=
                [ { dist :=
                    [ (1/2, List.toAssocList [(2, .Leaf .true), (3, .Leaf .true)])
                    , (1/2, List.toAssocList [(4, .Leaf .true)]) ] }
                , { dist := [ (1, List.toAssocList []) ] }
                ]})
      ])
    { nondet := [] }

def sa2 : SymAction String Nat :=
  .Node "A"
    (List.toAssocList
      [ (1, { nondet :=
              [ { dist :=
                  [ (1/3, List.toAssocList [(2, .Leaf .true), (3, .Leaf .true)])
                  , (2/3, List.toAssocList [(4, .Leaf .true)]) ] }
              , { dist := [ (1, List.toAssocList []) ] } ]})
      , (2, { nondet := [ { dist := [ (1, List.toAssocList [(1, .Leaf .true)]) ]} ]})
      ])
    { nondet := [] }

#eval! (display (interpretSymAction sa1 .nil))
#eval! (display (interpretSymAction sa1 (List.toAssocList [("A", 1)])))

#eval! (display (interpretSymAction sa2 .nil))
#eval! (display (interpretSymAction sa2 (List.toAssocList [("A", 1)])))


#eval! (display (interpretSymAction (seqSymAction sa1 sa2) (List.toAssocList [("A", 1)])))
#eval! (display (interpretSymAction (seqSymAction sa2 sa1) (List.toAssocList [("A", 1)])))

















-- theorem AssocList_Mem_implies_sizeOf_lt [SizeOf V] (a : AssocList K V)
--   : x ∈ a.toList → sizeOf x < sizeOf a := by
--   induction a with
--   | nil => simp
--   | cons k v t IH =>
--     intros A;
--     cases A with
--     | head =>
--       simp
--       cases t
--       simp
--       simp
--       grind
--     | tail _ mem =>
--       simp
--       apply Nat.lt_add_left
--       apply IH
--       apply mem

-- -- def notQuiteSizeOf [SizeOf K] [SizeOf V] : SymAction K V → Nat
-- --   | .Leaf p => 0
-- --   | .Node key branches default =>
-- --       1
-- --         + (branches.toList.map
-- --             (fun (_, snd) => (snd.map (fun a => (a.toList.map (notQuiteSizeOf ·.snd)).sum)).sum)
-- --           ).sum
-- --         + (default.map (fun a => (a.toList.map (notQuiteSizeOf ·.snd)).sum)).sum
-- -- termination_by sp => sizeOf sp
-- -- decreasing_by
-- --   simp


-- def interpretSPP : SymAction String Nat → KATState → List (Rat × KATState)
--   | .Leaf p => fun s => [(p, s)]
--   | .Node key branches default => fun s =>
--     let interpretNonDeterministic
--           (ndList : List (AssocList Nat (SymAction String Nat)))
--           (_forTermination : ndList = default ∨ (∃ x, (x, ndList) ∈ branches.toList))
--           :=
--       ndList.attach.flatMap (fun {val := nd, property := _Pnd} =>
--         nd.toList.attach.flatMap (fun {val := assign, property := _Passign} =>
--           (interpretSPP assign.snd s).map (fun (p, s) => (p, s.replace key assign.fst))
--         )
--       )
--     match s.findEntryP? (fun k _ => key = k) with
--     | none => interpretNonDeterministic default (.inl rfl)
--     | some (_, val) =>
--       match _SP : List.find? (fun (x, _) => x = val) branches.toList with
--       | none => interpretNonDeterministic default (.inl rfl)
--       | some (_x, sp) => interpretNonDeterministic sp (.inr ⟨_x, List.mem_of_find?_eq_some _SP⟩)
-- termination_by sp => sizeOf sp
-- decreasing_by
--   simp
--   apply Nat.lt_trans (m := sizeOf assign)
--   cases assign; simp; grind
--   apply Nat.lt_trans (m := sizeOf nd)
--   apply sizeOf_Mem_AssocList_lt
--   apply _Passign
--   cases _forTermination with
--   | inl _ =>
--     subst ndList
--     apply Nat.lt_add_left
--     apply List.sizeOf_lt_of_mem _Pnd
--   | inr E =>
--     apply Nat.lt_add_right
--     apply Nat.lt_add_left
--     apply Nat.lt_trans (m := sizeOf ndList)
--     apply List.sizeOf_lt_of_mem _Pnd
--     let ⟨n, E⟩ := E
--     apply Nat.lt_trans (m := sizeOf (n, ndList))
--     simp
--     grind
--     apply sizeOf_Mem_AssocList_lt
--     apply E

-- def sa1 : SymAction String Nat :=
--   .Node "A"
--     (List.toAssocList
--       [ (1, [ List.toAssocList
--                 [ (1, SymAction.Leaf 0)
--                 , (2, .Node "B" .nil [List.toAssocList [(2, .Leaf (1/3))]])
--                 , (3, .Node "B" .nil [List.toAssocList [(3, .Leaf (2/3))]])
--                 ]
--             ]
--         )])
--     []

-- def sa2 : SymAction String Nat :=
--   .Node "A"
--     (List.toAssocList
--       [ (1, [ List.toAssocList
--                 [ (2, .Node "B" .nil [List.toAssocList [(2, .Leaf (1/3))]])
--                 , (3, .Node "B" .nil [List.toAssocList [(3, .Leaf (2/3))]])
--                 ]
--             , List.toAssocList
--                 [ (2, .Node "B" .nil [List.toAssocList [(2, .Leaf (1/2))]])
--                 , (3, .Node "B" .nil [List.toAssocList [(3, .Leaf (1/2))]])
--                 ]
--             ]
--         )])
--     []

-- -- Lean doesn't know how to display AssocLists, so transforming to List
-- def display (result : List (Rat × KATState)) : List (Rat × List (String × Nat)) :=
--   result.map (fun (r, s) => (r, s.toList))

-- #eval! (display (interpretSPP sa1 .nil))
-- -- []
-- #eval! (display (interpretSPP sa1 (List.toAssocList [("A", 1)])))
-- -- [(0, [("A", 1)]), (1/3, [("A", 2)]), (2/3, [("A", 3)])]

-- #eval! (display (interpretSPP sa2 .nil))
-- -- []
-- #eval! (display (interpretSPP sa2 (List.toAssocList [("A", 1)])))
-- -- [(1/3, [("A", 2)]), (2/3, [("A", 3)]), (1/2, [("A", 2)]), (1/2, [("A", 3)])]
