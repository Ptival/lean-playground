import Batteries.Data.Rat.Basic
import Batteries.Data.AssocList

open Batteries

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

inductive SPP (K : Type k) (V : Type v) : Type (max k v) where
  | SPPLeaf : Rat → SPP K V
  | SPPNode :
      K →
      AssocList V (List (AssocList V (SPP K V))) →
  --                     ^^^^ this lists different possible assignments
  --               ^^^^ this list is for non-deterministic choice
  --  ^^^^ this lists different possible tests
      List (AssocList V (SPP K V)) →
  --        ^^^^ this lists different possible assignments
  --  ^^^^ this list is for non-deterministic choice
      SPP K V

abbrev KATState := AssocList String Nat

theorem AssocList_Mem_implies_sizeOf_lt [SizeOf V] (a : AssocList K V)
  : x ∈ a.toList → sizeOf x < sizeOf a := by
  induction a with
  | nil => simp
  | cons k v t IH =>
    intros A;
    cases A with
    | head =>
      simp
      cases t
      simp
      simp
      grind
    | tail _ mem =>
      simp
      apply Nat.lt_add_left
      apply IH
      apply mem

-- def notQuiteSizeOf [SizeOf K] [SizeOf V] : SPP K V → Nat
--   | .SPPLeaf p => 0
--   | .SPPNode key branches default =>
--       1
--         + (branches.toList.map
--             (fun (_, snd) => (snd.map (fun a => (a.toList.map (notQuiteSizeOf ·.snd)).sum)).sum)
--           ).sum
--         + (default.map (fun a => (a.toList.map (notQuiteSizeOf ·.snd)).sum)).sum
-- termination_by sp => sizeOf sp
-- decreasing_by
--   simp


def interpretSPP : SPP String Nat → KATState → List (Rat × KATState)
  | .SPPLeaf p => fun s => [(p, s)]
  | .SPPNode key branches default => fun s =>
    let interpretNonDeterministic
          (ndList : List (AssocList Nat (SPP String Nat)))
          (_forTermination : ndList = default ∨ (∃ x, (x, ndList) ∈ branches.toList))
          :=
      ndList.attach.flatMap (fun {val := nd, property := _Pnd} =>
        nd.toList.attach.flatMap (fun {val := assign, property := _Passign} =>
          (interpretSPP assign.snd s).map (fun (p, s) => (p, s.replace key assign.fst))
        )
      )
    match s.findEntryP? (fun k _ => key = k) with
    | none => interpretNonDeterministic default (.inl rfl)
    | some (_, val) =>
      match _SP : List.find? (fun (x, _) => x = val) branches.toList with
      | none => interpretNonDeterministic default (.inl rfl)
      | some (_x, sp) => interpretNonDeterministic sp (.inr ⟨_x, List.mem_of_find?_eq_some _SP⟩)
termination_by sp => sizeOf sp
decreasing_by
  simp
  apply Nat.lt_trans (m := sizeOf assign)
  cases assign; simp; grind
  apply Nat.lt_trans (m := sizeOf nd)
  apply sizeOf_Mem_AssocList_lt
  apply _Passign
  cases _forTermination with
  | inl _ =>
    subst ndList
    apply Nat.lt_add_left
    apply List.sizeOf_lt_of_mem _Pnd
  | inr E =>
    apply Nat.lt_add_right
    apply Nat.lt_add_left
    apply Nat.lt_trans (m := sizeOf ndList)
    apply List.sizeOf_lt_of_mem _Pnd
    let ⟨n, E⟩ := E
    apply Nat.lt_trans (m := sizeOf (n, ndList))
    simp
    grind
    apply sizeOf_Mem_AssocList_lt
    apply E

def spp1 : SPP String Nat :=
  .SPPNode "A"
    (List.toAssocList
      [ (1, [ List.toAssocList
                [ (1, SPP.SPPLeaf 0)
                , (2, .SPPNode "B" .nil [List.toAssocList [(2, .SPPLeaf (1/3))]])
                , (3, .SPPNode "B" .nil [List.toAssocList [(3, .SPPLeaf (2/3))]])
                ]
            ]
        )])
    []

def spp2 : SPP String Nat :=
  .SPPNode "A"
    (List.toAssocList
      [ (1, [ List.toAssocList
                [ (2, .SPPNode "B" .nil [List.toAssocList [(2, .SPPLeaf (1/3))]])
                , (3, .SPPNode "B" .nil [List.toAssocList [(3, .SPPLeaf (2/3))]])
                ]
            , List.toAssocList
                [ (2, .SPPNode "B" .nil [List.toAssocList [(2, .SPPLeaf (1/2))]])
                , (3, .SPPNode "B" .nil [List.toAssocList [(3, .SPPLeaf (1/2))]])
                ]
            ]
        )])
    []

-- Lean doesn't know how to display AssocLists, so transforming to List
def display (result : List (Rat × KATState)) : List (Rat × List (String × Nat)) :=
  result.map (fun (r, s) => (r, s.toList))

#eval! (display (interpretSPP spp1 .nil))
-- []
#eval! (display (interpretSPP spp1 (List.toAssocList [("A", 1)])))
-- [(0, [("A", 1)]), (1/3, [("A", 2)]), (2/3, [("A", 3)])]

#eval! (display (interpretSPP spp2 .nil))
-- []
#eval! (display (interpretSPP spp2 (List.toAssocList [("A", 1)])))
-- [(1/3, [("A", 2)]), (2/3, [("A", 3)]), (1/2, [("A", 2)]), (1/2, [("A", 3)])]
