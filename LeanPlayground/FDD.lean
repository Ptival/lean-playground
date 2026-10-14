import Init.Prelude

def foldWithMembership (l : List α) (init : β) (f : (x : α) → x ∈ l → β → β) : β :=
  match l with
  | [] => init
  | x :: xs =>
    f x List.mem_cons_self
      (foldWithMembership xs init (fun y xl b => f y (List.mem_cons_of_mem x xl) b))

def mapOnWithMembership (l : List α) (f : (x : α) → x ∈ l → β) : List β :=
    foldWithMembership l [] (fun x xmem tl => f x xmem :: tl)

abbrev KATState := List (String × Nat)

inductive FDD (K : Type k) (V : Type v) (A : Type a) : Type (max k (max v a)) where
  | FDDLeaf : A → FDD K V A
  | FDDNode : K → List (V × FDD K V A) → FDD K V A → FDD K V A

-- def decEqBranches
--   [DecidableEq K] [DecidableEq V] [DecidableEq A]
--   (decEqFDD : (a b : FDD K V A) → Decidable (Eq a b))
--   (a b : List (V × FDD K V A)) : Decidable (Eq a b) :=
--     sorry

-- @[inline] def FDD.decEq'
--   [DecidableEq K] [DecidableEq V] [DecidableEq A]
--   (a b : FDD K V A) : Decidable (Eq a b) :=
--    match a, b with
--    | .FDDLeaf a, .FDDLeaf b =>
--       match decEq a b with
--       | .isTrue p => .isTrue (by grind)
--       | .isFalse p => .isFalse (by grind)
--    | .FDDLeaf a, .FDDNode d e f => .isFalse (by grind)
--    | .FDDNode a b c, .FDDLeaf d => .isFalse (by grind)
--    | .FDDNode k1 bs1 d1, .FDDNode k2 bs2 d2 =>
--       match decEq k1 k2, decEqBranches decEq' bs1 bs2, decEq' d1 d2 with
--       | .isTrue p, .isTrue q, isTrue r => .isTrue (by grind)
--       | .isFalse p, _, _ => isFalse (by grind)
--       | _, .isFalse q, _ => isFalse (by grind)
--       | _, _, .isFalse r => isFalse (by grind)

-- @[inline] instance : DecidableEq (FDD K V A) := FDD.decEq


-- -- instance [BEq (FDD K V A)] : LawfulBEq (FDD K V A) where
-- --   rfl := fun {a} =>
-- --     match (motive := (fdd : FDD K V A) → (fdd == fdd) = true) a with
-- --     | .FDDLeaf _ => by
-- --       grind
-- --       sorry
-- --     | .FDDNode _ _ _ => sorry
-- --   eq_of_beq := _

-- abbrev SymbolicPacket K [Ord K] V [BEq V] := FDD K V Bool

-- def interpretSymbolicPacket : SymbolicPacket String Nat → KATState → Bool
--   | .FDDLeaf a => fun _ => a
--   | .FDDNode key branches default => fun s =>
--     match List.find? (fun (k, _) => key = k) s with
--     | none => interpretSymbolicPacket default s
--     | some (_, val) =>
--       match _SP : List.find? (fun (x, _) => x = val) branches with
--       | none => interpretSymbolicPacket default s
--       | some (_x, sp) => interpretSymbolicPacket sp s
-- termination_by sp => sizeOf sp
-- decreasing_by
--   simp
--   grind

--   simp
--   apply Nat.lt_add_right
--   apply Nat.lt_add_left
--   apply Nat.lt_trans (m := sizeOf (_x, sp))
--   simp
--   grind
--   apply List.sizeOf_lt_of_mem
--   grind

-- def canonicalizeFDD [BEq (FDD K V A)] [LawfulBEq (FDD K V A)] : FDD K V A → FDD K V A
--   | .FDDLeaf a => .FDDLeaf a
--   | .FDDNode key branches default =>
--     let default' := canonicalizeFDD default
--     let branches' := mapOnWithMembership branches (fun (v, fdd) mem => (v, canonicalizeFDD fdd))
--     let branches'' := branches'.filter (fun (_, fdd) => fdd != default')
--     match branches'' with
--     | [] => default'
--     | _ :: _ => .FDDNode key branches'' default
-- termination_by fdd => sizeOf fdd
-- decreasing_by
--   simp
--   grind

--   simp
--   apply Nat.lt_add_right
--   apply Nat.lt_add_left

--   apply Nat.lt_trans (m := sizeOf (v, fdd))
--   simp
--   apply List.sizeOf_lt_of_mem
--   grind

-- def falseFDD : FDD String Nat Bool := .FDDLeaf False
-- def trueFDD : FDD String Nat Bool := .FDDLeaf False
-- def xIsZeroFDD : FDD String Nat Bool := .FDDNode "x" [(0, trueFDD)] falseFDD
-- def falseFDDInDisguise : FDD String Nat Bool := .FDDNode "x" [(0, falseFDD), (1, falseFDD)] falseFDD

-- -- #eval canonicalizeFDD falseFDD
