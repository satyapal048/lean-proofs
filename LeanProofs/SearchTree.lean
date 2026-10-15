/-!
# Binary search trees: `insert` keeps the invariant

A `Tree` of naturals with an `insert` and a `contains`. The interesting
theorems are at the bottom:

* `insert_isBST` — inserting into a search tree yields a search tree;
* `contains_insert` — the tree afterwards contains exactly the old
  elements plus the new one;
* `contains_correct` — for a BST, the fast `contains` agrees with
  plain membership in the in-order traversal.

The invariant `IsBST` is phrased with `Forall`, a predicate that holds
at every node, which is what makes the induction go through cleanly.
-/

namespace LeanProofs.SearchTree

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
  deriving Repr

open Tree

/-- `Forall p t` means `p` holds at every node of `t`. -/
def Forall (p : Nat → Prop) : Tree → Prop
  | leaf => True
  | node l k r => p k ∧ Forall p l ∧ Forall p r

/-- The search-tree invariant: left subtree is strictly below the key,
right subtree is strictly above, recursively. -/
def IsBST : Tree → Prop
  | leaf => True
  | node l k r => Forall (· < k) l ∧ Forall (k < ·) r ∧ IsBST l ∧ IsBST r

def insert (x : Nat) : Tree → Tree
  | leaf => node leaf x leaf
  | node l k r =>
    if x < k then node (insert x l) k r
    else if k < x then node l k (insert x r)
    else node l k r

def contains (x : Nat) : Tree → Bool
  | leaf => false
  | node l k r =>
    if x < k then contains x l
    else if k < x then contains x r
    else true

def toList : Tree → List Nat
  | leaf => []
  | node l k r => toList l ++ k :: toList r

def fromList (xs : List Nat) : Tree := xs.foldl (fun t x => insert x t) leaf

#eval toList (fromList [8, 3, 10, 1, 6, 14, 4, 7, 13])
-- [1, 3, 4, 6, 7, 8, 10, 13, 14]

/-! ## Forall is preserved by insert (when the new key satisfies p) -/

theorem forall_insert {p : Nat → Prop} {x : Nat} {t : Tree}
    (hx : p x) (ht : Forall p t) : Forall p (insert x t) := by
  induction t with
  | leaf => exact ⟨hx, trivial, trivial⟩
  | node l k r ihl ihr =>
    obtain ⟨hk, hl, hr⟩ := ht
    unfold insert
    split
    · exact ⟨hk, ihl hl, hr⟩
    · split
      · exact ⟨hk, hl, ihr hr⟩
      · exact ⟨hk, hl, hr⟩

/-- The headline: `insert` preserves the search-tree invariant. -/
theorem insert_isBST {x : Nat} {t : Tree} (ht : IsBST t) : IsBST (insert x t) := by
  induction t with
  | leaf => exact ⟨trivial, trivial, trivial, trivial⟩
  | node l k r ihl ihr =>
    obtain ⟨hlk, hkr, hl, hr⟩ := ht
    unfold insert
    split
    · rename_i hxk
      exact ⟨forall_insert hxk hlk, hkr, ihl hl, hr⟩
    · split
      · rename_i hkx
        exact ⟨hlk, forall_insert hkx hkr, hl, ihr hr⟩
      · exact ⟨hlk, hkr, hl, hr⟩

/-! ## What `contains` says after an `insert` -/

theorem contains_insert_self (x : Nat) (t : Tree) :
    contains x (insert x t) = true := by
  induction t with
  | leaf => simp [insert, contains]
  | node l k r ihl ihr =>
    unfold insert
    split
    · rename_i h; simp [contains, h, ihl]
    · split
      · rename_i h1 h2; simp [contains, h1, h2, ihr]
      · rename_i h1 h2; simp [contains, h1, h2]

theorem contains_insert_of_ne {x y : Nat} (hxy : x ≠ y) (t : Tree) :
    contains x (insert y t) = contains x t := by
  induction t with
  | leaf =>
    simp only [insert, contains]
    -- x ≠ y so one of the two comparisons must fire.
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · simp [h]
    · simp [Nat.lt_asymm h, h]
  | node l k r ihl ihr =>
    unfold insert
    split
    · rename_i hyk
      by_cases hxk : x < k
      · simp [contains, hxk, ihl]
      · simp [contains, hxk]
    · split
      · rename_i hyk hky
        by_cases hxk : x < k
        · simp [contains, hxk]
        · by_cases hkx : k < x
          · simp [contains, hxk, hkx, ihr]
          · simp [contains, hxk, hkx]
      · rfl

/-- Combined form: membership after insertion is membership before,
or equality with the new key. -/
theorem contains_insert (x y : Nat) (t : Tree) :
    contains x (insert y t) = true ↔ x = y ∨ contains x t = true := by
  by_cases h : x = y
  · subst h; simp [contains_insert_self]
  · rw [contains_insert_of_ne h]; simp [h]

/-! ## `contains` is correct on search trees -/

/-- Any node satisfying `Forall p` has every traversed element satisfying `p`. -/
theorem forall_mem_toList {p : Nat → Prop} {t : Tree} (ht : Forall p t)
    {a : Nat} (ha : a ∈ toList t) : p a := by
  induction t with
  | leaf => simp [toList] at ha
  | node l k r ihl ihr =>
    obtain ⟨hk, hl, hr⟩ := ht
    simp only [toList, List.mem_append, List.mem_cons] at ha
    rcases ha with ha | rfl | ha
    · exact ihl hl ha
    · exact hk
    · exact ihr hr ha

theorem contains_correct {x : Nat} {t : Tree} (ht : IsBST t) :
    contains x t = true ↔ x ∈ toList t := by
  induction t with
  | leaf => simp [contains, toList]
  | node l k r ihl ihr =>
    obtain ⟨hlk, hkr, hl, hr⟩ := ht
    simp only [contains, toList, List.mem_append, List.mem_cons]
    by_cases hxk : x < k
    · -- x is below k: it cannot be k, and cannot be in the right subtree.
      simp only [hxk, ite_true]
      rw [ihl hl]
      constructor
      · exact fun h => Or.inl h
      · rintro (h | rfl | h)
        · exact h
        · exact absurd hxk (Nat.lt_irrefl _)
        · exact absurd (forall_mem_toList hkr h) (Nat.lt_asymm hxk)
    · by_cases hkx : k < x
      · simp only [hxk, hkx, ite_true, ite_false]
        rw [ihr hr]
        constructor
        · exact fun h => Or.inr (Or.inr h)
        · rintro (h | rfl | h)
          · exact absurd (forall_mem_toList hlk h) (Nat.lt_asymm hkx)
          · exact absurd hkx (Nat.lt_irrefl _)
          · exact h
      · -- neither strictly below nor above: x = k.
        have hxeq : x = k := Nat.le_antisymm (Nat.not_lt.mp hkx) (Nat.not_lt.mp hxk)
        simp [hxeq]

end LeanProofs.SearchTree
