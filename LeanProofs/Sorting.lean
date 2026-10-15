/-!
# Insertion sort, verified

The classic first "real" verification exercise. I wanted two guarantees
out of `insertionSort`:

1. the output is sorted (`Sorted`), and
2. the output is a rearrangement of the input (`List.Perm`).

Neither property alone is enough — `fun _ => []` satisfies (1) and
`id` satisfies (2). Together they pin the function down.

I deliberately kept this over `Nat` instead of generalising to a
`LinearOrder`, since this repo does not depend on Mathlib. The proofs
go through with `omega` doing the arithmetic reasoning.
-/

namespace LeanProofs.Sorting

/-- Put `x` in front of the first element that is not smaller than it. -/
def slideIn (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: rest => if x ≤ y then x :: y :: rest else y :: slideIn x rest

/-- Textbook insertion sort, built on `slideIn`. -/
def insertionSort : List Nat → List Nat
  | [] => []
  | h :: t => slideIn h (insertionSort t)

/-- A list is sorted when every element is ≤ everything after it. -/
inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | cons {a : Nat} {l : List Nat} :
      (∀ b ∈ l, a ≤ b) → Sorted l → Sorted (a :: l)

#eval insertionSort [5, 2, 9, 1, 5, 6]
-- [1, 2, 5, 5, 6, 9]

/-! ## Permutation half -/

theorem slideIn_perm (x : Nat) (l : List Nat) :
    List.Perm (slideIn x l) (x :: l) := by
  induction l with
  | nil => simp [slideIn]
  | cons y rest ih =>
    unfold slideIn
    split
    · exact List.Perm.refl _
    · -- y :: slideIn x rest ~ y :: x :: rest ~ x :: y :: rest
      exact (ih.cons y).trans (List.Perm.swap x y rest)

theorem insertionSort_perm (l : List Nat) :
    List.Perm (insertionSort l) l := by
  induction l with
  | nil => simp [insertionSort]
  | cons h t ih =>
    simp only [insertionSort]
    exact (slideIn_perm h (insertionSort t)).trans (ih.cons h)

/-! ## Sortedness half -/

/-- Everything in `slideIn x l` is either `x` itself or came from `l`. -/
theorem mem_slideIn {x b : Nat} {l : List Nat} (hb : b ∈ slideIn x l) :
    b = x ∨ b ∈ l := by
  induction l with
  | nil => simp [slideIn] at hb; exact Or.inl hb
  | cons y rest ih =>
    unfold slideIn at hb
    split at hb
    · rcases hb with _ | ⟨_, h⟩
      · exact Or.inl rfl
      · exact Or.inr h
    · rcases hb with _ | ⟨_, h⟩
      · exact Or.inr (List.mem_cons_self ..)
      · rcases ih h with rfl | h'
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem _ h')

theorem slideIn_sorted (x : Nat) {l : List Nat} (hl : Sorted l) :
    Sorted (slideIn x l) := by
  induction hl with
  | nil => exact Sorted.cons (by simp) Sorted.nil
  | @cons a rest hAll hRest ih =>
    unfold slideIn
    split
    · rename_i hxa
      -- x ≤ a and a ≤ everything in rest, so x ≤ everything.
      apply Sorted.cons
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hxa
        · exact Nat.le_trans hxa (hAll b hb')
      · exact Sorted.cons hAll hRest
    · rename_i hxa
      apply Sorted.cons
      · intro b hb
        rcases mem_slideIn hb with rfl | hb'
        · omega
        · exact hAll b hb'
      · exact ih

theorem insertionSort_sorted (l : List Nat) : Sorted (insertionSort l) := by
  induction l with
  | nil => exact Sorted.nil
  | cons h t ih => exact slideIn_sorted h ih

/-- The headline result: a sorted permutation of the input. -/
theorem insertionSort_spec (l : List Nat) :
    Sorted (insertionSort l) ∧ List.Perm (insertionSort l) l :=
  ⟨insertionSort_sorted l, insertionSort_perm l⟩

/-- Free consequence: sorting does not change the length. -/
theorem insertionSort_length (l : List Nat) :
    (insertionSort l).length = l.length :=
  (insertionSort_perm l).length_eq

end LeanProofs.Sorting
