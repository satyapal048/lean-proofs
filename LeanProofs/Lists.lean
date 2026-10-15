/-!
# List lemmas from scratch

Most of these already exist in the core library (`List.reverse_reverse`,
`List.length_append`, ...). I re-proved them against my own definitions
on purpose: the point was to see the induction skeleton behind each
one rather than to call `simp` and move on.

The last section shows an accumulator-based reverse is extensionally
equal to the naive one, which is the usual warm-up before proving
anything about tail-recursive code.
-/

namespace LeanProofs.Lists

variable {α β : Type}

/-- Naive quadratic reverse. -/
def flip : List α → List α
  | [] => []
  | x :: xs => flip xs ++ [x]

/-- Linear reverse using an accumulator. -/
def flipAcc : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => flipAcc xs (x :: acc)

/-- Our own `map`, so nothing below is secretly `simp`-closed by a
core lemma about `List.map`. -/
def apply (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: apply f xs

/-- Our own `length`. -/
def count : List α → Nat
  | [] => 0
  | _ :: xs => count xs + 1

#eval flip [1, 2, 3]
#eval flipAcc [1, 2, 3] []

/-! ## Length and append -/

theorem count_append (xs ys : List α) :
    count (xs ++ ys) = count xs + count ys := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih => simp [count, ih, Nat.add_right_comm]

theorem count_flip (xs : List α) : count (flip xs) = count xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [flip, count_append, count, ih]

theorem count_apply (f : α → β) (xs : List α) :
    count (apply f xs) = count xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [apply, count, ih]

/-! ## Reverse is an involution -/

theorem flip_append (xs ys : List α) :
    flip (xs ++ ys) = flip ys ++ flip xs := by
  induction xs with
  | nil => simp [flip]
  | cons x xs ih => simp [flip, ih, List.append_assoc]

theorem flip_flip (xs : List α) : flip (flip xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [flip, flip_append, ih]

/-- Reverse commutes with map. -/
theorem apply_flip (f : α → β) (xs : List α) :
    apply f (flip xs) = flip (apply f xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [flip, apply]
    rw [← ih]
    -- apply distributes over ++; prove that inline since it is one line.
    have dist : ∀ (us vs : List α), apply f (us ++ vs) = apply f us ++ apply f vs := by
      intro us vs
      induction us with
      | nil => rfl
      | cons u us ih' => simp [apply, ih']
    rw [dist]
    rfl

/-! ## The accumulator version agrees with the naive one -/

/-- The generalised statement; the accumulator has to be universally
quantified or the induction hypothesis is useless. -/
theorem flipAcc_eq (xs acc : List α) :
    flipAcc xs acc = flip xs ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp [flipAcc, flip, ih, List.append_assoc]

theorem flipAcc_nil (xs : List α) : flipAcc xs [] = flip xs := by
  rw [flipAcc_eq, List.append_nil]

/-- And both agree with the standard library's reverse. -/
theorem flip_eq_reverse (xs : List α) : flip xs = xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [flip, ih]

/-! ## Membership survives reversal -/

theorem mem_flip {a : α} {xs : List α} : a ∈ flip xs ↔ a ∈ xs := by
  rw [flip_eq_reverse, List.mem_reverse]

end LeanProofs.Lists
