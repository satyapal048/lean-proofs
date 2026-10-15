/-!
# Elementary number theory, by induction

Small results I proved while getting comfortable with `Nat` in Lean 4
without Mathlib's `ring` and `nlinarith`. The pattern throughout is:
induct, unfold one step of the recursion, hand the leftover linear
arithmetic to `omega`, and reach for `Nat.mul_succ` / `Nat.succ_mul`
(or rather their `add_one` spellings) whenever a product needs to be
expanded until `omega` only sees `k * k` as an opaque atom.
-/

namespace LeanProofs.Arithmetic

/-- `triangle n = 0 + 1 + ... + n`, defined recursively. -/
def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

/-- Gauss: twice the triangular number is `n * (n + 1)`.
Stated with the `2 *` on the left so there is no division to fight. -/
theorem two_mul_triangle (n : Nat) : 2 * triangle n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [triangle]
    -- (k+1) * (k+2) = k*(k+1) + 2*(k+1); expand the products so that
    -- `k * k` becomes a single atom and omega can finish.
    simp only [Nat.mul_add_one, Nat.add_one_mul] at *
    omega

/-- Sum of the first `n` odd numbers: `1 + 3 + ... + (2n-1)`. -/
def oddSum : Nat → Nat
  | 0 => 0
  | n + 1 => oddSum n + (2 * n + 1)

/-- ... is a perfect square. -/
theorem oddSum_eq_sq (n : Nat) : oddSum n = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [oddSum]
    simp only [Nat.mul_add_one, Nat.add_one_mul] at *
    omega

/-- Sum of the first `n` even numbers. -/
def evenSum : Nat → Nat
  | 0 => 0
  | n + 1 => evenSum n + 2 * n

theorem evenSum_eq (n : Nat) : evenSum n = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [evenSum]
    cases k with
    | zero => rfl
    | succ j =>
      simp only [Nat.add_sub_cancel] at *
      simp only [Nat.mul_add_one, Nat.add_one_mul] at *
      omega

/-! ## Parity -/

/-- `n * (n + 1)` is always even — one of the two factors is. -/
theorem even_mul_succ (n : Nat) : 2 ∣ n * (n + 1) :=
  ⟨triangle n, (two_mul_triangle n).symm⟩

/-- A square has the same parity as its root. -/
theorem sq_mod_two (n : Nat) : n * n % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [Nat.mul_mod, h]
  · rw [Nat.mul_mod, h]

/-! ## Fibonacci -/

/-- Fibonacci via structural recursion on two predecessors. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval (List.range 12).map fib
-- [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89]

/-- Running sum of Fibonacci numbers: `fib 0 + ... + fib n`. -/
def fibSum : Nat → Nat
  | 0 => fib 0
  | n + 1 => fibSum n + fib (n + 1)

/-- The sum of the first `n+1` Fibonacci numbers is `fib (n+2) - 1`.
Written additively to stay away from truncated subtraction. -/
theorem fibSum_succ (n : Nat) : fibSum n + 1 = fib (n + 2) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [fibSum]
    rw [show fib (k + 1 + 2) = fib (k + 1) + fib (k + 2) from rfl]
    omega

/-- Fibonacci numbers are monotone from index 1 onwards. -/
theorem fib_le_fib_succ (n : Nat) : fib n ≤ fib (n + 1) := by
  induction n with
  | zero => decide
  | succ k _ =>
    show fib (k + 1) ≤ fib k + fib (k + 1)
    omega

/-- Every Fibonacci number beyond the zeroth is positive. -/
theorem fib_pos {n : Nat} (hn : 0 < n) : 0 < fib n := by
  induction n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ k ih =>
    cases k with
    | zero => decide
    | succ j =>
      have := ih (Nat.succ_pos j)
      show 0 < fib j + fib (j + 1)
      omega

/-! ## Divisibility -/

theorem three_dvd_sum_consecutive (n : Nat) : 3 ∣ n + (n + 1) + (n + 2) :=
  ⟨n + 1, by omega⟩

/-- `gcd` is idempotent, stated directly from the core library's lemmas. -/
theorem gcd_self_mul (a b : Nat) : Nat.gcd a (a * b) = a := by
  exact Nat.gcd_eq_left (Nat.dvd_mul_right a b)

end LeanProofs.Arithmetic
