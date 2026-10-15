/-!
# A tiny compiler, proved correct

Arithmetic expressions get compiled to a stack machine, and
`compile_correct` says running the compiled code leaves exactly the
value of the expression on top of whatever stack you started with.

This is the standard "first compiler correctness proof", but it took me
a few attempts to state the lemma in the form that actually inducts:
the stack and the continuation code both have to stay universally
quantified (`generalizing`), otherwise the `Add`/`Mul` cases do not
line up with the hypotheses.
-/

namespace LeanProofs.StackMachine

/-- Source language: literals, variables looked up in an environment,
addition, multiplication. -/
inductive Expr where
  | lit : Nat → Expr
  | var : String → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

/-- Environments map variable names to values; unknown names read as 0. -/
abbrev Env := String → Nat

def eval (env : Env) : Expr → Nat
  | .lit n => n
  | .var s => env s
  | .plus a b => eval env a + eval env b
  | .times a b => eval env a * eval env b

/-- Target language. -/
inductive Instr where
  | push : Nat → Instr
  | load : String → Instr
  | add : Instr
  | mul : Instr
  deriving Repr

/-- Run instructions against a stack. A malformed program (binary op on
a stack with fewer than two entries) just drops the instruction; the
correctness theorem shows compiled code never hits that branch. -/
def run (env : Env) : List Instr → List Nat → List Nat
  | [], st => st
  | .push n :: rest, st => run env rest (n :: st)
  | .load s :: rest, st => run env rest (env s :: st)
  | .add :: rest, b :: a :: st => run env rest ((a + b) :: st)
  | .mul :: rest, b :: a :: st => run env rest ((a * b) :: st)
  | _ :: rest, st => run env rest st

def compile : Expr → List Instr
  | .lit n => [.push n]
  | .var s => [.load s]
  | .plus a b => compile a ++ compile b ++ [.add]
  | .times a b => compile a ++ compile b ++ [.mul]

/-- `run` over a concatenation is `run` twice. -/
theorem run_append (env : Env) (p q : List Instr) (st : List Nat) :
    run env (p ++ q) st = run env q (run env p st) := by
  induction p generalizing st with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | push n => simp [run, ih]
    | load s => simp [run, ih]
    | add =>
      match st with
      | b :: a :: st' => simp [run, ih]
      | [] => simp [run, ih]
      | [_] => simp [run, ih]
    | mul =>
      match st with
      | b :: a :: st' => simp [run, ih]
      | [] => simp [run, ih]
      | [_] => simp [run, ih]

/-- The correctness theorem, in its inductive form. -/
theorem compile_correct (env : Env) (e : Expr) (st : List Nat) :
    run env (compile e) st = eval env e :: st := by
  induction e generalizing st with
  | lit n => rfl
  | var s => rfl
  | plus a b iha ihb =>
    simp only [compile, eval, run_append, iha, ihb, run]
  | times a b iha ihb =>
    simp only [compile, eval, run_append, iha, ihb, run]

/-- The version you would quote: start from the empty stack, get the value. -/
theorem compile_eval (env : Env) (e : Expr) :
    run env (compile e) [] = [eval env e] :=
  compile_correct env e []

/-! ## A quick sanity check that the machine does something sensible -/

def sample : Expr := .plus (.times (.lit 3) (.var "x")) (.lit 4)

#eval compile sample
#eval run (fun s => if s == "x" then 5 else 0) (compile sample) []
-- [19]

end LeanProofs.StackMachine
