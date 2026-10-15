# lean-proofs

A collection of things I've formalised in Lean 4 while learning it properly.
Everything here is checked by `lake build` on every push (see the badge
below), there are no `sorry`s, and the project deliberately has **no
dependency on Mathlib** — I wanted to understand what the core library
gives you and how far `omega`, `simp` and `decide` go on their own before
leaning on `ring`, `linarith` and friends.

[![Lean Action CI](https://github.com/satyapal048/lean-proofs/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/satyapal048/lean-proofs/actions/workflows/lean_action_ci.yml)

Toolchain: `leanprover/lean4:4.35.0`.

## What's in here

| File | What it proves |
| --- | --- |
| `LeanProofs/Sorting.lean` | Insertion sort returns a sorted permutation of its input (`insertionSort_spec`). Both halves — `Sorted` and `List.Perm` — are proved separately and then combined. |
| `LeanProofs/SearchTree.lean` | A binary search tree whose `insert` preserves the BST invariant (`insert_isBST`), plus `contains_insert` and a proof that `contains` agrees with membership in the in-order traversal on any valid tree (`contains_correct`). |
| `LeanProofs/StackMachine.lean` | A small expression language compiled to a stack machine, with the usual correctness theorem `run env (compile e) st = eval env e :: st`. |
| `LeanProofs/Arithmetic.lean` | Gauss's formula, sum of odd numbers is a square, Fibonacci identities, parity and divisibility facts — all by induction on `Nat` with no Mathlib tactics. |
| `LeanProofs/Lists.lean` | Reverse is an involution, length/map/append lemmas, and a proof that an accumulator-based reverse equals the naive one. Re-proved from my own definitions rather than imported. |
| `LeanProofs/Logic.lean` | Propositional and quantifier identities, mostly in term mode, including the one De Morgan direction that genuinely needs classical logic. |

## Running it

```
lake build
```

That's it. No `lake exe cache get`, nothing to download beyond the toolchain.
If you have `elan`, it will pick up the pinned version from `lean-toolchain`.

## Why these particular proofs

Insertion sort, BST insert, and the stack-machine compiler are the three
exercises I'd recommend to anyone starting out, because each one forces a
different habit:

- Sorting makes you state *two* properties and notice that neither alone
  pins down the function.
- The BST invariant only inducts cleanly once you phrase it with an
  all-nodes predicate (`Forall`) instead of talking about the root.
- The compiler proof does not go through at all until you generalise over
  the stack *and* the remaining code — a good lesson in stating the
  inductive hypothesis you actually need rather than the theorem you want.

The arithmetic file exists because I kept reaching for `ring` and wanted
to know what to do without it. The answer turned out to be: expand
products with `Nat.mul_add_one` / `Nat.add_one_mul` until the only
non-linear term is `k * k`, then let `omega` treat that as an atom.

## Things I'd like to add

- Generalise `Sorting` from `Nat` to any type with a decidable linear order.
- Prove `fromList` produces a BST (it does — it's just `insert_isBST` folded).
- A `decide`-free proof of the `Fin 8` squares-mod-8 example in `Logic.lean`.
