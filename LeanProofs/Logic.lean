/-!
# Propositional and first-order warm-ups

Term-mode proofs where possible, tactic-mode where it reads better.
The point of this file was to be able to write proofs *without* `simp`
or `decide` doing the thinking, so most of these are explicit.

The last two show where classical reasoning is actually required:
`not_forall` needs `Classical.byContradiction`, while its dual
`not_exists` does not.
-/

namespace LeanProofs.Logic

variable {p q r : Prop}
variable {α : Type} {P Q : α → Prop}

theorem and_swap : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩

theorem or_swap : p ∨ q → q ∨ p
  | .inl hp => .inr hp
  | .inr hq => .inl hq

theorem curry_uncurry : (p ∧ q → r) ↔ (p → q → r) :=
  ⟨fun h hp hq => h ⟨hp, hq⟩, fun h ⟨hp, hq⟩ => h hp hq⟩

theorem or_distrib_and : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · rintro (hp | ⟨hq, hr⟩)
    · exact ⟨.inl hp, .inl hp⟩
    · exact ⟨.inr hq, .inr hr⟩
  · rintro ⟨hp | hq, hp' | hr⟩
    · exact .inl hp
    · exact .inl hp
    · exact .inl hp'
    · exact .inr ⟨hq, hr⟩

/-- Contrapositive, constructive direction only. -/
theorem contrapose (h : p → q) : ¬q → ¬p :=
  fun hnq hp => hnq (h hp)

/-- De Morgan, the direction that holds constructively. -/
theorem not_or_iff : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨fun h => ⟨fun hp => h (.inl hp), fun hq => h (.inr hq)⟩,
   fun ⟨hnp, hnq⟩ h => h.elim hnp hnq⟩

/-! ## Quantifiers -/

theorem forall_and : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) :=
  ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩,
   fun ⟨hP, hQ⟩ x => ⟨hP x, hQ x⟩⟩

theorem exists_or : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · rintro ⟨x, hx | hx⟩
    · exact .inl ⟨x, hx⟩
    · exact .inr ⟨x, hx⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨x, .inl hx⟩
    · exact ⟨x, .inr hx⟩

/-- Pushing a negation through `∃` is constructive. -/
theorem not_exists_iff : (¬∃ x, P x) ↔ ∀ x, ¬P x :=
  ⟨fun h x hx => h ⟨x, hx⟩, fun h ⟨x, hx⟩ => h x hx⟩

/-- Pushing a negation through `∀` is not: this needs excluded middle. -/
theorem not_forall_iff : (¬∀ x, P x) ↔ ∃ x, ¬P x := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro x
    apply Classical.byContradiction
    intro hnx
    exact hne ⟨x, hnx⟩
  · rintro ⟨x, hnx⟩ h
    exact hnx (h x)

/-- A classic: Peirce's law is equivalent to excluded middle for `p`. -/
theorem peirce_of_em (hem : p ∨ ¬p) : ((p → q) → p) → p :=
  fun h => hem.elim id (fun hnp => h (fun hp => absurd hp hnp))

/-! ## A small decidable fact, just to contrast with the above -/

example : ∀ n : Fin 8, n.val * n.val % 8 ∈ [0, 1, 4] := by decide

end LeanProofs.Logic
