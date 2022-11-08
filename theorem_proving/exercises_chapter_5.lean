variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    apply And.intro 
    . exact h.right
    . exact h.left
  . intro h
    apply And.intro 
    . exact h.right
    . exact h.left

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h 
    apply h.elim
    . intro hp
      exact Or.inr hp
    . intro hq 
      exact Or.inl hq
  . intro h 
    apply h.elim
    . intro hq 
      exact Or.inr hq 
    . intro hp 
      exact Or.inl hp

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by 
  apply Iff.intro
  . intro h 
    apply And.intro 
    . exact h.left.left
    apply And.intro
    . exact h.left.right
    . exact h.right 
  . intro h 
    apply And.intro 
    apply And.intro
    . exact h.left 
    . exact h.right.left
    exact h.right.right

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro 
  . intro h
    apply h.elim 
    . intro hpq 
      apply hpq.elim 
      . intro hp 
        exact Or.inl hp
      . intro hq 
        apply Or.inr
        exact Or.inl hq
    . intro hr 
      apply Or.inr (Or.inr hr)
  . intro h
    apply h.elim 
    . intro hp 
      apply Or.inl (Or.inl hp)
    . intro hqr 
      apply hqr.elim
      . intro hq 
        apply Or.inl (Or.inr hq)
      . intro hr
        exact Or.inr hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro 
  . intro h 
    apply Or.elim (h.right)
    . intro hq 
      apply Or.inl ⟨h.left, hq⟩
    . intro hr
      apply Or.inr ⟨h.left, hr⟩
  . intro h
    apply h.elim 
    . intro hpq 
      apply And.intro
      exact hpq.left
      exact Or.inl hpq.right
    . intro hpr
      apply And.intro
      exact hpr.left
      exact Or.inr hpr.right

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h 
    apply h.elim 
    . intro hp 
      exact ⟨Or.inl hp, Or.inl hp⟩ 
    . intro hqr
      apply And.intro 
      exact Or.inr hqr.left
      exact Or.inr hqr.right
  . intro h 
    apply Or.elim h.left
    . intro hp
      exact Or.inl hp
    . intro hq 
      apply Or.elim h.right
      . intro hp 
        exact Or.inl hp
      . intro hr 
        exact Or.inr ⟨hq,hr⟩ 

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h
    intros
    simp [*]
  . intro h
    intro h1 h2
    simp [h, h1, h2]

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h 
    apply And.intro
    . intro hp
      simp [h, hp]
    . intro hq
      simp [h, hq] 
  . intro h
    intro h1
    apply h1.elim 
    . intro hp 
      simp [*]
    . intro hq
      simp [*]

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro 
  . intro h 
    apply And.intro 
    . intro hp
      exact h (Or.inl hp)
    . intro hq 
      exact h (Or.inr hq)
  . intro h
    intro h1 
    apply h1.elim 
    . intro hp 
      exact h.left hp 
    . intro hq 
      exact h.right hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by 
  intro h h1
  apply h.elim 
  . intro hnp
    exact hnp h1.left
  . intro hnq 
    exact hnq h1.right

example : ¬(p ∧ ¬p) := by 
  intro h 
  exact h.right h.left

example : p ∧ ¬q → ¬(p → q) := by 
  intro h h1
  have h2 := h1 h.left 
  exact h.right h2

example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry

example : p ∨ False ↔ p := by 
  simp

example : p ∧ False ↔ False := by 
  simp

example : (p → q) → (¬q → ¬p) := sorry


open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry

-- Chapter 4

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry


open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

-- 2

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  admit


