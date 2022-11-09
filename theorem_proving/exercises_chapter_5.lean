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

example : ¬p → (p → q) := by
  intro h h1
  apply False.elim (h h1)

example : (¬p ∨ q) → (p → q) := by 
  intro h hp
  apply h.elim 
  . intro hnp 
    apply False.elim (hnp hp)
  . intro hq 
    exact hq

example : p ∨ False ↔ p := by 
  simp

example : p ∧ False ↔ False := by 
  simp

example : (p → q) → (¬q → ¬p) := by
  intro h hnq hp
  exact hnq (h hp)

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by 
  intro h 
  apply Or.elim (em p)
  . intro hp 
    have hqr := (h hp)
    apply hqr.elim 
    . intro hq 
      simp [*]
    . intro hr 
      simp [*]
  . intro hnp 
    simp [h, hnp]

example : ¬(p ∧ q) → ¬p ∨ ¬q := by 
  intro h
  apply Or.elim (em p)
  . intro hp 
    apply Or.inr 
    . intro hq 
      simp [h ⟨hp,hq⟩]
  . intro hnp 
    apply Or.inl <;> assumption

example : ¬(p → q) → p ∧ ¬q := by 
  intro h
  apply Or.elim (em p)
  . intro hp 
    apply And.intro 
    exact hp 
    intro hq 
    simp [hp, hq] at h
  . intro hnp 
    apply And.intro 
    apply False.elim 
    apply h 
    . intro hp 
      exact absurd hp hnp
    . intro hq 
      apply absurd 
      exact h
      simp [*]

example : (p → q) → (¬p ∨ q) := by 
  intro h 
  apply Or.elim (em q)
  . intro hq 
    exact Or.inr hq
  . intro hnq 
    apply Or.inl
    . intro hp
      apply absurd 
      exact (h hp) 
      exact hnq

example : (¬q → ¬p) → (p → q) := by 
  intro h hp 
  apply Or.elim (em q)
  . intro hq 
    exact hq 
  . intro hnq 
    exact absurd hp (h hnq)

example : p ∨ ¬p := by 
  exact (em p)

example : ((p → q) → p) → p := by 
  intro h 
  admit

-- Chapter 4

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by 
  apply Iff.intro 
  . intro h 
    apply And.intro 
    intro α 
    exact (h α).left
    intro α 
    exact (h α).right
  . intro h
    simp [*]

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by 
  intro h h1 
  simp [h, h1]

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by 
  intro h α 
  apply h.elim 
  . intro hp 
    exact Or.inl (hp α) 
  . intro hq
    exact Or.inr (hq α) 

example : α → ((∀ x : α, r) ↔ r) := by 
  intro α 
  apply Iff.intro 
  . intro h
    exact h α 
  . intro h 
    simp [*]

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro 
  . intro h 
    apply Or.elim (em r)
    . intro hr 
      exact Or.inr hr 
    . intro hnr 
      apply Or.inl 
      intro α 
      apply (h α).elim 
      . intro hp 
        exact hp
      . intro hr 
        apply False.elim 
        exact absurd hr hnr
  . intro h α 
    apply h.elim 
    . intro hp 
      simp [*]
    . intro hr 
      simp [*]

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by 
  apply Iff.intro 
  . intro h
    intro hr α 
    simp [*]
  . intro h α
    intro hr 
    simp [*]

-- open Classical

example : (∃ x : α, r) → r := by 
  intro h 
  cases h with 
  | intro α hr => simp [*] 

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  apply Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by 
  apply Iff.intro 
  . intro h 
    cases h with 
    | intro x px => constructor; exists x; exact px.left; exact px.right 
  . intro h 
    cases h.left with 
    | intro x px => exists x; constructor; exact px; exact h.right

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by 
  apply Iff.intro 
  . intro h 
    cases h with 
    | intro x px => 
      apply px.elim 
      . intro hpx 
        apply Or.inl
        apply Exists.intro x hpx 
      . intro hqx 
        apply Or.inr
        apply Exists.intro x hqx
  . intro h 
    apply h.elim 
    . intro hpx 
      cases hpx with 
      | intro x px => exists x; apply Or.inl; exact px 
    . intro hqx 
      cases hqx with
      | intro x qx => exists x; apply Or.inr; exact qx

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by 
  apply Iff.intro 
  . intro h h1
    cases h1 with 
    | intro x px => apply absurd (h x) px
  . intro h α 
    apply byContradiction
    intro hnp 
    apply absurd (Exists.intro α hnp) h  

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by 
  apply Iff.intro
  . intro h h1
    cases h with 
    | intro x px => apply absurd px (h1 x)
  . intro h
    apply byContradiction
    . intro h1
      apply absurd
      exact h 
      admit    

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by 
  apply Iff.intro 
  . intro h α hpa
    apply absurd (Exists.intro α hpa) h
  . intro h h1 
    cases h1 with 
    | intro x px => apply absurd px (h x)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by 
  apply Iff.intro 
  . intro h 
    apply byContradiction 
    admit

  . intro h h1
    cases h with 
    | intro x px => apply absurd (h1 x) px

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by 
  apply Iff.intro 
  . intro h h1 
    cases h1 with 
    | intro x px => apply (h x) px
  . intro h α hpa 
    apply h (Exists.intro α hpa)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by 
  apply Iff.intro 
  . intro h h1 
    cases h with 
    | intro x px => simp [*]
  . intro h 
    apply byCases 
    . intro hap 
      apply Exists.intro a (fun _ => h hap) 
    . intro hnap
      apply byContradiction
      . intro hnex  
        apply hnap
        . intro x 
          apply byContradiction
          . intro hnp 
            apply hnex (Exists.intro x (fun hp => absurd hp hnp))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by 
  apply Iff.intro 
  . intro h 
    cases h with 
    | intro x px => intro hr; exists x; simp [px hr]
  . intro h 
    apply Or.elim (em r)
    . intro hr 
      cases (h hr) with 
      | intro x px => 
      apply Exists.intro x 
      intro _
      exact px
    . intro hnr 
      apply Exists.intro a 
      . intro hr
        apply False.elim (hnr hr)

-- 2
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  simp [*]

