variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=   
  Iff.intro
    (fun h : p ∧ q => show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p => show p ∧ q from And.intro (And.right h) (And.left h))

example : p ∨ q ↔ q ∨ p := 
  Iff.intro
    (fun h : p ∨ q => show q ∨ p from 
      Or.elim h
        (fun hp : p =>
          show q ∨ p from Or.intro_right q hp)
        (fun hq : q =>
          show q ∨ p from Or.intro_left p hq))

    (fun h : q ∨ p => show p ∨ q from 
      Or.elim h
        (fun hq : q =>
          show p ∨ q from Or.intro_right p hq)
        (fun hp : p =>
          show p ∨ q from Or.intro_left q hp))

-- -- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
    (fun h: (p ∧ q) ∧ r => show p ∧ (q ∧ r) from
        have hpq : (p ∧ q) := h.left
        have hr : r := h.right
        And.intro (And.left hpq) (And.intro (And.right hpq) hr))
    (fun h: p ∧ (q ∧ r) => show (p ∧ q) ∧ r from
        have hp : p := h.left
        have hqr : (q ∧ r) := h.right
        And.intro (And.intro hp (And.left hqr)) hqr.right)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    (fun h : (p ∨ q) ∨ r => show p ∨ (q ∨ r) from
      h.elim 
      (fun hpq => show p ∨ (q ∨ r) from 
        hpq.elim
        (fun hp : p => Or.inl hp)
        (fun hq : q => Or.intro_right p (Or.intro_left r hq)))
      (fun hr: r => Or.intro_right p (Or.intro_right q hr)))
    (fun h: p ∨ (q ∨ r) => show (p ∨ q) ∨ r from
      h.elim
      (fun hp: p => Or.intro_left r (Or.intro_left q hp))
      (fun hqr : q ∨ r => 
        hqr.elim
        (fun hq => Or.intro_left r (Or.intro_right p hq))
        (fun hr => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (fun h : p ∧ (q ∨ r) => show (p ∧ q) ∨ (p ∧ r) from
      have hp : p := h.left
      Or.elim (h.right)
      (fun hq : q => Or.inl ⟨hp, hq⟩) -- p ∧ q
      (fun hr : r => Or.inr ⟨hp, hr⟩)) -- p ∧ r e Lean add ∨ 
    (fun h : (p ∧ q) ∨ (p ∧ r) => show p ∧ (q ∨ r) from
      Or.elim h
      (fun hpq => 
        have hp := hpq.left
        have hq := hpq.right
        ⟨hp, Or.inl hq⟩)
      (fun hpr => 
        have hp := hpr.left
        have hr := hpr.right
        ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro
    (fun h: p ∨ (q ∧ r) => show (p ∨ q) ∧ (p ∨ r) from 
      h.elim
      (fun hp : p => And.intro (Or.intro_left q hp) (Or.intro_left r hp))
      (fun hqr => 
        have hq : q := hqr.left
        have hr : r := hqr.right
        ⟨Or.inr hq, Or.inr hr⟩))
    (fun h: (p ∨ q) ∧ (p ∨ r) => show p ∨ (q ∧ r) from 
      have hpq := h.left 
      have hpr := h.right
      hpq.elim
      (fun hp => Or.inl hp)
      (fun hq => 
        hpr.elim
        (fun hp => Or.inl hp)
        (fun hr => Or.inr (And.intro hq hr))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
  (fun h : p → (q → r) => show p ∧ q → r from (fun hpq => (h hpq.left) hpq.right))
  (fun h : p ∧ q → r => show p → (q → r) from (fun hp => fun hq => h (And.intro hp hq)))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  Iff.intro
  (fun h : (p ∨ q) → r => show (p → r) ∧ (q → r) from 
    And.intro (fun hp => h (Or.inl hp)) (fun hq => h (Or.inr hq)))
  (fun h : (p → r) ∧ (q → r) => show (p ∨ q) → r from 
    (fun hpq => hpq.elim
      (fun hp => h.left hp)
      (fun hq => h.right hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro
  (fun h : ¬(p ∨ q) => show ¬p ∧ ¬q from 
    And.intro (fun hp => h (Or.inl hp)) (fun hq => h (Or.inr hq)))
  (fun h : ¬p ∧ ¬q => show ¬(p ∨ q) from 
  (fun hpq => hpq.elim 
    (fun hp => h.left hp)
    (fun hq => h.right hq)))

-- example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example (h : ¬p ∨ ¬q) : ¬(p ∧ q) := 
  h.elim
  (fun hnp => show ¬(p ∧ q) from (fun hp => hnp hp.left))
  (fun hnq => show ¬(p ∧ q) from (fun hq => hnq hq.right))

example : ¬(p ∧ ¬p) := fun hp => absurd hp.left hp.right

-- example : p ∧ ¬q → ¬(p → q) := sorry
example (h : p ∧ ¬q) : ¬(p → q) := fun hp => absurd (hp h.left) h.right

-- example : ¬p → (p → q) := sorry
example (hnp : ¬p) : (p → q) := fun hp => False.elim (hnp hp)

-- example : (¬p ∨ q) → (p → q) := sorry
example (h : ¬p ∨ q) : (p → q) := 
  fun hp : p => 
    h.elim
    (fun hnp => show q from False.elim (hnp hp))
    (fun hq => hq)

example : p ∨ False ↔ p := 
  Iff.intro
    (fun hpf : p ∨ False => show p from 
      hpf.elim
      (fun hp => hp)
      (fun hf => False.elim hf))
    (fun hp : p => show p ∨ False from Or.intro_left False hp)

example : p ∧ False ↔ False := 
  Iff.intro
    (fun h : p ∧ False => show False from h.right)
    (fun h : False => show p ∧ False from False.elim h)

example (h : p → q) : (¬q → ¬p) := fun hnq => fun hp => hnq (h hp)

open Classical

example (h : p → q ∨ r) : (p → q) ∨ (p → r) := Or.elim (em p)
  (fun hp => (Or.elim (h hp) 
    (fun hq => Or.inl (fun _ => hq))
    (fun hr => Or.inr (fun _ => hr))))
  (fun hnp => Or.inl (fun hp => False.elim (hnp hp)))

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q := 
  Or.elim (em p)
    (fun hp => Or.inr (fun hq => h (And.intro hp hq)))
    (fun hnp => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q := fun h => Or.elim (em p)
  (fun hp => And.intro hp (fun hq => absurd (fun _ => hq) h))
  (fun hnp => And.intro 
    (False.elim (h (fun hp => False.elim (absurd hp hnp)))) 
    (fun hq => absurd (fun _ => hq) h))

example (h : p → q) : ¬p ∨ q := Or.elim (em p) 
  (fun hp => Or.inr (h hp))
  (fun hnp => Or.inl hnp)

example (h : ¬q → ¬p) : (p → q) := fun hp => Or.elim (em q)
  (fun hq => hq)
  (fun hnq => False.elim ((h hnq) hp))

example : p ∨ ¬p := em p

example (_ : p → q) (hp: p) : p := byContradiction (fun hnp => hnp hp)

example : ((p → q) → p) → p := fun h => Or.elim (em p)
    (fun hp => hp)
    (fun hnp => absurd (h (fun hp => byContradiction (fun _ => hnp hp))) hnp)
