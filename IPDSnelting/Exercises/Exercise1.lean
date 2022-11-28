-- Let's first prove some simple example lemmas with the logical connectives we learned in the lecture.
section
-- Variables in sections determine the type of certain variables for the remainder of the section, saving us a bit of space.
variable (p q r : Prop)

example : p → p := fun hp => hp

example : p → (q → p) := fun hp => fun _ => hp

-- Note: `→` associates to the right, so the above proposition is equivalent to
-- `p → q → p`

example : (p → False) → (p → q) := fun hnp => fun hp => nomatch hnp hp

example : (p ∨ p) → p := fun h =>
  match h with 
  | Or.inr hp => hp
  | Or.inl hp => hp

example : (p → q → r) → (p ∧ q → r) := fun h => fun hpq => h hpq.1 hpq.2

example : (p ∧ q → r) → (p → q → r) := fun h => fun hp => fun hq => h ⟨hp,hq⟩ 

example : p → (p → q) → p ∧ q := fun hp => fun hpq => ⟨hp, hpq hp⟩ 

theorem imp_and : (p → q ∧ r) → (p → q) ∧ (p → r) := fun h => 
  And.intro (fun hp => (h hp).1) (fun hp => (h hp).2)

-- Matching on `And.intro` can quickly become tedious, so you can use the following helper functions from now on:
#check And.left
#check And.right

/- BIIMPLICATION -/

-- Biimplication ("if and only if") is written \iff.
-- It is defined as a data type on the constructor
-- Iff.intro : (A → B) → (B → A) → (A ↔ B)
-- Can you recover the proof for A → B by a match expression?

example (hpq : p ↔ q) : (p → q) := fun hp => 
  match hpq with 
  | ⟨hpq',_⟩ => hpq' hp

-- Like for `And`, we have names for both directions of the biimplication:
#check Iff.mp
#check Iff.mpr

-- Prove the following biimplications using the threorem from above!
-- Note: `↔` is defined to bind less tightly than other connectives such as `∧` or `∨`.

theorem iff_and : (p → q ∧ r) ↔ (p → q) ∧ (p → r) := 
  Iff.intro 
  (fun h => ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩)
  (fun h hp => ⟨h.left hp, h.right hp⟩)

theorem or_and : (p ∨ q → r) ↔ (p → r) ∧ (q → r) := 
  Iff.intro 
  (fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩)
  (fun h hpq => 
    match hpq with 
    | Or.inl hp => h.left hp
    | Or.inr hq => h.right hq
  )

theorem iff_and_false : False ↔ p ∧ False := 
  Iff.intro 
  (fun h => ⟨nomatch h, h⟩)
  (fun h => h.2)

/- NEGATION -/

-- Negation is defined by ¬ A := (A → False).
-- How is that a good choice? Let us check some basic properties of negation:

example : ¬False := fun h => h

theorem imp_not_not : p → ¬¬p := fun hp hnp => hnp hp

example : ¬(p ∧ ¬p) := fun hpnp => hpnp.2 hpnp.1

theorem not_or_not : (¬p ∨ ¬q) → ¬(p ∧ q) := fun h h1 => 
  match h with 
  | Or.inl hnp => hnp h1.1
  | Or.inr hnq => hnq h1.2

-- The following ones are a harder to prove. Don't hesitate to skip them or ask your
-- tutors if you get stuck

example : ¬(p ↔ ¬p) := fun h => 
    -- (fun hp => h.1 hp) this is an implication
    have hp : p := h.2 (fun hp => h.1 hp hp)
    h.1 hp hp

-- example : ¬¬(¬¬p → p) := fun h => nomatch h (fun h1 => _)
example : ¬¬(¬¬p → p) := 
  fun hnnnpp => hnnnpp fun hnnp => False.elim (hnnp (fun hp => hnnnpp fun _ => hp))


/- CLASSICAL AXIOMS -/

-- Some tautologies about negation cannot be proven by just assuming the logical
-- connectives as algebraic propositions. Instead, we need to assume these facts
-- as axioms. To have access to these, we need to open a namespace called "Classical".
-- We will learn more about constructive versus classical logic in week 5.
open Classical

-- The following statement is called the _law of excluded middle_.
-- It is assumed as an axiom, which means that it doesn't have to be proved.

#check em p

-- Now use the law of excluded middle to show that the theorem not_or_not is reversible:

theorem not_and : ¬(p ∧ q) → (¬ p ∨ ¬ q) := fun h => 
  match (em p) with 
  | Or.inr hnp => Or.inl hnp
  | Or.inl hp => 
    match (em q) with 
    | Or.inr hnq => Or.inr hnq
    | Or.inl hq => Or.inr (nomatch h ⟨hp,hq⟩)

-- Also, we can now deal better with double negations:

example : ¬¬p ↔ p := 
  match (em p) with 
  | Or.inr hnp => ⟨fun hnnp => nomatch hnnp hnp, fun hp hnp => hnp hp⟩
  | Or.inl hp => ⟨fun _ => hp, fun _ hnp => hnp hp⟩

end
