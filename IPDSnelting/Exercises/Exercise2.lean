section
variable (α : Type) (p q : α → Prop) (r : α → α → Prop)

/- UNIVERSAL QUANTIFICATION -/

-- We can leave off `: α` if Lean can infer it (here via `p`/`q`)
example : (∀ x, p x) → (∀ x, p x → q x) → (∀ x, q x) := fun h h1 α => (h1 α) (h α) 

-- The reverse direction of the slides example
example : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := fun h => ⟨fun α => (h α).1, fun α => (h α).2⟩ 

-- TODO: Prove the corresponding forward/reverse lemma(s) for `∨` (that hold)!
-- hint: input `∀` as `\all`

-- We can bind multiple variables in a single `∀`
example : (∀ x y, r x y) → (∀ y x, r x y) := fun h y x => h x y

/- EXISTENTIAL QUANTIFICATION -/

/-
Interestingly, in contrast to the universal quantifier, the existential quantifier is not primitive
but can be specified as an inductive type:
```
inductive Exists (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
```
That is, `Exists.intro` takes/offers a "witness" and a proof that the predicate holds for the witness.
Instead of `Exists (fun x => p x)`, we can also write `∃ x, p x` (input `∃` as `\ex`).
-/

example : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ (∃ x, q x) := fun h => 
  match h with 
  | ⟨w,hw⟩ => ⟨Exists.intro w hw.1, Exists.intro w hw.2⟩  

example : ¬(∃ x, p x) → (∀ x, ¬ p x) := fun h α hpa => nomatch h ⟨α,hpa⟩ 

example : (∀ x, ¬ p x) → ¬(∃ x, p x) := fun h h1 => 
  match h1 with 
  | ⟨w,hw⟩ => (h w) hw

example : (∃ x, ¬ p x) → ¬ (∀ x, p x) := fun h h1 => 
  match h with 
  | ⟨w,hw⟩ => hw (h1 w)

section
open Classical
-- The following example can only be solved using the classical axioms
-- This one is pretty tricky again, don't feel bad about skipping it
-- hint: use the following helper theorem that can be derived from `em`:
#check byContradiction
-- hint: you may even need to use it more than once
example : ¬(∀ x, p x) → (∃ x, ¬ p x) := fun h => byContradiction
  (fun h1 => h (fun α => byContradiction (fun h2 => h1 ⟨α,h2⟩))) 
end

-- TODO: Decide for yourself what variables you need to model and prove the following
-- important real-world observation, which is sometimes called "drinker paradox":
--   "If there is at least one person in the pub, then there is someone in the pub such that,
--    if (s)he is drinking, then everyone in the pub is drinking."
-- hint: you can define "is in pub" either as a predicate variable on a "Person" type (`(Person : Type)`),
--   or, more simply, directly as a type "Occupant" since we are not interested in persons outside the pub
-- hint: you might need classical logic again
section Drinker
open Classical
variable (Occupant: Type) (drinking : Occupant -> Prop)

example : (∃ x: Occupant, True) → ∃ x, drinking x → ∀ x', drinking x' := 
  fun h => 
    match h with 
    | ⟨w,_⟩ => match em (∃ x', ¬ drinking x') with
      | Or.inl drink => 
        match drink with 
        | ⟨w',hw'⟩ => Exists.intro w' (fun h1 => False.elim (hw' h1))
      | Or.inr nodrink => Exists.intro w (fun _ x' => byContradiction (fun h2 => nodrink ⟨x',h2⟩ ))

end Drinker

/- EQUALITY -/

example : ∀ a b c : α, a = b → b = c → a = c := fun a b c h h1 => h ▸ h1 ▸ rfl

example : ∀ a : α, ∃ b : α, b = a := fun _ => ⟨_,rfl⟩ 

-- "`Eq` is the least reflexive relation"
example : (∀ a, r a a) → (∀ a b, a = b → r a b) := fun h a b h1 => 
  match h1 with 
  | Eq.refl a => (h a)

end
