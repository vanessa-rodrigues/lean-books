open Classical

-- 1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  Iff.intro
  (fun h: (∀ x, p x ∧ q x) => show (∀ x, p x) ∧ (∀ x, q x) from 
    And.intro (fun y: α => (h y).left) (fun y: α => (h y).right))
  (fun h: (∀ x, p x) ∧ (∀ x, q x) => show (∀ x, p x ∧ q x) from 
    (fun y : α => And.intro (h.left y) (h.right y)))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  fun h : (∀ x, p x → q x) => fun h1 : (∀ x, p x) => (fun x : α => (h x) (h1 x))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  fun h : (∀ x, p x) ∨ (∀ x, q x) => 
    h.elim
    (fun h1 => fun x : α => Or.inl (h1 x))
    (fun h2 => fun x : α => Or.inr (h2 x))

-- 2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := 
  fun h : α => Iff.intro
    (fun h1 => h1 h)
    (fun hr => fun _ : α => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
  Iff.intro
  (fun h : (∀ x, p x ∨ r) => sorry)

  (fun h : (∀ x, p x) ∨ r => h.elim 
    (fun h1 => fun α => Or.inl (h1 α))
    (fun h1 => fun α => Or.inr h1))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
  Iff.intro
  (fun h : ∀ x, r → p x => fun hr => fun α => (h α) hr)
  (fun h : r → ∀ x, p x => fun α => fun hr => (h hr) α) 

-- 3
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  match (h barber) with
    | ⟨l, r⟩ =>
      let w := shaves barber barber
      Or.elim (em w)
        (fun a => absurd a (l a))
        (fun b => absurd (r b) b)

-- 4
def even (n : Nat) : Prop := ∃ m, n = 2 * m

-- I would like knowing a way that allows me to check this is correct
def prime (n : Nat) : Prop := ¬∃ m, (Nat.mod n m = 0) ∧ ¬(m = 1) ∧ ¬(m = n) 

def infinitely_many_primes : Prop := ∀ n, (prime n) → ∃ m, (prime m) ∧ (m > n) 

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry


-- 5
variable (r : Prop)

example : (∃ x : α, r) → r := fun h => 
  Exists.elim h
  (fun _ => fun r => r)
example : (∃ x : α, r) → r := fun h => 
  match h with
  | ⟨_, hw⟩ => hw

example (a : α) : r → (∃ x : α, r) := fun hr => Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  Iff.intro 
  (fun h => match h with 
    | ⟨w,hw⟩ => And.intro (Exists.intro w hw.left) hw.right)
  (fun h => match h with 
    | ⟨w,hw⟩ => w.elim (fun α => fun h1 => Exists.intro α (And.intro h1 hw)))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  Iff.intro 
  (fun h => match h with
  | ⟨w,hw⟩ => (hw.elim
      (fun h1 => Or.inl (Exists.intro w h1))
      (fun h1 => Or.inr (Exists.intro w h1))))
  (fun h => h.elim
    (fun h1 => match h1 with
      | ⟨w,hw⟩ => Exists.intro w (Or.inl hw))
    (fun h1 => match h1 with
      | ⟨w,hw⟩ => Exists.intro w (Or.inr hw)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  Iff.intro
  (fun h => fun h1 => match h1 with
    | ⟨w,hw⟩ => absurd (h w) hw)
  (fun h => sorry)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  Iff.intro
  (fun h => match h with 
    | ⟨w, hw⟩ => fun h1 => 
      have hp := h1 w
      absurd hw hp)
  (fun h => sorry)

-- example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry

-- example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  Iff.intro
  (fun h => fun h1 => match h1 with
  | ⟨w,hw⟩ => (h w) hw)
  (fun h => sorry)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  Iff.intro
  (fun h => fun h1 => sorry)
  (fun h =>  sorry)

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
  Iff.intro
  (fun h => match h with
    | ⟨w,hw⟩ => fun hr => Exists.intro w (hw hr))
  (fun h => Exists.intro a (fun hr => sorry))
