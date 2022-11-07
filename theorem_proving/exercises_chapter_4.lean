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
  (fun h : (∀ x, p x ∨ r) => (Or.elim (em r) 
    (fun hr => Or.inr hr) 
    (fun hnr => Or.inl (fun α => have h1 := (h α)
      h1.elim 
      (fun h2 => h2)
      (fun hr => False.elim (absurd hr hnr)) 
    ))))
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
    | ⟨w, hw⟩ =>
      let l := shaves barber barber
      Or.elim (em l)
        (fun h1 => absurd h1 (w h1))
        (fun h1 => absurd (hw h1) h1)

-- 4
def even (n : Nat) : Prop := ∃ m, n = 2 * m

-- I would like knowing a way that allows me to check if this is correct
def prime (n : Nat) : Prop := ¬∃ m, (Nat.mod n m = 0) ∧ ¬(m = 1) ∧ ¬(m = n) 

def infinitely_many_primes : Prop := ∀ n, ∃ m, (prime n) ∧ (prime m) ∧ (m > n) 

def Fermat_prime (n : Nat) : Prop := ∃ m, m < 5 ∧ (Nat.pow 4 m) = n ∧ prime n

def infinitely_many_Fermat_primes : Prop := ∀ n, ∃ m, (Fermat_prime n) ∧ (Fermat_prime m) ∧ (m > n) 

def goldbach_conjecture : Prop := ∀ n, ∃ m, ∃ s, n > 2 ∧ prime m ∧ prime s ∧ n = (m + s)

def Goldbach's_weak_conjecture : Prop := ∀ n: Nat, ∃ x, ∃ y, ∃ z, n > 5 ∧ (Nat.mod n 2) = 1 ∧ n = x + y + z ∧ prime x ∧ prime y ∧ prime z

def Fermat's_last_theorem : Prop := ∀ n : Nat, ¬∃ x, ¬∃ y, ¬∃ z,  n > 2 ∧ (Nat.pow x n) + (Nat.pow y n) = (Nat.pow z n)

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
  (fun h => fun α => byContradiction (fun h1 => absurd (Exists.intro α h1) h))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  Iff.intro
  (fun h => match h with 
    | ⟨w, hw⟩ => fun h1 => 
      have hp := h1 w
      absurd hw hp)
  (fun h => byContradiction (fun h1 => absurd 
    (fun α => byCases 
      (fun h2 : p α => False.elim (absurd ⟨α,h2⟩ h1))
      (fun h2 => h2)) h))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
  Iff.intro
  (fun h => fun α => fun hpa => absurd (Exists.intro α hpa) h)
  (fun h => fun h1 => match h1 with 
    | ⟨w, hw⟩ => absurd hw (h w))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
  Iff.intro 
  (fun h => byContradiction 
  (fun h1 => absurd 
      (fun α => byCases 
      (fun hpa : p α => hpa)
      (fun hnp => False.elim (absurd (Exists.intro α hnp) h1))) h)) 
  (fun h => match h with 
    | ⟨w, hw⟩ => fun h1 => absurd (h1 w) hw)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  Iff.intro
  (fun h => fun h1 => match h1 with
  | ⟨w,hw⟩ => (h w) hw)
  (fun h => fun α => fun h1 => h (Exists.intro α h1))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  Iff.intro
  (fun ⟨b, (hb : p b → r)⟩ => fun h1 => hb (h1 b)) -- removed the exists already ?
  (fun h => byCases
    (fun hap : ∀ x, p x => Exists.intro a (fun _ => h hap))
    (fun hnap : ¬ ∀ x, p x =>
    byContradiction
      (fun hnex : ¬ ∃ x, p x → r =>
        have hap : ∀ x, p x :=
          fun x =>
          byContradiction
            (fun hnp : ¬ p x =>
              have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
              show False from hnex hex)
        show False from hnap hap)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
  Iff.intro
  (fun h => match h with
    | ⟨w,hw⟩ => fun hr => Exists.intro w (hw hr))
  (fun h => Or.elim (em r) 
  (fun hr => sorry)
  (fun hnr => Exists.intro a (fun hr => False.elim (hnr hr))))

