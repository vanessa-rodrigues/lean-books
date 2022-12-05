namespace Hidden
-- 1
inductive Nat where 
  | zero : Nat 
  | succ : Nat → Nat 
deriving Repr 

def add : Nat → Nat → Nat 
  | Nat.zero, k => k
  | Nat.succ n, k => Nat.succ (add n k)

#eval add (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)

def mul : Nat → Nat → Nat 
  | Nat.zero, _ => Nat.zero
  | Nat.succ n, k => add k (mul n k)

#eval mul (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero))

def pow (n m : Nat) : Nat := 
  match m with 
  | Nat.zero => Nat.succ Nat.zero 
  | Nat.succ m => mul n (pow n m)

#eval pow (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

--2
inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α
deriving Repr 

notation  (priority := high) "[" "]" => List.nil   -- `[]`
infixr:67 (priority := high) " :: "  => List.cons  -- `a :: as`

-- as a warm-up exercise, let's define concatenation of two lists
def append (as bs : List α) : List α := 
  match as with 
  | [] => bs 
  | x :: xs => x :: (append xs bs)

infixl:65 (priority := high) " ++ " => append

def reverse (xs : List α) : List α := 
  match xs with 
  | List.nil => List.nil
  | List.cons x xs => (reverse xs) ++ (List.cons x List.nil)

@[simp]theorem append_nil (xs: List α) : reverse (xs ++ []) = [] ++ reverse xs := by 
  induction xs 
  . case nil => rfl 
  . case cons x xs h => simp [h, append, reverse]

@[simp]theorem nil_append (xs: List α) : reverse ([] ++ xs) = reverse xs ++ [] := by 
  induction xs 
  . case nil => rfl 
  . case cons x xs h => 
    rw [reverse]
    sorry
    -- simp [h, append, reverse]


theorem reverse_append (xs : List α) (ys : List α) : reverse (xs ++ ys) = reverse ys ++ reverse xs := by
  induction xs
  . case nil => sorry
  . case cons x xs => 
    sorry


#eval reverse (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))

theorem double_reverse (xs : List α) : reverse (reverse xs) = xs := by
  induction xs
  . case nil => rfl
  . case cons x xs h => 
    rw [reverse]
    sorry
    -- simp [h] 
    -- simp [reverse, append]

    -- simp_all [reverse, h, append]

-- 3   


end Hidden 

-- 4 

inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
deriving Repr

namespace Vector

def v1 := Vector.cons 5 (Vector.cons 0 Vector.nil)
def v2 := Vector.cons 8 (Vector.cons 5 (Vector.cons 0 Vector.nil))

-- def add [Add α] : Vector α n → Vector α n → Vector α n
--   | nil,       nil       => nil
--   | cons a as, cons b bs => cons (a + b) (add as bs)


-- def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
--   Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
--     (fun h : 0 = n + 1 => Nat.noConfusion h)
--     (fun (a : α) (m : Nat) (as : Vector α m) =>
--      fun (h : m + 1 = n + 1) =>
--        Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

-- def tail (v : Vector α (n+1)) : Vector α n :=
--   tailAux v rfl

-- def append: {n m : Nat} → Vector α n → Vector α m → Vector α (n + m)
--   -- | 0,   nil,       nil       => nil
--   |  0, _, nil,       k       => k
--   | cons a as, k => cons a (append as (tail k))

-- #eval add v1 v2

end Vector

-- 5
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => (eval v e₁) + (eval v e₂)
  | times e₁ e₂ => (eval v e₁) * (eval v e₂)

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

#eval simpConst sampleExpr

def fuse : Expr → Expr := sorry

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry


example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬ (True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1+1 := by
  decide

#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (Eq.refl true)

#check @of_decide_eq_true
-- ∀ {p : Prop} [Decidable p], decide p = true → p

#check @decide
-- (p : Prop) → [Decidable p] → Bool


example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- |- a * (b * c) = a * (c * b)
    lhs
    -- |- a * (b * c)
    congr
    -- 2 goals : |- a and |- b * c
    rfl
    -- |- b * c
    rw [Nat.mul_comm]


#eval 4 = 4

def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

end Set

theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
