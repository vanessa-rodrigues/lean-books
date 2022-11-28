namespace Hidden
inductive Bool where
  | false : Bool
  | true  : Bool

def and (a b : Bool) : Bool :=
  match a with
  | Hidden.Bool.true => b
  | Hidden.Bool.false => Hidden.Bool.false

def or (a b : Bool) : Bool :=
  match a, b with
  | Hidden.Bool.true, _ => Hidden.Bool.true
  | _, Hidden.Bool.true => Hidden.Bool.true
  | _, _ => Hidden.Bool.false

def not (a : Bool) : Bool :=
  match a with
  | Hidden.Bool.true => Hidden.Bool.false
  | Hidden.Bool.false => Hidden.Bool.true

end Hidden


-- namespace Hidden
-- inductive List (α : Type u) where
-- | nil  : List α
-- | cons : α → List α → List α

-- namespace List
-- def append (as bs : List α) : List α :=
--  match as with
--  | nil       => bs
--  | cons a as => cons a (append as bs)

-- theorem nil_append (as : List α) : append nil as = as :=
--  rfl

-- theorem cons_append (a : α) (as bs : List α)
--                     : append (cons a as) bs = cons a (append as bs) :=
--  rfl

-- #check @Nat.recOn
-- -- @Nat.recOn : {motive : Nat → Sort u_1} →
-- -- (t : Nat) → motive Nat.zero → ((n : Nat) → motive n → motive (Nat.succ n)) → motive t

-- #check @List.recOn
-- -- @List.recOn : {α : Type u_2} →
-- -- {motive : List α → Sort u_1} →
-- -- (t : List α) → motive nil → ((a : α) → (a_1 : List α) → motive a_1 → motive (cons a a_1)) → motive t

-- theorem append_nil (as : List α) : append as nil = as :=
--   List.recOn (motive := fun xs => append xs nil = xs) as 
--   (by simp [nil_append]) -- rfl also works 
--   (fun α xs f => by simp [cons_append, f])

-- theorem append_assoc (as bs cs : List α)
--         : append (append as bs) cs = append as (append bs cs) :=
--   List.recOn (motive := fun xs => append (append xs bs) cs = append xs (append bs cs)) as 
--   rfl
--   (fun α xs f => by simp [cons_append, f])

-- def length {α : Type u} (xs : List α) : Nat := 
--   match xs with 
--   | nil => 0
--   | cons _ xs => 1 + (length xs)

-- def as := cons 1 (cons 2 (cons 3 nil))
-- def bs := cons 4 nil

-- #eval length (append as bs) = length as + length bs
  
-- end List
-- end Hidden

open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl

open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k -- occurs in the goal 
  exact hz   -- goal is p 0
  apply hs   -- goal is a : ℕ ⊢ p (succ a)

open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  exact hz   -- goal is p 0
  apply hs   -- goal is a : ℕ ⊢ p (succ a)


example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d) -- not clear
  show a + d = d + a
  rw [Nat.add_comm]

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction

namespace Hidden
inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
end Hidden

namespace Hidden
theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := by 
  rw [h₁, h₂]

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) := by
  simp [h]
  
end Hidden

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end


-- -------------------------- EXERCISES --------------------------------------
-- 1

namespace Hidden

def mul (n1 : Nat) (n2 : Nat) : Nat := 
  match n1, n2 with
  | zero, _ => zero
  | _, zero => zero
  | x, succ y => Nat.add x (mul x y)

instance : Mul Nat where
  mul := mul

#eval mul 3 0

def pred (n : Nat) : Nat :=
  match n with
  | zero => 0 
  | succ x => x

#eval pred 4

def sub (n : Nat) (m : Nat) : Nat := 
  match n,m with
  | zero, _ => 0
  | a, zero => a
  | a, succ b => if b >= (a - 1) then 0 else pred (sub a b)
  
#eval sub 3 6

def exp (n : Nat) (m : Nat) : Nat := 
  match m with 
  | zero => 1 
  | succ x => mul n (exp n x)

#eval exp 3 3

theorem mul_zero (m : Nat) : m * zero = zero := by
  cases m
  case zero => rfl
  case succ x => rfl

theorem zero_mul (m : Nat) : zero * m = zero := by
  cases m
  case zero => rfl
  case succ x => rfl

theorem mul_com (n m : Nat) : m * n = n * m := by
  cases n
  case zero => simp [mul_zero, zero_mul]
  case succ x => sorry

theorem mul_distr (a b c: Nat) : a * (b + c) = a * b + a * c := sorry 

end Hidden

namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
deriving Repr

namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
 rfl

theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl

#check @Nat.recOn
-- @Nat.recOn : {motive : Nat → Sort u_1} →
-- (t : Nat) → motive Nat.zero → ((n : Nat) → motive n → motive (Nat.succ n)) → motive t

#check @List.recOn
-- @List.recOn : {α : Type u_2} →
-- {motive : List α → Sort u_1} →
-- (t : List α) → motive nil → ((a : α) → (a_1 : List α) → motive a_1 → motive (cons a a_1)) → motive t

theorem append_nil (as : List α) : append as nil = as :=
  List.recOn (motive := fun xs => append xs nil = xs) as 
  (by simp [nil_append]) -- rfl also works 
  (fun α xs f => by simp [cons_append, f])

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  List.recOn (motive := fun xs => append (append xs bs) cs = append xs (append bs cs)) as 
  rfl
  (fun α xs f => by simp [cons_append, f])

-- 2 
def length {α : Type u} (xs : List α) : Nat := 
  match xs with 
  | nil => 0
  | cons _ xs => 1 + (length xs)

def as := cons 1 (cons 2 (cons 3 nil))
def bs := cons 4 nil

#eval length (append as bs) = length as + length bs

def reverse {α : Type u} (xs : List α) : List α := 
  match xs with 
  | nil => nil
  | cons x xs => append (reverse xs) (cons x nil)

#eval reverse (cons 1 (cons 2 (cons 3 nil)))

theorem length_nil (s : List α) (h : s = nil) : length s = 0 := by 
  rw [h]
  rfl

theorem length_theorem (s t : List α) : length (append s t) = length s + length t := sorry

theorem length_reverse (t : List α) : length (reverse t) = length t := sorry

theorem reverse_theorem (t : List α) : reverse (reverse t) = t := sorry

  
end List
end Hidden

-- 3 
namespace Hidden

inductive Expr where
  | const : Nat -> Expr 
  | var : Nat -> Expr 
  | plus : Expr -> Expr -> Expr 
  | times : Expr -> Expr -> Expr 
deriving Repr

def eval (e : Expr) : Nat := 
  match e with
  | Expr.const x => x
  | Expr.var x => x
  | Expr.plus e1 e2 => (eval e1) + (eval e2)
  | Expr.times e1 e2 => (eval e1) * (eval e2)

#eval eval (Expr.plus (Expr.const 5) (Expr.var 3))

end Hidden

-- 4
