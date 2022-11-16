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


namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α

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

def length {α : Type u} (xs : List α) : Nat := 
  match xs with 
  | nil => 0
  | cons _ xs => 1 + (length xs)

def as := cons 1 (cons 2 (cons 3 nil))
def bs := cons 4 nil

#eval length (append as bs) = length as + length bs
  
end List
end Hidden

