/- Even more induction! -/
set_option trace.Meta.Tactic.simp true

variable (r : α → α → Prop)

-- The reflexive transitive closure of `r` as an inductive predicate
inductive RTC : α → α → Prop where
  -- Notice how declaring `r` as a `variable` instead of as a parameter instead of declaring it
  -- directly as a parameter of `RTC` means we don't have to write `RTC r a a` inside the
  -- declaration of `RTC`. This also works with recursive `def`s!
  | refl : RTC a a
  | trans : r a b → RTC b c → RTC a c

-- We have arbitrarily chosen a "left-biased" definition of `RTC.trans`, but can easily show the
-- mirror version by induction on the predicate
theorem RTC.trans' : RTC r a b → r b c → RTC r a c := by
  intros hab hbc
  induction hab with
  | refl => exact RTC.trans hbc RTC.refl
  -- `a/b/c` in the constructor `RTC.trans` are marked as *implicit* because we didn't specify them
  -- explicitly.
  -- Just like in other contexts, we can use `@` to specify/match implicit parameters in `induction`.
  | @trans a a' b haa' ha'b ih => 
    apply RTC.trans 
    exact haa' 
    exact (ih hbc)   

open Nat

-- By the way, we can leave out `:= fun p1 ... => match p1, ... with` at `def`
def double : Nat → Nat
  | zero   => 0
  | succ n => succ (succ (double n))

-- The tactic injection proves that constructors like succ are injective and that they are distinct
theorem double.inj : double n = double m → n = m := by
  intro h
  -- Try to finish this proof. You might find that the inductive case is impossible to solve!
  -- Do you see a different approach? If not, read on!
  induction n generalizing m with
  | zero => cases m <;> trivial
  | succ n h1 => 
    cases m with 
    | zero => contradiction
    | succ m => 
      rw [double] at h
      -- h: succ (succ (double n)) = double (succ m)
      injection h with h -- h: succ (double n) = succ (double m)
      injection h with h -- double n = double m
      rw [h1 h]

-- The issue with the above approach is that our inductive hypothesis is not sufficiently general!
-- When we begin induction, we have already fixed (introduced) a particular `m`, but for the inductive
-- step we need the inductive hypothesis for a *different* m.
-- We could avoid this by carefully introducing `m` (and `h`, which depends on it) only after `induction`:
-- ```
-- theorem double.inj : ∀ m, double n = double m → n = m := by
--   induction n with
--   | zero => intro m h; ...
--   ...
-- ```
-- `induction` even allows us to apply a tactic before *each* case:
-- ```
-- theorem double.inj : ∀ m, double n = double m → n = m := by
--   induction n with
--       intro m h
--   | zero => ...
--   ...
-- ```
-- However, it turns out that we do not have to change the theorem statement at all: if we simply say
-- ```
-- induction n generalizing m with
-- ```
-- then `induction` will automatically `revert` (yes, that's also a tactic) and re`intro`duce the variable(s)
-- before/after induction for us! So add `generalizing m` above, see how the inductive hypothesis is
-- affected, and then go finish that proof!


/- Partial & dependent maps -/

-- *Partial maps* are a useful data type for the semantics project and many other topics.
-- They map *some* keys of one type to values of another type.
abbrev Map (α β : Type) := α → Option β
-- We express partiality via the `Option` type, which either holds `some b` for `b : β`, or `none`.
-- Ctrl+click it for the whole definition.

namespace Map

def empty : Map α β := fun k => none

-- If we wanted a partial map for programming, we might choose a more efficient implementation such
-- as a search tree or a hash map. If, on the other hand, we are only interested in using it in a
-- formalization, a simple function like above is usually the better solution. For example, a
-- simple typing context `Γ` can be formalized as a partial map from variable names to their types.

-- The function-based definition makes defining operations such as a map update quite easy:

/-- Set the entry `k` of the map `m` to the value `v`. All other entries are unchanged. -/
def update [DecidableEq α] (m : Map α β) (k : α) (v : Option β) : Map α β := 
  fun x => if k = x then v else m x

-- def update [DecidableEq α] (m : Map α β) (k : α) (v : Option β) : Map α β := 
--   fun k' => if k = k' then v else m k'

-- A `scoped` notation is activated only when opening/inside the current namespace
scoped notation:max m "[" k " ↦ " v "]" => update m k v

theorem apply_update [DecidableEq α] (m : Map α β) : m[k ↦ v] k = v := by simp [update]  

-- hint: use function extensionality (`apply funext`)
theorem update_self [DecidableEq α] (m : Map α β) : m[k ↦ m k] = m := by
-- funext {f₁ f₂ : ∀ (x : α), β x} (h : ∀ x, f₁ x = f₂ x) : f₁ = f₂
  funext k'  -- an abbreviation for `apply funext; intro k'`
  by_cases h : k = k' <;> simp [update, h]

end Map

-- One interesting generalization of partial maps we can express in Lean are *dependent maps* where
-- the *type* of the value may depend on the key:
abbrev DepMap (α : Type) (β : α → Type) := (k : α) → Option (β k)

namespace DepMap

def empty : DepMap α β := fun k => none

-- If we try to define `update` as above, it turns out that we run into a type error!
-- You may want to use the "dependent if" `if h : p then t else e` that makes a *proof* of
-- the condition `p` available in each branch: `h : p` in the `then` branch and `h : ¬p` in the
-- `else` branch. You should then be able to use rewriting (e.g. `▸`) to fix the type error.
def update [DecidableEq α] (m : DepMap α β) (k : α) (v : Option (β k)) : DepMap α β :=
  fun x => if h : k = x then h ▸ v else m x
    -- fun x => if k = x then v else m x

scoped notation:max m "[" k " ↦ " v "]" => update m k v

-- This one should be as before...
theorem apply_update [DecidableEq α] (m : DepMap α β) : m[k ↦ v] k = v := by simp [update]

-- ...but this one is where the fun starts: try replicating the corresponding `Map` proof...
theorem update_self [DecidableEq α] (m : DepMap α β) : m[k ↦ m k] = m := by
  funext k'  -- an abbreviation for `apply funext; intro k'`
  by_cases h : k = k' 
  case inl => 
    rw [h]
    simp [update]
  case inr => 
    simp [h, update]
-- and you should end up with an unsolved goal containing a subterm of the shape `(_ : a = b) ▸ c`. This
-- is the rewrite from `update`; the proof is elided as `_` by default because, as we said in week 1, Lean
-- considers all proofs of a proposition as equal, so we really don't care what proof is displayed there.
-- So how do we get rid of the `▸`? We know it is something like a match  on `Eq.refl`; more formally,
-- both `▸` and such a match compile down to an application of `Eq`'s *recursor* (week 3).
-- We know matches/recursors reduce ("go away") when applied to a matching constructor application,
-- i.e. for `▸` we have `(rfl ▸ c) ≡ c`.
-- So why didn't `simp` reduce away `(_ : a = b) ▸` if it works for `rfl` and all proofs are the same?
-- Well, all proofs of a *single* proposition are the same, but `rfl` is not a proof of `a = b` unless
-- `a` and `b` are in fact the same term! Thus the general way to get rid of `(_ : a = b) ▸` is to
-- first rewrite the goal with a proof of the very equality `a = b`. After that, `simp`, or definitional
-- equality in general, will get rid of the `▸`.
-- Now, for technical reasons we should use `rw` instead of `simp` itself to do this rewrite. The short
-- answer as to why that is is that `simp` tries to be *too clever* in this case: it will rewrite `a = b`
-- on both sides of the `▸` individually, which usually makes it more flexible (week 4, slide pages 17 & 21),
-- but in this case unfortunately leads to a type-incorrect proof. The "naive" strategy of `rw`, which will
-- simply replace all `a` with `b` everywhere simultaneously by applying the `Eq` recursor once at the root,
-- turns out to be the better approach in this case.
-- Phew, that was a lot of typing (in the theoretic sense and on my keyboard). If you can't get the proof to
-- work, don't worry about it, we will not bother you with this kind of "esoteric" proof again. If, on the
-- other hand, you are interested in this kind of strong dependent typing, we may have an interesting variant
-- of the semantics project to offer you next week!

end DepMap

open List Nat

/- Insertion Sort -/

-- Let's implement insertion sort in Lean and show that the resulting `List` is indeed sorted.
-- To that end, we first assume that the type `α` is of the type class `LE`, meaning that we can use
-- the symbol `≤` (\le) as notation.
-- We also assume (notice that cool dot notation) that this relation is decidable:
variable [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)]

-- First, we want to define a predicate that holds if a list is sorted.
-- The predicate should have three constructors:
-- The empty list `[]` and the single element list `[a]` are sorted,
-- and we can add `a` to the front of a sorted list `b :: l`, if `a ≤ b`.
inductive Sorted : List α → Prop where 
  | nil : Sorted []
  | single : Sorted [a]
  | cons_cons : a ≤ b → Sorted (b::l) → Sorted (a::b::l) 

-- The main ingredient to insertion sort is a function `insertInOrder` which inserts
-- a single element `a` before the first entry `x` of a list for which `a ≤ x` holds.
-- Define that function by recursion on the list. Remember that `≤` is decidable.
-- def insertInOrder (a : α) (xs : List α) : List α := 
--   let rec helper (a : α) (xs : List α) (ys : List α) : List α := 
--     match xs with  
--     | [] => ys ++ [a]
--     | x :: xs => if a ≤ x then ys ++ (a::x::xs) else helper a xs (ys ++ [x])
--   helper a xs []

def insertInOrder (a : α) (xs : List α) : List α := 
  match xs with
  | [] => [a]
  | x :: xs =>
    if a ≤ x then
      a :: x :: xs
    else
      x :: insertInOrder a xs

-- Now, check whether the function actually does what it should do.
#eval insertInOrder 4 [1, 3, 4, 6, 7]
#eval insertInOrder 4 [1, 2, 3]

-- Defining `insertionSort` itself is now an easy recursion.
-- def insertionSort (xs : List α) : List α := 
--   let rec helper (xs : List α) (ys : List α) : List α := 
--     match xs with 
--     | [] => ys
--     | x :: xs => helper xs (insertInOrder x ys)
--   helper xs []

def insertionSort (xs : List α) : List α := 
  match xs with
  | []      => []
  | x :: xs => insertInOrder x (insertionSort xs)

-- Let's test the sorting algorithm next.
#eval insertionSort [6, 2, 4, 4, 1, 3, 64]
#eval insertionSort [1, 2, 3]
#eval insertionSort (Nat.repeat (fun xs => xs.length :: xs) 500 [])

-- Now we want to move on to actually verify that the algorithm does what it claims to do!
-- To prove this, we don't need the relation to be transitive, but we need to assume the following property:
variable (antisymm : ∀ {x y : α}, ¬ (x ≤ y) → y ≤ x)

-- Okay, now prove the statement itself!
-- Hints:
--   * You might at one point have the choice to either apply induction on a list or on a witness of `Sorted`.
--     Choose wisely.
--   * Remember the tactic `by_cases` from the fifth exercise!
theorem sorted_insertInOrder {xs : List α} (h : Sorted xs) : Sorted (insertInOrder x xs) := by
  induction h with
  | nil => exact Sorted.single
  | @single a => 
    simp only [insertInOrder]
    by_cases hxa : x ≤ a <;> simp only [hxa]
    case inl => exact Sorted.cons_cons hxa Sorted.single
    case inr => exact Sorted.cons_cons (antisymm hxa) Sorted.single
  | @cons_cons a b l hab hbl ih => 
    simp only [insertInOrder]
    by_cases hxa : x ≤ a <;> simp only [hxa]
    case inl => exact Sorted.cons_cons hxa (Sorted.cons_cons hab hbl)
    case inr => 
      by_cases hxb : x ≤ b <;> simp only [hxb]
      case inl => exact Sorted.cons_cons (antisymm hxa) (Sorted.cons_cons hxb hbl)
      case inr =>
        simp only [insertInOrder, hxb] at ih
        exact Sorted.cons_cons hab ih

theorem sorted_insertionSort (as : List α) : Sorted (insertionSort as) := 
  match as with 
  | nil => Sorted.nil
  | x :: xs => sorted_insertInOrder antisymm (sorted_insertionSort xs)

-- Here's a "soft" question: Have we now fully verified that `insertionSort` is a sorting algorithm?
-- What other property would be an obvious one to verify (which you don't have to do here)?

