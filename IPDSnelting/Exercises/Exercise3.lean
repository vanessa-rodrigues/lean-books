/- NATURAL NUMBERS

We saw the definition of the natural numbers `Nat` and the addition on them on the slides.
Since we want to define it ourselves and not use Lean's built-in version, we will call ours `Nat'`.
 -/
inductive Nat' : Type
  | zero : Nat'
  | succ : Nat' → Nat'
deriving Repr

open Nat'

def add (m n : Nat') : Nat' :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

-- Let us now try to recursively define multiplication on the `Nat'`.
def mul (m n : Nat') : Nat' := 
  match n with 
  | zero => zero 
  | succ n => add m (mul m n)

-- Next, check your definition of `mul` by evaluating a few examples. This can be done with the
-- command `#eval`.

#eval mul (Nat'.succ (Nat'.succ Nat'.zero)) (Nat'.succ (Nat'.succ Nat'.zero))

-- Let's define `≤` as an inductive predicate on `Nat'`s!
inductive LE' : Nat' → Nat' → Prop where
  | refl (n : Nat') : LE' n n
  -- TODO: We're off to a good start since `≤` is certainly reflexive, but something is still
  -- missing (or else we'd just redefine `Eq` for `Nat'`s). Can you think of one more constructor
  -- that makes it so `LE' n m` holds whenever we would intuitively expect `n ≤ m` to hold?
  -- hint: it remains to be shown that `LE' n m` should hold when `m` is *greater* than `n`, so
  -- the new constructor should probably involve `Nat'`'s `succ` constructor to reach those greater numbers.
  -- hint: it should be an *inductive* case, meaning using another `LE'` application as an assumption
  -- note: `LE'` could also be defined in terms of `add`, but that makes working with it awkward,
  -- so let's not do that.
  | succ : LE' n m -> LE' n (succ m)

-- Now let's prove some things about `LE'`. But first we'll give it the standard notation.
infix:50 " ≤ " => LE'

example (n : Nat') : n ≤ succ (succ n) := LE'.succ (LE'.succ (LE'.refl _))

-- This one is a bit harder: we will need induction!
-- As described on the slides, induction is just a special case of recursion
theorem le_add (m n : Nat') : m ≤ add m n :=
  match n with
  -- This is the base case
  | zero => LE'.refl _
  -- This is the inductive case. You probably want to use `le_add m n` (the inductive hypothesis) somewhere inside of it!
  | succ n =>
    -- Lean automatically converts `add m (succ n)` to `succ (add m n)` for us when necessary, but it can help
    -- to make the conversion explicit. `show` simply lets us restate the goal, using any definitionally equal type.
    show m ≤ succ (add m n) from
    LE'.succ (le_add m n)

#check @Eq.subst

-- Now try proving this theorem on `add` using the same induction scheme
theorem zero_add (n : Nat') : add zero n = add n zero := 
  match n with
  | zero => rfl
  | succ m => -- show add zero (succ n) = add (succ n) zero 
      show succ (add zero m) = succ (add m zero) from
      (zero_add m) ▸ rfl

/-
LISTS

The type `List α` of lists on a Type α is defined to be the type on the constructors
`nil : List α`
and
`cons : α → List α → List α`.

We can use `[]` as a notation for `nil` and `x :: xs` as a notation for `cons x xs`.
-/
open List


-- Let's define something we can't in most other functional languages:
-- a function returning the first element of a list given a proof that is is non-empty! (`xs ≠ []` is shorthand for `¬ (xs = [])`)
def hd (xs : List α) : xs ≠ [] → α := fun _ => 
  match xs with 
  | cons x _ => x
-- Did you notice that `hd` is a dependent function? The *type/proposition* of the second parameter depends on the *value* of the first.
-- We can write `hd`s type as `∀ (xs : List α), xs ≠ [] → α` or, equivalently, `(xs : List α) → xs ≠ [] → α`.

/- 
TREES

Define a type `Tree α` of binary trees with node labels of type `α`. Each tree is either a labelled leaf or a labelled inner node with two trees attached to it.
 -/

inductive Tree (α : Type) : Type where
  | leaf : α -> Tree α
  | branch : Tree α -> α -> Tree α -> Tree α

open Tree

-- Now, let us define the depth and the size of a tree. You can use the function `Nat.max` to get the maximum of two natural numbers. The depth of a leaf is 1.
def depth (t : Tree α) : Nat := 
  match t with 
  | leaf _ => 1 
  | branch l _ r => Nat.max (depth l) (depth r) + 1

def size (t : Tree α) : Nat := 
  match t with 
  | leaf _ => 1 
  | branch l _ r => (size l) + (size r) + 1

-- We can turn a tree into a list by traversing it in various ways, depending on whether we add the root
-- before its subtrees (preOrder), between its subtrees (inOrder) or after its subtrees (postOrder).
-- Define preOrder, inOrder, and postOrder as functions `Tree α → List α`.
def preOrder (t : Tree α) : List α := 
  match t with 
  | leaf v => [v]
  | branch l v r => v :: preOrder l ++ preOrder r

def inOrder (t : Tree α) : List α := 
  match t with 
  | leaf v => [v]
  | branch l v r => preOrder l ++ [v] ++ preOrder r

def postOrder (t : Tree α) : List α := 
    match t with 
  | leaf v => [v]
  | branch l v r => preOrder l ++ preOrder r ++ [v]

-- Define a function which returns the mirror image of a given tree.
def mirror (t : Tree α) : Tree α := match t with 
  | leaf v => leaf v 
  | branch l v r => branch (mirror r) v (mirror l)

-- Now we prove two facts about this function:
-- First, we prove that it is involutive (mirroring a tree twice returns the original tree).
-- Then, we prove that the mirror image of two trees is equal, if and only if the trees themselves are.

-- Useful lemmas, if you don't want to use ▸ as much (but it is also just as doable with some `have`s and ▸):
#check @Eq.trans
#check @Eq.symm
#check @congrArg

theorem mirror_involutive (t : Tree α) : mirror (mirror t) = t := 
  match t with 
  | leaf _ => rfl 
  | branch l _ r => show branch .. = _ from -- .. = _ _ _
    Eq.symm (mirror_involutive l) ▸ Eq.symm (mirror_involutive r) ▸ rfl

-- hint: try using `mirror_involutive`
theorem mirror_eq (s t : Tree α) : mirror s = mirror t ↔ s = t := 
  Iff.intro 
  (fun h => 
    have mmsmmt : mirror (mirror s) = mirror (mirror t) := h ▸ rfl
    mirror_involutive s ▸ mirror_involutive t ▸ mmsmmt)
  (fun h => congrArg mirror h)

/- STRUCTURES -/

-- Define the structure `Semigroup α` for a semigroup on a type `α`.
-- Reminder: A semigroup is an algebraic structure with an associative binary operation `mul`.
structure Semigroup (α : Type) where 
  mul : α -> α -> α
  assoc : mul (mul a b) c = mul a (mul b c) 

-- Now extend the structure to one for a monoid on α.
-- Reminder : A monoid is a semigroup with an element which acts as the left and right identity on `mul`.
structure Monoid (α : Type) extends Semigroup α where 
  e : α -- element 
  e_mul : mul e a = e -- left id in mul
  mul_e : mul a e = e -- right id in mul

-- Now try to instantiate the type `Nat'` as a monoid.
-- Leave out the three proofs (associativity, left and right inverse), we'll learn better ways to write such proofs next week.
def Nat'Monoid : Monoid Nat' := 
  {
    mul := mul,
    assoc := sorry,
    e := succ zero,
    e_mul := sorry,
    mul_e := sorry
  }
