/- TACTICS -/

-- example (n m k : Nat) : (n + m) * k = (m + n) * k := by 
--   have t := Nat.add_comm n -- Ao substituir n + m por m + n as equacoes ficam iguais
--   rw [t]

namespace TBA

-- definitions from last week
-- NOTE: We renamed it from `Nat'` for consistency. The new namespace makes sure we don't use the
-- standard library `Nat`.
inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

open Nat

def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

-- With this command we add a notation for `add`. From now on we will be able to write `m + n` for
-- `add m n`. The 65 denotes how strongly the operator should bind to what's adjacent to it.
-- The `priority` means that Lean will prefer it over the built-in `+`.
infix:65 (priority := high) " + " => add

def mul (m n : Nat) : Nat :=
  match n with
  | zero   => zero
  | succ n => (mul m n) + m

-- We also want a notation for `mul`, with a higher binding strength than addition so that
-- `a + b * c` means `a + (b * c`)`.
infix:70 (priority := high) " * " => mul

inductive LE : Nat → Nat → Prop where
  | refl (n : Nat) : LE n n
  | succ : LE m n → LE m (succ n)

-- lower binding strength than either addition or multiplication
infix:50 (priority := high) " ≤ " => LE

-- Let's start by reproving some theorems from last week, but this time with tactics!
-- useful tactics:
-- * `induction ... with ...`
-- * `rw [f]` to unfold applications of a function `f`
-- * `rw [h]` to rewrite every `a` to `b` if `h : a = b`
-- * `apply/exact`
-- * `simp/simp_all`... are powerful and basically always useful, though make sure that you could also
--   do the proof without them
theorem zero_add : zero + n = n := by
  induction n with
  | zero      => rfl
  | succ n ih => -- rw [add, ih]
    induction n 
    case succ.zero => 
      rfl 
    case succ.succ => 
      simp_all [add]

theorem add_zero : n + zero = n := by
  rfl

theorem le_add : m ≤ m + n := by 
  induction n  
  case zero => 
    exact LE.refl _ 
  case succ n h => 
    apply LE.succ 
    simp_all

-- Alright, let's start automating more!
attribute [simp] add mul
-- These definitions will now automatically be unfolded when you use `simp/simp_all`

theorem succ_add : (succ n) + m = succ (n + m) := by
  induction m 
  case zero => rfl
  case succ h => simp [h]

-- This one is a bit more tricky, you might need to prove a helper lemma!
theorem add_comm : n + m = m + n := by 
  induction n 
  case zero => 
    exact zero_add
  case succ n h => 
    simp [h, succ_add]

-- Associativity can be proven in a similar way.
theorem add_assoc : (m + n) + k = m + (n + k) := by 
  induction k 
  case zero => 
    rfl 
  case succ n h => 
    simp [h]

def one := succ zero

theorem mul_one : m * one = m := by 
  induction m <;> simp_all

theorem one_mul : one * m = m := by 
  induction m <;> simp_all

-- To prove associativity of multiplication, you might have to come up with
-- some more lemmas about multiplication first. Some are similar to the above laws of
-- addition, some use both addition and multiplication ("distributivity" is the keyword).

theorem mul_zero : n * zero = zero := by 
  induction n <;> simp

@[simp]theorem zero_mul : zero * n = zero := by 
  induction n <;> simp_all

theorem mul_distr : a * (b + c) = (a * b) + (a * c) := by 
  induction c
  case zero => simp
  case succ a h => 
    rw [add, mul, mul, h, add_assoc]
  -- simp [add_assoc, h] -- would be a loop if Lean was not smart enough

theorem mul_assoc : (m * n) * k = m * (n * k) := by 
  induction k 
  case zero => simp
  case succ n h => simp [mul_distr, h]

-- Remember the structures for semigroups and monoids which we defined last week?
structure Semigroup (α : Type) where
  mul   : α → α → α
  assoc : mul (mul a b) c = mul a (mul b c)

structure Monoid (α : Type) extends Semigroup α where
  e     : α
  e_mul : mul e a = a
  mul_e : mul a e = a

-- You should now be able to instantiate two of them, including proofs!
def Nat_add_Monoid : Monoid Nat := 
  {
    mul := add,
    assoc := add_assoc,
    e := zero,
    e_mul := zero_add,
    mul_e := add_zero
  }

def Nat_mul_Monoid : Monoid Nat := 
  {
    mul := mul,
    assoc := mul_assoc,
    e := succ zero,
    e_mul := one_mul,
    mul_e := mul_one
  }

end TBA
