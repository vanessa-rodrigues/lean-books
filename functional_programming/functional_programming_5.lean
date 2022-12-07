-- Mapping on a Tree

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β) 
  | leaf => pure BinTree.leaf
  | branch l v r => f v >>= fun x => BinTree.mapM f l >>= fun y => BinTree.mapM f r >>= fun z => pure (BinTree.branch y x z)

def tree := BinTree.branch (BinTree.branch BinTree.leaf 4 BinTree.leaf) 5 (BinTree.branch BinTree.leaf 12 (BinTree.branch BinTree.leaf 50 BinTree.leaf)) 

-- def test : BinTree Nat -> Nat
--   | BinTree.leaf => 0 
--   | BinTree.branch l v r => 0 

#eval BinTree.mapM (m := Id) (fun x => x) tree

-- The Option Monad Contract

-- correct 
instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

-- wrong 
instance : Monad Option where
  pure x := some x
  bind opt next := none
--  bind (pure v) f should be the same as f v

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun ⟨⟩ => Many.none)


-- Checking Contracts
-- Check the monad contract for State σ and Except ε.




instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x

-- Except.bind (Except.pure v) f
-- Except.bind (Except.ok v) f
-- f v

-- Except.bind v Except.pure == v
-- attempt = v
-- next == pure 
-- if v == error => v 
-- if v == ok => pure ok => v

-- bind (bind v f) g == bind v (fun x => bind (f x) g)
-- Except.bind (Except.bind v f) g
-- 

def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

-- bind (pure v) f
-- bind (fun s => (s,v)) f 
-- first = (fun s => (s,v)), next = f 
-- fun y => s' = s and x = v
-- f x s' 

-- Readers with Failure

def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

def Reader.bind (result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env

def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderOption.pure (x : α) : ReaderOption ρ (Option α) := fun _ => some x

def ReaderOption.bind (result : ReaderOption ρ (Option α)) (next : α → ReaderOption ρ (Option β)) : ReaderOption ρ (Option β) :=
  fun env => sorry

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α

abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max), ("mod", (· % ·))]

#check ReaderOption.pure 6

-- 5.3
inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op


inductive Arith where
  | plus
  | minus
  | times
  | div

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

-- def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int): Expr (Prim special) → m Int
--   | Expr.const i => pure i
--   | Expr.prim p e1 e2 =>
--     evaluateM applySpecial e1 >>= fun v1 =>
--     evaluateM applySpecial e2 >>= fun v2 =>
--     applyPrim applySpecial p v1 v2

def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int): Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 => do 
    let v1 <- evaluateM applySpecial e1
    let v2 <- evaluateM applySpecial e2
    (applyPrim applySpecial p v1 v2)

def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op

open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))

----------------------------
instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x


-- def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
--   lookup xs 0 >>= fun first =>
--   lookup xs 2 >>= fun third =>
--   lookup xs 4 >>= fun fifth =>
--   lookup xs 6 >>= fun seventh =>
--   pure (first, third, fifth, seventh)

def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  let first <- lookup xs 0 
  let third <- lookup xs 2
  let fifth <- lookup xs 4
  let seventh <- lookup xs 6
  pure (first, third, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]

#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals

#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds

