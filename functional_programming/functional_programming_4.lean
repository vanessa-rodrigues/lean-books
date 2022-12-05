-- 4.1

-- Another Representation
structure Pos where
  succ :: -- constructor
  pred : Nat
deriving Repr

#eval Pos.succ 4

def Pos.add : Pos -> Pos -> Pos
  | succ n1, succ n2 => Pos.succ (n1 + n2 + 1)

instance : Add Pos where 
  add := Pos.add

#eval (Pos.succ 4) + (Pos.succ 0)

def Pos.mul : Pos -> Pos -> Pos
  | succ n1, succ n2 => Pos.succ ((n1 + 1) * (n2 + 1) - 1)

instance : Mul Pos where 
  mul := Pos.mul

#eval (Pos.succ 4) * (Pos.succ 1)

def Pos.ToString (p : Pos) : String := toString (p.pred + 1)

instance : ToString Pos where 
  toString x := Pos.ToString x

#eval toString (Pos.succ 4)

instance : OfNat Pos n where 
  ofNat := Pos.succ n

def pos : Pos := 2

#eval pos

-- Even Numbers
-- inductive Even : Type where
--   | zero : Even 
--   | succ : Even -> Even

inductive Even : Nat → Type where
  | zero : Even 0 
  | succ : ∀ (_ : Even n), Even (Nat.succ (Nat.succ n))

def ev := Even.succ (Even.succ Even.zero)

#check ev

def evenZeroAux (ev : Even m) : m = n + 2 → Even n := 
  Even.casesOn (motive := fun x _ => x = n + 2 → Even n) ev 
  (fun h : 0 = n + 2 => Nat.noConfusion h)
  (fun h h1 => Nat.noConfusion h1 
    (fun h2 => Nat.noConfusion h2 (fun h3 => by 
      rw [h3, Nat.add] at h
      exact h)))


def Even.add {α : Nat} [Add Nat] : Even α -> Even α -> Even α 
  | zero, k => k
  | Even.succ n1, k => succ (n1.add (evenZeroAux k rfl)) 

instance {α : Nat} [Add Nat] : Add (Even α) where 
  add x := Even.add x

-- #eval ev + Even.zero


def Even.mul [Mul Nat] : Even n -> Even n -> Even n 
  | Even.zero, _ => Even.zero
  | Even.succ n1, Even.succ n2 => Even.succ (Even.mul n1 n2) 

-- def Even.mul : Even α -> Even α -> Even α
--   | Even.zero, _ => Even.zero
--   | Even.succ n, k => Even.succ n 

-- -- instance : Mul Even where 
-- --   mul := Even.mul 

-- -- def Even.toString (atTop : Bool) (ev : Even) : String :=
-- --   let paren s := if atTop then s else "(" ++ s ++ ")"
-- --     match ev with
-- --     | Even.zero => "Even.zero"
-- --     | Even.succ n => paren s!"Even.succ {Even.toString false n}"

-- -- instance : ToString Even where 
-- --   toString := Even.toString true

-- -- #eval Even.succ (Even.succ Even.zero)

-- -- def isEven (n : Nat) := Nat.mod n 2 == 0

-- -- I don't know what to do with an odd number. I know how to transform it in a even number but I don't know how to raise an error 
-- -- instance [OfNat α 0] : OfNat (Even) n where
-- --   ofNat :=
-- --     let rec natPlusOne : Nat → Even
-- --       | 0 => Even.zero
-- --       | k + 1 => Pos.succ (natPlusOne k)
-- --     natPlusOne n
-- -- def even : Even := 2

-- -- #eval even

-- HTTP Requests

inductive HttpRequest : Float -> String -> Option String -> Type where 
  | GET : (version : Float) -> (uri : String) -> _ -> HttpRequest version uri none
  | POST : (version : Float) -> (uri : String) -> (body : String) -> HttpRequest version uri (some body) 
  | DELETE : (version : Float) -> (uri : String) -> _ -> HttpRequest version uri none

structure HttpResponse where
  code : Nat 
  codeMsg : String 
  txt : Option String 
deriving Repr

#eval HttpResponse.mk 345 "Test" none

-- 4.3 
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def PointMul [Mul α] (p1: PPoint α) (p2: PPoint α) : (PPoint α) := 
  PPoint.mk (p1.x * p2.x) (p1.y * p2.y)

instance [Mul α] : Mul (PPoint α) where 
  mul := PointMul

def HPointMul [Mul α] (p: PPoint α) (h: α) : (PPoint α) := 
    PPoint.mk (p.x * h) (p.y * h)

instance [Mul α] : HMul (PPoint α) α (PPoint α) where 
  hMul := HPointMul

#eval {x := 2.5, y := 3.7 : PPoint Float} * (2.0 : Float)

-- 4.5 
--1
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }

def LocalAppend (xs: List α) (ys: NonEmptyList α) : (NonEmptyList α) := 
  match xs with
  | [] => ys
  | x :: xss => { head := x, tail := xss ++ (List.cons ys.head ys.tail) }

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where 
  hAppend := LocalAppend

#eval [1,2,3] ++ ({ head := 4, tail := [6,7,8] } : NonEmptyList Nat)

#eval [1,2,3] ++ ({ head := 4, tail := [] } : NonEmptyList Nat)

#eval ([] : List Nat) ++ ({ head := 4, tail := [6,7,8] } : NonEmptyList Nat)

--2
inductive BinTree (α : Type) where
  | leaf (val : α) : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf _, BinTree.leaf _ =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf _ =>
    0
  | BinTree.branch left x right =>
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

def mapBinTree (f : α -> β) (tree: BinTree α) : BinTree β := 
  match tree with
  | BinTree.leaf x => BinTree.leaf (f x)
  | BinTree.branch l x r => BinTree.branch (mapBinTree f l) (f x) (mapBinTree f r)

instance : Functor BinTree where 
  map f tree := mapBinTree f tree 

#eval mapBinTree (fun x => x * 2) (BinTree.branch (BinTree.leaf 4) 5 (BinTree.leaf 8))
