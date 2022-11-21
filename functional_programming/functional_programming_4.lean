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

--Even Numbers
-- inductive Even : Type where
--   | zero : Even 
--   | succ : Even -> Even

inductive Even : Nat -> Type where
  | zero : Even Nat.zero 
  | succ : (Even n) -> Even (Nat.succ (Nat.succ n))
deriving Repr

#eval (Even.succ Even.zero)

def Even.toNat {α : Nat} : Even α → Nat
  | Even.zero => 0
  | Even.succ n => n.toNat + 2

#eval Even.toNat (Even.succ (Even.succ Even.zero))

def Even.add (n1 : Even α) (n2 : Even α) : Even α := 
  match n1, n2 with
  | Even.zero, k => k 
  | Even.succ k1, Even.succ k2 => Even.succ (k1.add k2)

instance {α : Nat} [Add Nat] : Add (Even α) where 
  add := Even.add 

-- #eval ((Even.succ Even.zero) + (Even.succ (Even.succ Even.zero)))


-- -- def Even.mul : Even -> Even -> Even
-- --   | Even.zero, _ => Even.zero
-- --   | Even.succ n, k => (Even.mul n k) + k

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

