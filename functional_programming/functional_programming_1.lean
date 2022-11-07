#check 42 + 19

#check String.append "A" (String.append "B" "C")

#check String.append (String.append "A" "B") "C"

#check -6

#check if 3 == 3 then 5 else 7

#check if 3 == 4 then "equal" else "not equal"

def joinStringsWith (s1: String) (s2: String) (s3: String) : String :=
  String.append s2 (String.append s1 s3)

#eval joinStringsWith ", " "one" "and another"

#check joinStringsWith

def volume (height: Nat) (width: Nat) (depth: Nat) : Nat :=
  height * width * depth

#eval volume 3 3 3

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr

-- same name with different types. Is it not allowed?
def volume_prism (prism : RectangularPrism) : Float :=
  prism.height * prism.width * prism.depth

#eval volume_prism (RectangularPrism.mk 3 3 3)

structure Point where
  x : Float
  y : Float
deriving Repr

structure Segment where
  p1 : Point
  p2 : Point
deriving Repr

def seg_length (seg: Segment) : Float := 
  let cateto_1 := Float.abs (seg.p1.x - seg.p2.x)
  let cateto_2 := Float.abs (seg.p1.y - seg.p2.y)
  Float.sqrt ((Float.pow cateto_1 2) + (Float.pow cateto_2 2))

#eval seg_length (Segment.mk (Point.mk 0 1) (Point.mk 1 1))

structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float


def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)

#eval (length Nat [1,2,3])

def length_2 {α : Type} (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)

#eval (length_2 [1,2,3,4])

def fives : String × Int := ("five", 5) -- Prod

#eval [].head? (α := Int)

-- Sum (Or operator)
-- def PetName : Type := String ⊕ String

-- def animals : List PetName :=
--   [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

-- #eval animals

-- 1.6

def last_entry? {α : Type} (xs : List α) : Option α := 
  match xs with 
  | [] => none
  | x :: [] => some x
  | _ :: ys => last_entry? ys

#eval last_entry? [1]
#eval last_entry? [1,3,4,5]
#eval last_entry? ([] : List Nat)
#eval last_entry? ["harry", "ron", "hermione"]

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := 
  match xs with 
  | [] => none
  | y :: ys => if predicate y then some y else findFirst? ys predicate

#eval [5,3,7,8].findFirst? (fun y => y < 5)
#eval [].findFirst? (fun y => y < 5)

def Prod.swap {α β : Type} (pair : α × β) : β × α := (pair.2, pair.1)

#eval fives.swap 

inductive PetName (α : Type) : Type where
  | cat : α -> PetName α 
  | dog : α -> PetName α  

def animals : List (PetName String) :=
  [PetName.dog "Spot", PetName.cat "Tiger", PetName.dog "Fifi", PetName.dog "Rex", PetName.cat "Floof"]

-- #eval animals


def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := 
  match xs, ys with 
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => List.cons (x,y) (zip xs ys)


#eval zip [1,2,3] ["harry", "ron", "hermione", "hagrid"]


def take_internal {α : Type} (n : Nat) (xs : List α) (ys : List α) : List α :=
  match n, xs with
  | 0, _ => ys
  | _, [] => ys
  | n, x :: xs => take_internal (n-1) xs (List.cons x ys)

def take {α : Type} (n : Nat) (xs : List α) : List α := 
  take_internal n xs []

#eval take 3 ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"]


def pet : PetName String := PetName.cat "Voldemort"

def sevens : String × Int := ("seven", 7)

-- def mul_to_sum {α : Type} (h : Bool × α) : α ⊕ α := sorry