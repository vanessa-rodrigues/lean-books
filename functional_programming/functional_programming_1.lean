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
