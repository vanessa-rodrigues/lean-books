-- def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- def woodlandCritters : List String :=
--   ["hedgehog", "deer", "snail"]

-- #eval third woodlandCritters (by simp)

-- 1

def twoPlusThreeIsFiveRfl : 2 + 3 = 5 := rfl

def fifteenMinusEightIsSevenRfl : 15 - 8 = 7 := rfl

def helloWorldRfl : "Hello, ".append "world" = "Hello, world" := rfl

def fiveIsLessThanEighteenRfl : (5 < 18) = (18 > 5) := rfl  

-- 2

def twoPlusThreeIsFive : 2 + 3 = 5 := by simp

def fifteenMinusEightIsSeven : 15 - 8 = 7 := by simp

def helloWorld : "Hello, ".append "world" = "Hello, world" := by simp

def fiveIsLessThanEighteen : 5 < 18 := by simp  

-- 3 

def fifth (xs : List α) (ok : xs.length > 4) : α := xs[4]

def harryPotterCharacters : List String := ["harry", "ron", "hermione", "neville", "luna", "sirius"]

#eval fifth harryPotterCharacters (by simp)
