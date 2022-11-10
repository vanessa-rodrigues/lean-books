-- def main : IO Unit := IO.println "Hello, world!"

-- def main : IO Unit := do
--   let stdin ← IO.getStdin
--   let stdout ← IO.getStdout

--   stdout.putStrLn "How would you like to be addressed?"
--   let input ← stdin.getLine
--   let name := input.dropRightWhile Char.isWhitespace

--   stdout.putStrLn s!"Hello, {name}!"

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 : List (IO Unit) := countdown 5

-- #eval from5.length

def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

-- def main : IO Unit := runActions from5

def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
