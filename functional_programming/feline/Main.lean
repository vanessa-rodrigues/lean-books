def bufsize : USize := 20 * 1024

partial def dump (stream : IO.FS.Stream) : IO Unit := do 
  let buf <- stream.read bufsize 
  if buf.isEmpty then
    pure () 
  else 
    let stdout <- IO.getStdout
    stdout.write buf 
    dump stream

def dump_String (stream : String) : IO Unit := do 
  let stdout <- IO.getStdout
  stdout.putStrLn stream 
  pure ()

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists <- filename.pathExists 
  --   if not (← filename.pathExists) then
  if not fileExists then
    let stderr <- IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else 
    let handle <- IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with 
  | [] => pure exitCode 
  | "--help" :: args => 
    dump_String "Help message!"
    process exitCode args  
  | "-" :: args => 
    let stdin <- IO.getStdin
    dump stdin 
    process exitCode args 
  | filename :: args =>
    let stream <- fileStream ⟨filename⟩ 
    match stream with 
    | none => 
      process 1 args 
    | some stream => 
      dump stream 
      process exitCode args

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
