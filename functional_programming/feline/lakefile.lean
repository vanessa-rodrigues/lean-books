import Lake
open Lake DSL

package feline {
  -- add package configuration options here
}

@[defaultTarget]
lean_exe feline {
  root := `Main
}
