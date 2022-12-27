-- See Lean doc/monads/transformers.lean
namespace Args1

abbrev Arguments := List String

def indexOf? [BEq α] (xs : List α) (s : α) (start := 0): Option Nat :=
  match xs with
  | [] => none
  | a :: tail => if a == s then some start else indexOf? tail s (start+1)

def requiredArgument (name : String) : ReaderT Arguments (Except String) String := do
  let args ← read
  match indexOf? args name with
    | some i => 
      if h : i + 1 < args.length then 
        return args[i+1]'h 
      else
        throw s!"Value required for command line argument {name}"
    | none => 
      throw s!"Command line argument {name} missing"

def optionalSwitch (name : String) : ReaderT Arguments (Except String) Bool := do
  let args ← read
  return match (indexOf? args name) with
  | some _ => true
  | none => false

#eval requiredArgument "--input" |>.run ["--input", "foo"]
-- Except.ok "foo"

#eval requiredArgument "--input" |>.run ["--input"]
-- Except.error "Value required for command line argument --input"

#eval requiredArgument "--input" |>.run ["foo", "bar"]
-- Except.error "Command line argument --input missing"

#eval optionalSwitch "--help" |>.run ["--help"]
-- Except.ok true

#eval optionalSwitch "--help" |>.run []


structure Config where
  help : Bool := false
  verbose : Bool := false
  input : List String := []
  deriving Repr

abbrev CliConfigM := StateT Config (ReaderT Arguments (Except String))

def parseArguments : CliConfigM Bool := do
  let mut config ← get
  if (← optionalSwitch "--help") then
    throw "Usage: example [--help] [--verbose] [--input <input file>]"
  dbg_trace "config: "
  config := { config with
    verbose := (← optionalSwitch "--verbose"),
    input := config.input.concat (← requiredArgument "--input") }
  set config
  return true

def main (args : List String) : IO Unit := do
  let config : Config := {}
  match parseArguments |>.run config |>.run args with
  | Except.ok (_, c) => do
    IO.println s!"Processing input '{c.input}' with verbose={c.verbose}"
  | Except.error s => IO.println s

  
set_option trace.Meta.Match.debug true
set_option trace.Meta.synthInstance true
set_option trace.Elab.definition true
set_option pp.all true

#eval main ["--help"]
-- Usage: example [--help] [--verbose] [--input <input file>]

#eval main ["--input", "foo"]
-- Processing input file 'foo' with verbose=false

#eval main ["--verbose", "--input", "bar", "--input", "foo"]
-- Processing input 'bar' with verbose=true

end Args1