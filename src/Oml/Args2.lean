-- See Lean doc/monads/transformers.lean
namespace Args2

abbrev Arguments := List String

def indexOf? [BEq α] (xs : List α) (s : α) (start := 0): Option Nat :=
  match xs with
  | [] => none
  | a :: tail => if a == s then some start else indexOf? tail s (start+1)

def requiredArgument (name : String) : ExceptT String (ReaderM Arguments) String := do
  let args ← read
  let value := match indexOf? args name with
    | some i => if i + 1 < args.length then args[i+1]! else ""
    | none => ""
  if value == "" then throw s!"Command line argument {name} missing"
  return value

def optionalSwitch (name : String) : ExceptT String (ReaderM Arguments) Bool := do
  let args ← read
  return match (indexOf? args name) with
  | some _ => true
  | none => false

#eval requiredArgument "--input" |>.run ["--input", "foo"]
-- Except.ok "foo"

#eval requiredArgument "--input" |>.run ["foo", "bar"]
-- Except.error "Command line argument --input missing"

#eval optionalSwitch "--help" |>.run ["--help"]
-- Except.ok true

#eval optionalSwitch "--help" |>.run []


structure Config where
  help : Bool := false
  verbose : Bool := false
  input : String := ""
  deriving Repr

abbrev CliConfigM := StateT Config (ExceptT String (ReaderM Arguments))

def parseArguments : CliConfigM Bool := do
  let mut config ← get
  if (← optionalSwitch "--help") then
    throw "Usage: example [--help] [--verbose] [--input <input file>]"
  config := { config with
    verbose := (← optionalSwitch "--verbose"),
    input := (← requiredArgument "--input") }
  set config
  return true

def main (args : List String) : IO Unit := do
  let config : Config := { input := "default"}
  match parseArguments |>.run config |>.run args with
  | Except.ok (_, c) => do
    IO.println s!"Processing input '{c.input}' with verbose={c.verbose}"
  | Except.error s => IO.println s


#eval main ["--help"]
-- Usage: example [--help] [--verbose] [--input <input file>]

#eval main ["--input", "foo"]
-- Processing input file 'foo' with verbose=false

#eval main ["--verbose", "--input", "bar"]
-- Processing input 'bar' with verbose=true

end Args2