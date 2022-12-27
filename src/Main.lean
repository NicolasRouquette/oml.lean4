import Oml.O1

def usage : String := "
  Usage...
"

def main (args : List String): IO Unit :=
  match args with
  | [] => IO.println usage
  | ["1"] => O1.main
  | x =>
    IO.println s!"Unknown: {x}"
