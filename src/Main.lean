import Oml.O1
import Oml.O4

def usage : String := "
  Usage...
"

def main (args : List String): IO Unit :=
  match args with
  | [] => IO.println usage
  | ["1"] => O1.main
  | ["4"] => O4.main
  | x =>
    IO.println s!"Unknown: {x}"
