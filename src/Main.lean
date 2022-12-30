import Oml.O1
import Oml.Instances
import Oml.Syntax
import Oml.Resolver
import Oml.testSyntax
import Oml.testResolver

def usage : String := "
  Usage...
"

def main (args : List String): IO Unit :=
  match args with
  | [] => IO.println usage
  | ["1"] => O1.main
  | x =>
    IO.println s!"Unknown: {x}"
