import Lean.Data.HashMap
import Lean.Data.HashSet
namespace MWE4

structure State where
  declarations: Lean.HashMap String (Lean.HashSet String)

-- all declaration values must be declaration keys
def State.wff: State → Bool := fun s => s.declarations.toList.all fun (_, xs) => xs.toList.all s.declarations.contains

def State.withDeclaration (s: State) (d: String) : State := 
  match s.declarations.contains d with
  | true => s
  | false => { s with declarations := s.declarations.insert d .empty }

def State.withSpecialization (s: State) (sub: String) (sup: String): State :=
  let s := s.withDeclaration sup
  { s with declarations := s.declarations.insert sub ((s.declarations.findD sub .empty).insert sup) }

theorem State.withDeclarationWff (s: State) (d: String) : s.wff → (s.withDeclaration d).wff := sorry

theorem State.withSpecializationWff (s: State) (sub: String) (sup: String): s.wff → (s.withSpecialization sub sup).wff := sorry

end MWE4
