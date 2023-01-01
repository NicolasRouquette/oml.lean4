import Std.Data.AssocList

namespace MWE5

abbrev Sups := Std.AssocList String Unit

structure State where
  declarations: Std.AssocList String Sups

-- all declaration values must be declaration keys
def State.wff: State → Prop :=
  fun s => s.declarations.all 
    fun (_ sups) => sups.all 
      fun (sup _) => s.declarations.contains sup

def State.withDeclaration (s: State) (d: String) : State := 
  match s.declarations.contains d with
  | true => s
  | false => { s with declarations := s.declarations.replace d .nil }

def State.withSpecialization (s: State) (sub: String) (sup: String): State :=
  let s := s.withDeclaration sup
  let sups : Sups := match s.declarations.find? sub with 
  | none => .nil
  | some x => x.replace sup ()
  { s with declarations := s.declarations.replace sub sups }

theorem State.withDeclarationWff (s: State) (d: String) : s.wff → (s.withDeclaration d).wff := by
  intro h
  sorry

theorem State.withSpecializationWff (s: State) (sub: String) (sup: String): s.wff → (s.withSpecialization sub sup).wff := by
  intro h
  sorry

end MWE5
