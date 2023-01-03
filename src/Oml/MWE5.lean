import Std.Data.AssocList

namespace MWE5

abbrev Strings := List String
abbrev Sups := Std.AssocList String Strings
instance : Repr Sups where reprPrec s n := s.toList.repr n

structure State where
  declarations: Std.AssocList String Strings := .nil
  deriving Repr

def State.empty: State := {}

-- all declaration values must be declaration keys
def State.wff: State → Bool :=
  fun s => s.declarations.all 
    fun (_ sups) => sups.all 
      fun sup => s.declarations.contains sup

def State.withDeclaration (s: State) (d: String) : State := 
  match s.declarations.contains d with
  | true => s
  | false => { s with declarations := s.declarations.cons d .nil }

def State.withSpecialization (s: State) (sub: String) (sup: String): State :=
  let s := s.withDeclaration sub |>.withDeclaration sup
  let sups : Strings := match s.declarations.find? sub with 
  | none => 
    -- this case can never happen since sub has been declared.
    [sup]
  | some xs => 
    if xs.contains sup then xs else xs.cons sup
  { s with declarations := s.declarations.replace sub sups }

theorem State.withDeclaration.noChange (s: State) (d: String) (h: s.declarations.contains d) 
: s = s.withDeclaration d 
:= by rw [State.withDeclaration, h]

theorem State.withDeclaration.added1 (s: State) (d: String) (h: !s.declarations.contains d) 
: (s.withDeclaration d).declarations.contains d
:= by 
  rw [State.withDeclaration] at *
  simp_all

theorem State.withDeclaration.added2 (s: State) (d: String) (h: !s.declarations.contains d) 
: (s.withDeclaration d).declarations.find? d = some []
:= by 
  rw [State.withDeclaration] at *
  simp_all

theorem State.withDeclaration.wff (s: State) (d: String) 
: s.wff → (s.withDeclaration d).wff 
:= by 
  simp_all [State.wff, State.withDeclaration]
  intro h
  split
  . apply h
  . simp_all
    
    sorry
    
    
theorem State.withSpecialization.noChange (s: State) (sub: String) (sup: String)
(h1: s.declarations.contains sub) 
(h2: s.declarations.contains sup) 
(h3: (s.declarations.find? sub).all (fun sups => sups.contains sup))
: s = s.withSpecialization sub sup
:= by
  --unfold State.withSpecialization State.withDeclaration at *
  simp [State.withSpecialization, State.withDeclaration] at *
  simp_all
  apply h3
  sorry

theorem State.withSpecialization.added (s: State) (sub: String) (sup: String)
(h1: !s.declarations.contains sub) 
(h2: !s.declarations.contains sup) 
: (s.withSpecialization sub sup).declarations.contains sub && 
  (s.withSpecialization sub sup).declarations.contains sup
:= by
  rw [State.withSpecialization] at *
  simp [State.withDeclaration, Std.AssocList.contains, List.any, List.replaceF] at *
  simp_all
  apply And.intro
  sorry

theorem State.withSpecialization.wff (s: State) (sub: String) (sup: String)
: s.wff → (s.withSpecialization sub sup).wff 
:= by
  simp [State.wff, State.withSpecialization, State.withDeclaration] at *
  intro h
  simp [*] at *
  sorry

def s0 : State := State.empty |>.withSpecialization "a" "b"
#eval s0

end MWE5
