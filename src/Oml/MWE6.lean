import Std.Data.AssocList

namespace MWE6

inductive Syntax where
  | leaf
  | withDeclaration (d: String) (s: Syntax) 
  | withSpecialization (sub: String) (sup: String) (s: Syntax)
  deriving Repr

def s1 := Syntax.leaf |>.withDeclaration "a" |>.withSpecialization "a" "b"
#eval s1

abbrev Strings := List String

abbrev Sups := Std.AssocList String Strings
instance : Repr Sups where reprPrec s n := s.toList.repr n

structure State where
  decls: Strings := .nil
  specializations: Sups := .nil
  deriving Repr

def State.wff(s: State) : Prop :=
  s.specializations.all 
    fun (sub sups) => 
      s.decls.contains sub &&
      sups.all (fun sup => s.decls.contains sup)

def State.empty: State := {}

theorem State.empty.wff : State.empty.wff := by rfl

def State.withDecl (s: State) (d: String) : State :=
  match s.decls.contains d with
  | true    => s
  | false   => { s with decls := d :: s.decls }


theorem State.withDecl.noChange (s: State) (d: String) (h: s.decls.contains d) : s = s.withDecl d := by {
  sorry
}

theorem State.withDecl.added (s: State) (d: String) (h: ! s.decls.contains d) : (s.withDecl d).decls.contains d := by {
  sorry
}

theorem State.withDecl.wff (s: State) (d: String) (h: s.wff) : s.withDecl d |>.wff := by {
  sorry
}

-- To ensure WFF, make sure sub and sup are declared.
def State.withSpecialization (s: State) (sub: String) (sup: String) : State :=
  let s' := s.withDecl sub |>.withDecl sup
  let sups : Strings := match s'.specializations.find? sub with 
    | none => [sup]
    | some xs => if xs.contains sup then xs else xs.cons sup
  match s'.specializations.contains sub with
  | false => { s' with specializations := s'.specializations.cons sub .nil }
  | true => { s' with specializations := s'.specializations.replace sub sups }

def Syntax.toState (s: Syntax): State :=
  match s with 
  | .leaf =>
    .empty
  | .withDeclaration d s =>
    s.toState.withDecl d
  | .withSpecialization sub sup s => 
    s.toState.withSpecialization sub sup

def st1 := s1.toState
#eval st1

end MWE6
