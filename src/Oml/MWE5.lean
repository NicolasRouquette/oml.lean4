import Std.Data.AssocList
import Std.Data.List.Lemmas

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

theorem State.withDeclaration.added3 (s: State) (d: String)
: (s.withDeclaration d).declarations.contains d
:= by
  simp [State.withDeclaration]
  split <;> simp
  next x heq => simp_all

theorem State.withDeclaration.wff (s: State) (d: String) (h: s.wff)
: (s.withDeclaration d).wff 
:= by 
  simp [State.wff, State.withDeclaration] at h ⊢
  intro (s1, ss) 
  split <;> simp
  . apply h
  · rintro (⟨rfl, rfl⟩ | h' )
    . intro.
    . exact fun x hs => .inr (h _ h' x hs)

def addBoth : (Std.AssocList String Strings) → String → String → (Std.AssocList String Strings)
| .nil, sub, sup            => .cons sup [] (.cons sub [sup] .nil)
| .cons a as tail, sub, sup => bif a == sub then .cons sub (as.insert sup) tail else .cons a as (addBoth tail sub sup)

theorem addBoth.nil (sub: String) (sup: String)
: (addBoth .nil sub sup).contains sub && (addBoth .nil sub sup).contains sup
:= by simp [addBoth]

--set_option pp.explicit true 
theorem addBoth.added (ss: Std.AssocList String Strings) (sub: String) (sup: String)
: (addBoth ss sub sup).contains sub && (addBoth ss sub sup).contains sup
:= by {
  induction ss
  case nil => {
    simp [addBoth]
  }
  case cons key value tail tail_ih => {
    simp [Std.AssocList.contains] at *
    induction tail 
    case nil =>
      simp [addBoth]
      apply And.intro <;>simp_all
    case cons =>
      apply And.intro
      case left => {
        simp [addBoth]
        simp_all
        simp [*]
        
      }
      case right => {
        induction tail <;> simp [addBoth]
        
      }
  }
  done
}


theorem addBoth.sub.more (ss: Std.AssocList String Strings) (sub: String) (sup: String) (key: String) (value: Strings)
: (addBoth ss sub sup).contains sub → (addBoth (ss.cons key value) sub sup).contains sub
:= by {
  simp [Std.AssocList.contains, addBoth]
  intro x h fst
  apply Exists.elim
  --induction ss 
  
}

theorem addBoth.sub (ss: Std.AssocList String Strings) (sub: String) (sup: String)
: (addBoth ss sub sup).contains sub
:= by {
  simp [Std.AssocList.contains]
  induction ss 
  case nil =>
    simp [addBoth]
  case cons key value tail tail_ih =>
    simp [addBoth] 
     
    

    
}

def State.withSpecialization (s: State) (sub: String) (sup: String): State :=
  { declarations := addBoth s.declarations sub sup }

--set_option pp.explicit true 

theorem State.withSpecialization.added1 (s: State) (sub: String) (sup: String)
: (s.withSpecialization sub sup).declarations.contains sub && (s.withSpecialization sub sup).declarations.contains sup
:= by {
  have h := s.withSpecialization sub sup
  simp [State.withSpecialization]
  apply And.intro
  case left => {

  }
  case right => {

  }
}

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

theorem State.withSpecialization.added2 (s: State) (sub: String) (sup: String)
(h1: !s.declarations.contains sub) 
(h2: !s.declarations.contains sup) 
: (s.withSpecialization sub sup).declarations.contains sub && 
  (s.withSpecialization sub sup).declarations.contains sup
:= by
  simp [State.withSpecialization, State.withDeclaration] at *
  apply And.intro
  . 
   
  simp [Std.AssocList.contains, List.any, List.replaceF] at *
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
