
namespace MWE3

structure State where
  declarations: List String
  aspects: List String
  concepts: List String
deriving Repr

-- the set of declarations must equal to the disjoint union of aspects and concepts.
def State.wff: State → Prop :=
  fun s => ∀ a c, 
  (s.aspects.contains a → s.declarations.contains a && ! s.concepts.contains a) && 
  (s.concepts.contains c → s.declarations.contains c && ! s.aspects.contains c)

def State' := { s: State // s.wff }
#print State'
def s1 := State.mk ["a","b","c"] ["a"] ["b","c"] 
#eval s1
#check s1.wff
#print s1

def s1' : State' := ⟨ s1, s1.wff ⟩ 
#print s1'

def s2 := State.mk ["a","b","c"] ["a","b"] ["b","c"] 
#eval s2

example : s2.wff = True := by 
  sorry

end MWE3
