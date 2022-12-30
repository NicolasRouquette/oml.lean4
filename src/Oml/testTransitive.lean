import Oml.Transitive
import Oml.Instances

namespace testTransitive

def h1 : Lean.PersistentHashMap String String := 
  ((Lean.PersistentHashMap.empty.insert "a" "b").insert "b" "c").insert "d" "c"

#eval Transitive.trans1 h1 "a"

def h2 : Lean.PersistentHashMap String (Lean.HashSet String) := 
  (((Lean.PersistentHashMap.empty.insert "a" ((Lean.HashSet.empty.insert "b").insert "e")
  ).insert "b" ((Lean.HashSet.empty.insert "a").insert "d")
  ).insert "c" ((Lean.HashSet.empty.insert "d").insert "h")
  ).insert "e" ((Lean.HashSet.empty.insert "f").insert "g")

#eval Transitive.transs h2 "a"

end testTransitive