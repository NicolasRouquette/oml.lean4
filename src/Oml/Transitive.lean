import Lean.Data.HashSet
import Lean.Data.PersistentHashMap

namespace Transitive

universe u v
variable {α : Type u} [BEq α] [Hashable α]

partial def trans1 (h: Lean.PersistentHashMap α α) (a: α): Lean.HashSet α :=
  trans1' h a Lean.HashSet.empty
where
  trans1' (h: Lean.PersistentHashMap α α) (a: α) (v: Lean.HashSet α): Lean.HashSet α :=
    match h.find? a with
      | none =>
        v
      | some a'=>
        let v' := (v.insert a).insert a'
        trans1' (h.erase a) a' v'

partial def transs (h: Lean.PersistentHashMap α (Lean.HashSet α)) (a: α): Lean.HashSet α :=
  let s : Lean.HashSet α := Lean.HashSet.empty.insert a
  transs' h s Lean.HashSet.empty
where
  transs' (h: Lean.PersistentHashMap α (Lean.HashSet α)) (s: Lean.HashSet α) (r: Lean.HashSet α): Lean.HashSet α :=
    let ((h': Lean.PersistentHashMap α (Lean.HashSet α)), (r': Lean.HashSet α)) := 
      s.fold 
        (fun ((hi: Lean.PersistentHashMap α (Lean.HashSet α)), (ri: Lean.HashSet α)) a => 
          match hi.find? a with
            | none =>
              (hi, ri)
            | some as =>
              let hj : Lean.PersistentHashMap α (Lean.HashSet α):= hi.erase a
              let rj : Lean.HashSet α := as.fold .insert ri
              (hj, rj)) 
        (h, Lean.HashSet.empty)
    if r'.isEmpty then
      r
    else
      transs' h' r' (r'.fold .insert r)

end Transitive
