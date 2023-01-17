-- WIP Trying to proove addBoth.sub, addBoth.sup 
import Std.Data.AssocList
import Std.Data.List.Lemmas

namespace MWE8

theorem cond_eq_ite (c : Bool) (a b : α) : cond c a b = if c then a else b := by cases c <;> rfl

abbrev Strings := List String

instance : Repr (Std.AssocList String Strings) where reprPrec s n := s.toList.repr n

def addDecl (s: Std.AssocList String Strings) (d: String) : Std.AssocList String Strings :=
match s.contains d with
| true => s
| false => .cons d [] s

theorem addDecl.added (s: Std.AssocList String Strings) (d: String): (addDecl s d).contains d
:= by
  simp [addDecl]
  split <;> simp
  next x heq => simp_all

theorem addDecl.cons (s: Std.AssocList String Strings) (d: String): (addDecl s d).isEmpty = false
:= by
  simp [addDecl]
  split <;> simp [List.isEmpty]
  . case h_1 x heq =>
    split <;> simp_all
    done

theorem addDecl.after (s: Std.AssocList String Strings) (x y: String): s.contains x → (addDecl s y).contains x
:= by
  intro h
  simp [Std.AssocList.contains, addDecl] at h ⊢
  apply Exists.elim h
  split <;> simp_all

def addSubSup: String → String → Std.AssocList String Strings → Std.AssocList String Strings
| sub, sup, .nil            => .cons sub [sup] .nil
| sub, sup, .cons a as tail => bif a = sub then .cons sub (as.insert sup) tail else .cons a as (addSubSup sub sup tail)
  
theorem addSubSup.sub (sub sup: String) (ss: Std.AssocList String Strings): (addSubSup sub sup ss).contains sub
:= by
  induction ss <;> simp_all
  . case cons key value tail tail_ih =>
    simp [addSubSup, cond_eq_ite]
    by_cases key = sub
    . case pos h =>
      simp [h]
    . case neg h =>
      simp [h, tail_ih]

def addBoth (sub sup: String) (ss: Std.AssocList String Strings) : Std.AssocList String Strings :=
  let ss' := addDecl ss sup
  addSubSup sub sup ss'

theorem addBoth.sub (sub sup: String) (ss: Std.AssocList String Strings) 
: (addBoth sub sup ss).contains sub
:= by
  induction ss <;> simp_all
  . case nil =>
    simp [addBoth, addDecl, addSubSup, cond_eq_ite]
    split <;> simp_all
    done
  . case cons key value tail tail_ih =>
    simp [addBoth, addDecl]
    by_cases key = sup
    . case pos h1 =>
      simp [h1]
      simp [h1, cond_eq_ite, addSubSup]
      by_cases sup = sub
      . case pos h2 =>
        simp [h2]
        done
      . case neg h2 =>
        simp [h2]
        sorry
    . case neg h1 =>
      simp [h1]



theorem addBoth.sup (sub sup: String) (ss: Std.AssocList String Strings) 
: (addBoth sub sup ss).contains sup
:= by
  simp [addBoth]
  simp [addDecl]
  induction ss <;> simp_all
  . case nil =>
    by_cases sub = sup
    . case pos h =>
      simp [h]
      sorry
    . case neg h =>
      simp [h]
      sorry
  . case cons key value tail tail_ih =>
    simp [addDecl, cond_eq_ite]
    by_cases sup = key
    . case pos h =>
      simp [h]
      simp [addBoth] at tail_ih
      sorry
    . case neg h =>
      simp_all 
      . case inl =>
        contradiction
      . case inr h' =>
        simp_all
        sorry

end MWE8