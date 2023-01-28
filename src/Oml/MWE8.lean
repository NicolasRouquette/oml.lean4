-- WIP Trying to proove addBoth.sub, addBoth.sup 
-- Why is there a significant difference in the proofs involving Eq vs. BEq?
import Std.Data.AssocList
import Std.Data.List.Lemmas
import Std.Classes.BEq

namespace MWE8

theorem cond_eq_ite (c : Bool) (a b : α) : cond c a b = if c then a else b := by cases c <;> rfl

theorem cond_decide {α} (p : Prop) [Decidable p] (t e : α) : cond (decide p) t e = if p then t else e := by
  by_cases p <;> simp [*]

@[simp] theorem beq_eq_eq [DecidableEq α] (x y : α) :
  (x == y) = decide (x = y) := rfl

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

theorem addDecl.after (s: Std.AssocList String Strings) (x y: String): s.contains x → (addDecl s y).contains x
:= by
  intro h
  simp [Std.AssocList.contains, addDecl] at h ⊢
  apply Exists.elim h
  split <;> simp_all
  done

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
      simp [h]
      apply tail_ih

def addBoth (sub sup: String) (ss: Std.AssocList String Strings) : Std.AssocList String Strings :=
  let ss' := addDecl ss sup
  addSubSup sub sup ss'

theorem addBoth.sub_eq (sub sup: String) (ss: Std.AssocList String Strings) 
: (addBoth sub sup ss).contains sub
:= by
  induction ss <;> simp_all
  . case nil =>
    simp [addBoth, addDecl, addSubSup, cond_eq_ite]
    split <;> simp_all
  . case cons key value tail tail_ih =>
    simp [addBoth, addDecl]
    by_cases key = sup <;> simp [*]
    . case pos =>
      simp [addSubSup, cond_eq_ite]
      by_cases sup = sub <;> simp [*]
      . case neg h =>
        simp [addBoth, addDecl] at tail_ih
        split at tail_ih 
        . case h_1 =>
          by_cases key = sub <;> simp [*]
        . case h_2 x heq =>
          by_cases key = sub <;> simp_all
          simp [addSubSup, cond_eq_ite, h] at tail_ih
          apply tail_ih
    . case neg h =>
      split <;> simp_all
      . case h_1 x heq =>
        done
      . case h_2 x heq =>
        done

theorem addBoth.sub_beq (sub sup: String) (ss: Std.AssocList String Strings) 
: (addBoth sub sup ss).contains sub
:= by
  induction ss <;> simp_all
  . case nil =>
    simp [addBoth, addDecl, addSubSup, cond_eq_ite]
    split <;> simp_all
  . case cons key value tail tail_ih =>
    simp [addBoth, addDecl]
    by_cases key == sup <;> simp_all
    . case pos =>
      simp [addSubSup, cond_eq_ite]
      by_cases sup == sub <;> simp [*]
      . case pos =>
        simp_all
      . case neg h =>
        simp [addBoth, addDecl] at tail_ih
        split at tail_ih 
        . case h_1 =>
          by_cases key == sub <;> simp_all
        . case h_2 x heq =>
          by_cases key == sub <;> simp_all
          simp [addSubSup, cond_eq_ite, h] at tail_ih
          apply tail_ih
    . case neg h =>
      split <;> simp_all
      . case h_1 x heq =>
        done
      . case h_2 x heq =>
        done

theorem addBoth.sup_eq (sub sup: String) (ss: Std.AssocList String Strings) 
: (addBoth sub sup ss).contains sup
:= by
  simp [addBoth]
  simp [addDecl]
  induction ss <;> simp [*]
  . case nil =>
    simp [addSubSup, cond_eq_ite]
    by_cases sup = sub <;> simp [*]
  . case cons key value tail tail_ih =>
    simp [addDecl, cond_eq_ite]
    by_cases key = sup <;> simp [*]
    . case pos h1 =>
      simp [addSubSup, cond_eq_ite] at tail_ih ⊢ 
      by_cases sup = sub <;> simp [*]
    . case neg h1 =>
      let ⟨ x, hx, he ⟩ := tail_ih
      split <;> simp_all
      . case h_1 y heq =>
        done
      . case h_2 y heq =>
        simp [h1, cond_eq_ite, beq_eq_false_iff_ne, h1] at heq
        done

theorem addBoth.sup_beq (sub sup: String) (ss: Std.AssocList String Strings) 
: (addBoth sub sup ss).contains sup
:= by
  simp [addBoth]
  simp [addDecl]
  induction ss <;> simp_all
  . case nil =>
    simp [addSubSup, cond_eq_ite]
    by_cases sup == sub <;> simp_all
  . case cons key value tail tail_ih =>
    simp [addDecl, cond_eq_ite]
    by_cases key == sup <;> simp_all
    . case pos h1 =>
      simp [addSubSup, cond_eq_ite]
      by_cases sup == sub <;> simp_all
    . case neg h1 => 
      split <;> simp_all
      . case h_1 x heq =>
        done
      . case h_2 x heq =>
        done

end MWE8