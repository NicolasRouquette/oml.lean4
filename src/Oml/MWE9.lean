-- WIP: only 3 lemmas to prove: addBoth2SubSup1, addSubSup.more.sub, addSubSup.more.sup

-- Tested with: 
-- leanprover/lean4:nightly unchanged - Lean (version 4.0.0-nightly-2023-01-28, commit e37f209c1a2a, Release)

import Std.Data.AssocList
import Std.Data.List.Lemmas
import Std.Classes.BEq

namespace MWE9

theorem cond_eq_ite (c : Bool) (a b : α) : cond c a b = if c then a else b := by cases c <;> rfl

theorem cond_decide {α} (p : Prop) [Decidable p] (t e : α) : cond (decide p) t e = if p then t else e := by
  by_cases p <;> simp [*]

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Problems.20simplifying.20.20conditions.20with.20hypotheses/near/324212540
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

@[simp] theorem addBoth2SubSup1
  (sub sup: String) 
  (tail: Std.AssocList String Strings)
  (h: ∃ x, x ∈ Std.AssocList.toList (addBoth sub sup tail) ∧ x.fst = sub)
: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup tail) ∧ x.fst = sub
:= by
  sorry

@[simp] theorem addSubSup.more.sub
  (sub sup: String) 
  (tail: Std.AssocList String Strings)
  (h: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup tail) ∧ x.fst = sub)
  (other: Std.AssocList String Strings)
: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup other) ∧ x.fst = sub
:= by
 sorry

@[simp] theorem addSubSup.more.sup
  (sub sup: String) 
  (tail: Std.AssocList String Strings)
  (h: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup tail) ∧ x.fst = sup)
  (other: Std.AssocList String Strings)
: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup other) ∧ x.fst = sup
:= by
 sorry

@[simp] theorem addBoth2SubSup2 
  (sub sup: String) 
  (tail: Std.AssocList String Strings)
  (h: ∃ x, x ∈ Std.AssocList.toList (addBoth sub sup tail) ∧ x.fst = sub)
  (other: Std.AssocList String Strings)
: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup other) ∧ x.fst = sub
:= by
  have ht := addBoth2SubSup1 sub sup tail h
  exact addSubSup.more.sub sub sup tail ht other

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
      exact addBoth2SubSup2 sub sup tail tail_ih (Std.AssocList.cons sup value tail)
    . case neg =>
      split <;> simp_all
      . case h_1 =>
        exact addBoth2SubSup2 sub sup tail tail_ih (Std.AssocList.cons key value tail)
      . case h_2 =>
        exact addBoth2SubSup2 sub sup tail tail_ih (Std.AssocList.cons sup [] (Std.AssocList.cons key value tail))

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
      split <;> simp_all
      . case h_1 =>
        exact addSubSup.more.sup sub sup tail tail_ih (Std.AssocList.cons key value tail)
      . case h_2 =>
        exact addSubSup.more.sup sub sup (Std.AssocList.cons sup [] tail) tail_ih (Std.AssocList.cons sup [] (Std.AssocList.cons key value tail))

end MWE9