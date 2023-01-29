-- WIP: only 2 lemma2 to prove: AssocList.contains_exists, addSubSup.sub_sup

-- Tested with: 
-- leanprover/lean4:nightly unchanged - Lean (version 4.0.0-nightly-2023-01-28, commit e37f209c1a2a, Release)

import Std.Data.AssocList
import Std.Data.List.Lemmas
import Std.Classes.BEq

namespace MWE10

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
  
@[simp] theorem addSubSup.sub (sub sup: String) (ss: Std.AssocList String Strings): (addSubSup sub sup ss).contains sub
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

@[simp] theorem addSubSup.exists.sub (sub sup: String) (tail: Std.AssocList String Strings)
: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup tail) ∧ x.fst = sub
:= by
  induction tail <;> simp_all
  . case cons key value t ih =>
    simp [addSubSup, cond_eq_ite]
    by_cases key = sub
    . case pos h =>
      simp [h]
    . case neg h =>
      simp [h]
      apply ih

def addBoth (sub sup: String) (ss: Std.AssocList String Strings) : Std.AssocList String Strings :=
  let ss' := addDecl ss sup
  addSubSup sub sup ss'

@[simp] theorem addSubSup.cons
  (sub sup: String) 
  (tail: Std.AssocList String Strings)
  (h: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup tail) ∧ x.fst = sup)
: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] (Std.AssocList.cons key value tail))) ∧ x.fst = sup
:= by
  simp [addSubSup, cond_eq_ite]
  by_cases sup = sub <;> simp_all

@[simp] theorem addSubSup.cons2
  (sub sup: String) 
  (tail: Std.AssocList String Strings)
  (h: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] tail)) ∧ x.fst = sup)
: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] (Std.AssocList.cons key value tail))) ∧ x.fst = sup
:= by
  simp [addSubSup, cond_eq_ite]
  by_cases sup = sub <;> simp_all

theorem addBoth.sub_eq (sub sup: String) (ss: Std.AssocList String Strings) 
: (addBoth sub sup ss).contains sub
:= by
  induction ss <;> simp_all
  . case nil =>
    simp [addBoth, addDecl, addSubSup, cond_eq_ite]
    split <;> simp_all
  . case cons =>
    simp [addBoth, addDecl]

@[simp] theorem AssocList.contains_exists
  (s: Std.AssocList String Strings)
  (x: String)
  (h: s.contains x)
: ∃ a, a ∈ Std.AssocList.toList s ∧ a.fst = x
:= by
  sorry

@[simp] theorem addSubSup.sub_sup
  (sub sup: String) 
  (tail: Std.AssocList String Strings)
  (h: ∃ x, x ∈ Std.AssocList.toList tail ∧ x.fst = sup)
: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup tail) ∧ x.fst = sup
:= by
  sorry

theorem addBoth.sup_eq2 (sub sup: String) (ss: Std.AssocList String Strings) 
: (addBoth sub sup ss).contains sup
:= by
  rw [addBoth]
  let ss' := addDecl ss sup
  have h1: ss'.contains sup := addDecl.added ss sup
  have h2: ∃ x, x ∈ Std.AssocList.toList ss' ∧ x.fst = sup := by
    exact AssocList.contains_exists ss' sup h1
  simp_all

end MWE10