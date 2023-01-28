-- WIP Trying to proove addBoth.sub, addBoth.sup 
-- Is it really necessary to import BEq and have beq_eq_eq?

-- Tested with: 
-- leanprover/lean4:nightly unchanged - Lean (version 4.0.0-nightly-2023-01-28, commit e37f209c1a2a, Release)

import Std.Data.AssocList
import Std.Data.List.Lemmas
import Std.Classes.BEq

namespace MWE8

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
        -- Given the tactic state:
        -- subsupkey: String
        -- value: Strings
        -- tail: Std.AssocList String Strings
        -- x: Bool
        -- tail_ih: ∃ x, x ∈ Std.AssocList.toList (addBoth sub sup tail) ∧ x.fst = sub
        -- h: ¬key = sup
        -- heq: ∃ x, x ∈ Std.AssocList.toList tail ∧ x.fst = sup
        
        -- How to prove?
        -- ⊢ ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons key value tail)) ∧ x.fst = sub
        sorry

      . case h_2 x heq =>
        -- Given the tactic state:
        -- subsupkey: String
        -- value: Strings
        -- tail: Std.AssocList String Strings
        -- x: Bool
        -- tail_ih: ∃ x, x ∈ Std.AssocList.toList (addBoth sub sup tail) ∧ x.fst = sub
        -- h: ¬key = sup
        -- heq: (List.any (Std.AssocList.toList tail) fun x => decide (x.fst = sup)) = false
        
        -- How to prove?
        -- ⊢ ∃ x,
        --   x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] (Std.AssocList.cons key value tail))) ∧
        --     x.fst = sub
        sorry

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
        -- Given the tactic state: (same as addBoth.sub_eq: path cons/neg/h_1)
        -- subsupkey: String
        -- value: Strings
        -- tail: Std.AssocList String Strings
        -- x: Bool
        -- tail_ih: ∃ x, x ∈ Std.AssocList.toList (addBoth sub sup tail) ∧ x.fst = sub
        -- h: ¬key = sup
        -- heq: ∃ x, x ∈ Std.AssocList.toList tail ∧ x.fst = sup

        -- How to prove?
        -- ⊢ ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons key value tail)) ∧ x.fst = sub
        sorry

      . case h_2 x heq =>
        -- Given the tactic state: (same as addBoth.sub_eq: path cons/neg/h_2)
        -- subsupkey: String
        -- value: Strings
        -- tail: Std.AssocList String Strings
        -- x: Bool
        -- tail_ih: ∃ x, x ∈ Std.AssocList.toList (addBoth sub sup tail) ∧ x.fst = sub
        -- h: ¬key = sup
        -- heq: (List.any (Std.AssocList.toList tail) fun x => decide (x.fst = sup)) = false

        -- How to prove?
        -- ⊢ ∃ x,
        --   x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] (Std.AssocList.cons key value tail))) ∧
        --     x.fst = sub
        sorry

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
        -- Given the tactic state:
        -- subsupkey: String
        -- value: Strings
        -- tail: Std.AssocList String Strings
        -- x: String × Strings
        -- y: Bool
        -- tail_ih: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup tail) ∧ x.fst = sup
        -- h1: ¬key = sup
        -- hx: x ∈ Std.AssocList.toList (addSubSup sub sup tail)
        -- he: x.fst = sup
        -- heq: ∃ x, x ∈ Std.AssocList.toList tail ∧ x.fst = sup

        -- How to prove?
        -- ⊢ ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons key value tail)) ∧ x.fst = sup
        sorry

      . case h_2 y heq =>
        -- Given the tactic state:
        -- subsupkey: String
        -- value: Strings
        -- tail: Std.AssocList String Strings
        -- x: String × Strings
        -- y: Bool
        -- tail_ih: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] tail)) ∧ x.fst = sup
        -- h1: ¬key = sup
        -- hx: x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] tail))
        -- he: x.fst = sup
        -- heq: (List.any (Std.AssocList.toList tail) fun x => decide (x.fst = sup)) = false

        -- How to prove?
        -- ⊢ ∃ x,
        --   x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] (Std.AssocList.cons key value tail))) ∧
        --     x.fst = sup
        sorry

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
      let ⟨ x, hx, he ⟩ := tail_ih
      split <;> simp_all
      . case h_1 y heq =>
        -- Given the tactic state (same as addBoth.sup_eq: path cons/neg/h1)
        -- subsupkey: String
        -- value: Strings
        -- tail: Std.AssocList String Strings
        -- x: String × Strings
        -- y: Bool
        -- tail_ih: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup tail) ∧ x.fst = sup
        -- h1: ¬key = sup
        -- hx: x ∈ Std.AssocList.toList (addSubSup sub sup tail)
        -- he: x.fst = sup
        -- heq: ∃ x, x ∈ Std.AssocList.toList tail ∧ x.fst = sup

        -- How to prove?
        -- ⊢ ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons key value tail)) ∧ x.fst = sup
        sorry

      . case h_2 y heq =>
        -- Given the tactic state: (same as addBoth.sup_eq: path cons/neg/h2)
        -- subsupkey: String
        -- value: Strings
        -- tail: Std.AssocList String Strings
        -- x: String × Strings
        -- y: Bool
        -- tail_ih: ∃ x, x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] tail)) ∧ x.fst = sup
        -- h1: ¬key = sup
        -- hx: x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] tail))
        -- he: x.fst = sup
        -- heq: (List.any (Std.AssocList.toList tail) fun x => decide (x.fst = sup)) = false

        -- How to prove?
        -- ⊢ ∃ x,
        --   x ∈ Std.AssocList.toList (addSubSup sub sup (Std.AssocList.cons sup [] (Std.AssocList.cons key value tail))) ∧
        --     x.fst = sup
        sorry

end MWE8