import Std.Data.AssocList
import Std.Data.List.Lemmas

namespace MWE7

abbrev Strings := List String

def addBoth : (Std.AssocList String Strings) → String → String → (Std.AssocList String Strings)
| .nil, sub, sup            => .cons sup [] (.cons sub [sup] .nil)
| .cons a as tail, sub, sup => bif a = sub then .cons sub (as.insert sup) tail else .cons a as (addBoth tail sub sup)

theorem addBoth.nil (sub: String) (sup: String)
: (addBoth .nil sub sup).contains sub && (addBoth .nil sub sup).contains sup
:= by simp [addBoth]

theorem cond_eq_ite (c : Bool) (a b : α) : cond c a b = if c then a else b := by cases c <;> rfl

theorem addBoth.sub (ss: Std.AssocList String Strings) (sub: String) (sup: String)
: (addBoth ss sub sup).contains sub
:= by
  simp [Std.AssocList.contains]
  induction ss <;> simp [addBoth]
  . next key value tail tail_ih =>
    simp [addBoth] 
    simp [cond_eq_ite]
    by_cases key = sup
    . case pos h =>
      simp [h]
      by_cases sub = sup
      . case pos ss =>
        simp [ss]
      . case neg ss =>
        split <;> simp_all
    . case neg =>
      split <;> simp_all

end MWE7