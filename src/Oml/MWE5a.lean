import Std.Data.AssocList
import Std.Data.List.Lemmas

namespace MWE5a

abbrev Strings := List String

def addSup : Strings → String → Strings
| [], sup       => [sup]
| x :: xs, sup  => if x = sup then x :: xs else x :: (addSup xs sup)

example (l : Strings) (x : String) : (addSup l x).contains x := by
  simp [List.contains]
  apply List.elem_eq_true_of_mem
  induction l <;> simp [addSup]
  split <;> simp [*]
  
theorem addSup.nil (sup: String)
: List.elem sup (addSup [] sup)
:= by simp [addSup]

theorem addSup.more (x: String) (head: String) (xs: Strings) (sup: String) 
(h: List.elem sup (addSup (x :: xs) sup))
:   List.elem sup (addSup (x :: head :: xs) sup)
:= by
  match xs with
  | [] =>
    simp [addSup, h]
    split
    . next ht => 
      simp_all
    . next hf => 
      simp_all
      split
      . rfl
      . split
        . simp_all
        . next ht =>
          rw [List.elem]
          split
          . rfl
          . simp
  | a :: as =>
    rw [← addSup.more]
    assumption
  termination_by addSup.more _ _ xs _ _ => xs.length

theorem addSup.cons (x: String) (xs: Strings) (sup: String) 
: List.elem sup (addSup (x :: xs) sup)
:= by
  induction xs
  case nil =>
    simp_all [addSup]
    split
    . case inl =>
      simp_all
    . case inr =>
      next hf =>
        simp_all [hf]
        split <;> rfl
  case cons head tail tail_ih =>
    apply addSup.more x head tail sup tail_ih 

end MWE5a
