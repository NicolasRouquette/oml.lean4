import Std.Classes.BEq

namespace MWE_eq1

example [BEq α] [LawfulBEq α] {x y : α} (h : ¬(x = y))
  : (match x == y with | true => 0 | false => 1) = 1 := by
  have : (x == y) = false := by simp [beq_eq_false_iff_ne, h]
  simp [this]

end MWE_eq1