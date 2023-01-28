import Std.Classes.BEq

namespace MWE_eq1

example [BEq α] [LawfulBEq α] {x y : α}
  : (x == y) = (x = y) := by 
  simp_all

end MWE_eq1