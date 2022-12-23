-- See: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/OO.20polymorphism.3F/near/297486439
namespace O1

structure Point where
  x : Float
  y : Float

class IsPoint (α : Type _) where
  toPoint:  α → Point

structure Point3D extends Point where
  z : Float

instance : IsPoint Point3D where
  toPoint := Point3D.toPoint

instance : IsPoint (Float × Float) where
  toPoint := fun (a, b) => { x := a, y := b }

def printPoint [IsPoint α] (p : α) : IO Unit :=
  let p := IsPoint.toPoint p
  IO.println s!"{p.x}, {p.y}"

def main : IO Unit := do
  let p : Point3D := { x := 1.0, y := 2.0, z := 3.0 }
  printPoint p
  let q := (1.0, 2.0)
  printPoint q
  

end O1

