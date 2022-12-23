-- See: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/OO.20polymorphism.3F/near/297718318
namespace O5

class Vector (α : Type) where
  length : α → Float

structure DynVector := 
  (α : Type) 
  [inst : Vector α] 
  (val : α)

attribute [instance] DynVector.inst

instance [Vector α] : Coe α DynVector := ⟨({ val := · })⟩

def sumLengths (xs : List DynVector) : Float :=
  xs.map (Vector.length ·.val) |>.foldl (·+·) 0

structure Vector2D := (x y : Float)

instance : Vector Vector2D where
  length | {x, y} => Float.sqrt (x * x + y * y)

structure Vector3D extends Vector2D := (z : Float)

instance : Vector Vector3D where
  length | {x, y, z} => Float.sqrt (x * x + y * y + z * z)

#eval do
  let a : Vector2D := { x := 3, y := 4 }
  IO.println (sumLengths [a]) -- 5

  let b : Vector3D := { x := 8, y := 9, z := 12 }
  IO.println (sumLengths [b]) -- 17

  IO.println (sumLengths [a, b]) -- 22

def a : Vector2D := { x := 3, y := 4 }
def b : Vector3D := { x := 8, y := 9, z := 12 }

def l : List DynVector := [a, b]

#eval sumLengths [a]

end O5