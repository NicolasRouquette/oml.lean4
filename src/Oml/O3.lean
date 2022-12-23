-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/OO.20polymorphism.3F/near/297516151
namespace O3

structure Point where
  x : Float
  y : Float
  deriving Repr

class ToPoint (α : Type _) where
  toPoint : α → Point

instance : ToPoint Point where
  toPoint := id

structure Point3D extends Point where
  z : Float
  deriving Repr

class ToPoint3D (α : Type _) where
  toPoint3D : α → Point3D

instance : ToPoint3D Point3D where
  toPoint3D := id

instance [ToPoint3D α] : ToPoint α where
  toPoint x := (ToPoint3D.toPoint3D x).toPoint

structure Point4D extends Point3D where
  w : Float
  deriving Repr

class ToPoint4D (α : Type _) where
  toPoint4D : α → Point4D

instance : ToPoint4D Point4D where
  toPoint4D := id

instance [ToPoint4D α] : ToPoint3D α where
  toPoint3D x := (ToPoint4D.toPoint4D x).toPoint3D

instance [ToPoint α] : Coe α Point where
  coe := ToPoint.toPoint

instance [ToPoint3D α] : Coe α Point3D where
  coe := ToPoint3D.toPoint3D

instance [ToPoint4D α] : Coe α Point4D where
  coe := ToPoint4D.toPoint4D

def printPoints (p : List Point) : IO Unit :=
  for p in p do
    IO.println s!"{p.x}, {p.y}"

def print3DPoints (p : List Point3D) : IO Unit :=
  for p in p do
    IO.println s!"{p.x}, {p.y}, {p.z}"

def p : Point3D := { x := 1.0, y := 2.0, z := 3.0 }
def q : Point4D := { x := 1.0, y := 2.0, z := 3.0, w := 5.0 }
def pps : List Point := [p, q]
#eval pps
#print pps

def main : IO Unit := do
  printPoints [p]
  print3DPoints [p, q]
  
end O3
