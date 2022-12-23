-- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/OO.20polymorphism.3F/near/297514072
namespace O2

structure Point where
  x : Float
  y : Float

def Point.printPoint (p : Point) : IO Unit :=
  IO.println s!"{p.x}, {p.y}"

structure Point3D extends Point where
  z : Float

def p3 : Point3D where
  x := 1.0
  y := 2.0
  z := 3.0

instance : Coe Point3D Point where
  coe := Point3D.toPoint


structure Point4D extends Point3D where
  w : Float

def p4 : Point4D where
  x := 1.0
  y := 2.0
  z := 3.0
  w := 4.0

instance : Coe Point4D Point3D where
  coe := Point4D.toPoint3D

#eval p3.printPoint
#eval Point.printPoint p3
#eval p4.printPoint
#eval Point.printPoint p4

def pps : List Point := [p3, p4]
#print pps

end O2