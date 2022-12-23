-- See: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/OO.20polymorphism.3F/near/297629381
namespace O42

inductive Geo_Type
| Point2D
| Point3D
deriving Repr, DecidableEq

open Geo_Type

structure Slots_Point2D where
  (x y : Float)
  deriving Repr

structure Slots_Point3D extends Slots_Point2D where
  z : Float
  deriving Repr

def Geo_Type.Slots : Geo_Type → Type
| Point2D => Slots_Point2D
| Point3D => Slots_Point3D

-- Even though Geo_Type.Slots returns a Type, 
-- the following proves that there is a Repr instance for that Type.
def toRepr : (T : Geo_Type) → Repr T.Slots := 
by {
  intro T;
  cases T <;> 
  unfold Geo_Type.Slots <;> 
  simp <;>
  infer_instance
}

/-- Get casting funct
ion to first type from second type -/
def Geo_Type.cast : (t : Geo_Type) → (t' : Geo_Type) → Option (t'.Slots → t.Slots)
| Point2D, Point2D => some id
| Point2D, Point3D => some (λ x => x.toSlots_Point2D)
| Point3D, Point3D => some id
| _, _ => none

/-- Whether the second type is a subtype of the first. -/
def Geo_Type.supertype (t t' : Geo_Type) : Bool := (t.cast t').isSome


/-- Objects of subtype t -/
structure Obj (t : Geo_Type) where
  ty : Geo_Type
  sub : Geo_Type.supertype t ty
  slots : ty.Slots

instance : Coe Slots_Point2D (Obj Point2D) where coe s := ⟨Point2D, rfl, s⟩
instance : Coe Slots_Point3D (Obj Point3D) where coe s := ⟨Point3D, rfl, s⟩

instance : Repr (Obj (T : Geo_Type)) where
  reprPrec o _ := ((instReprGeo_Type.reprPrec o.ty 1).append (Std.Format.text " ")).append ((toRepr o.ty).reprPrec o.slots 1)

def s2: Slots_Point2D := {x := 1, y := 2}
#eval s2

def o2: Obj Point2D := s2
#eval o2

end O42