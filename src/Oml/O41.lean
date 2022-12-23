-- See: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/OO.20polymorphism.3F/near/297629381
namespace O41

inductive Geo_Type
| Point2D
| Point3D
| Point4D
| Square2D
deriving Repr, DecidableEq

open Geo_Type

structure Slots_Point2D where
  (x y : Float)
  deriving Repr

structure Slots_Point3D extends Slots_Point2D where
  z : Float
  deriving Repr

structure Slots_Point4D extends Slots_Point3D where
  w : Float
  deriving Repr

structure Slots_Square2D extends Slots_Point2D where
  width : Float
  deriving Repr

def Geo_Type.Slots : Geo_Type → Type
| Point2D => Slots_Point2D
| Point3D => Slots_Point3D
| Point4D => Slots_Point4D
| Square2D => Slots_Square2D

/-- Even though Geo_Type.Slots returns a Type, 
 - the following proves that there is a Repr instance for that Type.
 -/
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
| Point2D, Point4D => some (λ x => x.toSlots_Point2D)
| Point3D, Point4D => some (λ x => x.toSlots_Point3D)
| Point4D, Point4D => some id
| Point2D, Square2D => some (λ x => x.toSlots_Point2D)
| Square2D, Square2D => some id
| _, _ => none

/-- Whether the second type is a subtype of the first. -/
def Geo_Type.supertype (t t' : Geo_Type) : Bool := (t.cast t').isSome

theorem Geo_Type.supertype.trans (h : Geo_Type.supertype t t') (h' : Geo_Type.supertype t' t'') :
  Geo_Type.supertype t t'' :=
by
  cases t
  all_goals
    cases t'
    all_goals
      cases t''
      all_goals
        simp at h
        try simp at h'
        try simp

def Option.get : (x : Option α) → x.isSome → α
| some v, _ => v
| none, h => by simp [Option.isSome] at h

/-- Get the cast function from a proof that `t'` is a subtype of `t`. -/
def Geo_Type.supertype.cast (h : Geo_Type.supertype t t') : t'.Slots → t.Slots :=
  Option.get (Geo_Type.cast t t') h

/-- Objects of subtype t -/
structure Obj (t : Geo_Type) where
  ty : Geo_Type
  sub : Geo_Type.supertype t ty
  slots : ty.Slots

instance : Coe Slots_Point2D (Obj Point2D) where coe s := ⟨Point2D, rfl, s⟩
instance : Coe Slots_Point3D (Obj Point3D) where coe s := ⟨Point3D, rfl, s⟩
instance : Coe Slots_Point4D (Obj Point4D) where coe s := ⟨Point4D, rfl, s⟩
instance : Coe Slots_Square2D (Obj Square2D) where coe s := ⟨Square2D, rfl, s⟩

/-- Extract the slots from an `Obj`. -/
def Obj.get (o : Obj t) : t.Slots := Geo_Type.supertype.cast o.sub o.slots

/-- Cast up, which can be done statically. -/
def Obj.cast_up (o : Obj t) (h : Geo_Type.supertype t' t := by rfl) : Obj t' where
  ty := o.ty
  sub := Geo_Type.supertype.trans h o.sub
  slots := o.slots

def Obj.can_cast (o : Obj t) (t' : Geo_Type) : Bool := Geo_Type.supertype t' o.ty

/-- Cast up or down using run-time information. -/
def Obj.cast (o : Obj t) (h : o.can_cast t') : Obj t' where
  ty := o.ty
  sub := h
  slots := o.slots

instance : Repr (Obj (T : Geo_Type)) where
  reprPrec o _ := ((instReprGeo_Type.reprPrec o.ty 1).append (Std.Format.text " ")).append ((toRepr o.ty).reprPrec o.slots 1)

def s2: Slots_Point2D := {x := 1, y := 2}
#eval s2

def o2: Obj Point2D := s2
#eval o2

def o3: Obj Point3D := ({x := 1, y := 2, z := 3}: Slots_Point3D)
#eval o3
#eval o3.get
#eval o3.slots
#eval o3.slots.x
#eval o3.slots.y
#eval o3.slots.z

def o4: Obj Point4D := ({x := 1, y := 2, z := 3, w := 4}: Slots_Point4D)
#eval o4
#eval o4.get.w
-- 4.000000

def o43: Obj Point3D := o4.cast_up
#eval o43
#eval o43.slots.w
-- 4.000000
#eval o43.get
--#eval o43.get.w
-- invalid field 'w', the environment does not contain 'O41.Geo_Type.Slots.w'
--  Obj.get o43
-- has type
--  Slots Point3D
end O41