import Lean.Data.Json

instance : Lean.ToJson UInt8 := ⟨fun n => Lean.Json.num n.val⟩

instance : Lean.FromJson UInt8 := ⟨fun j => match Lean.Json.getInt? j with
| Except.error e => 
  throw e
| Except.ok i => 
  if h : i.toNat < UInt8.size then 
    return UInt8.ofNatCore i.toNat h 
  else 
    throw "Natural number less than 256 expected"⟩

instance : Lean.ToJson UInt32 := ⟨fun n => Lean.Json.num n.val⟩

instance : Lean.FromJson UInt32 := ⟨fun j => match Lean.Json.getInt? j with
| Except.error e => 
  throw e
| Except.ok i => 
  if h : i.toNat < UInt32.size then 
    return UInt32.ofNatCore i.toNat h 
  else 
    throw "Natural number less than 256 expected"⟩

universe u v
variable {α : Type u} {β : Type v}

instance [BEq α] [Hashable α] [Repr α]: Repr (Lean.HashSet α) where
  reprPrec h n := h.toList.repr n

instance [BEq α] [Hashable α] [Lean.ToJson α]: Lean.ToJson (Lean.HashSet α) where
  toJson h := Lean.toJson h.toList
   
instance [BEq α] [Hashable α] [Lean.FromJson α]: Lean.FromJson (Lean.HashSet α) where
  fromJson?  
    | Lean.Json.arr as => 
      (as.mapM Lean.fromJson?).map fun a: Array α => 
        a.foldl Lean.HashSet.insert Lean.HashSet.empty
    | j => throw s!"expected JSON array, got '{j}'"
   
instance [BEq α] [Hashable α] [Repr (α × β)]: Repr (Lean.HashMap α β) where
  reprPrec h n := h.toList.repr n

instance [BEq α] [Hashable α] [Lean.ToJson (α × β)]: Lean.ToJson (Lean.HashMap α β) where
  toJson h := Lean.toJson h.toList
   
instance [BEq α] [Hashable α] [Lean.FromJson (α × β)]: Lean.FromJson (Lean.HashMap α β) where
  fromJson?  
    | Lean.Json.arr as => 
      (as.mapM Lean.fromJson?).map fun a: Array (α × β) => Lean.HashMap.ofList (a.toList)
    | j => throw s!"expected JSON array, got '{j}'"
 
instance [BEq α] [Hashable α] [Repr (α × β)]: Repr (Lean.PersistentHashMap α β) where
  reprPrec h n := h.toList.repr n

instance [BEq α] [Hashable α] [Lean.ToJson (α × β)]: Lean.ToJson (Lean.PersistentHashMap α β) where
  toJson h := Lean.toJson h.toList
   
instance [BEq α] [Hashable α] [Lean.FromJson (α × β)]: Lean.FromJson (Lean.PersistentHashMap α β) where
  fromJson?  
    | Lean.Json.arr as => 
      (as.mapM Lean.fromJson?).map fun a: Array (α × β) => 
        a.foldl (fun m (pair: α × β) => Lean.PersistentHashMap.insert m pair.fst pair.snd) Lean.PersistentHashMap.empty
    | j => throw s!"expected JSON array, got '{j}'"